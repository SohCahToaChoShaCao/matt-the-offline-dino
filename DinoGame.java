import javax.sound.sampled.*;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferStrategy;
import java.awt.image.BufferedImage;
import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.LockSupport;

public class DinoGame extends Canvas implements Runnable {

    // Canvas dimensions (matches HTML version 1:1)
    public static final int W = 800;
    public static final int H = 300;
    public static final int GROUND_Y = 245;

    // Original Chrome Offline Dino physics (locked to 60 FPS real time via nanoTime dt)
    private static final double INITIAL_SPEED = 5.5;
    private static final double MAX_SPEED = 12.0;
    private static final double ACCELERATION = 0.001;
    private static final double GRAVITY = 0.6;
    private static final double JUMP_VELOCITY = -12.5;

    // Pre-allocated colors & fonts (zero per-frame object allocations = zero GC lag)
    private static final Color COLOR_BG = Color.WHITE;
    private static final Color COLOR_PAUSE_VEIL = new Color(255, 255, 255, 185);
    private static final Color COLOR_DARK = new Color(83, 83, 83);
    private static final Color COLOR_CLOUD = new Color(220, 220, 220);
    private static final Color COLOR_PEBBLE = new Color(158, 158, 158);
    private static final Color COLOR_HI = new Color(136, 136, 136);
    private static final Color COLOR_SUB = new Color(117, 117, 117);

    private static final Font FONT_SCORE = new Font("Monospaced", Font.BOLD, 18);
    private static final Font FONT_START = new Font("Monospaced", Font.BOLD, 24);
    private static final Font FONT_OVER = new Font("Monospaced", Font.BOLD, 28);
    private static final Font FONT_SUB = new Font("Monospaced", Font.PLAIN, 15);
    private static final Stroke GROUND_STROKE = new BasicStroke(1.5f);
    private static final Stroke REPLAY_STROKE = new BasicStroke(2.5f);

    // Obstacle holder (1 = 1 cactus, 2 = 2 cactuses, 3 = 3 cactuses, 4 = flying dino)
    private static class Obstacle {
        int kind;
        double x;
        int y;
        int w;
        int h;

        Obstacle(int kind, double x, int y, int w, int h) {
            this.kind = kind;
            this.x = x;
            this.y = y;
            this.w = w;
            this.h = h;
        }
    }

    // Dino state
    private final int dinoX = 60;
    private final int dinoW = 110;
    private final int dinoH = 79;
    private final int duckW = 122;
    private final int duckH = 48;
    private double dinoY = GROUND_Y - dinoH;
    private double dinoVy = 0;

    // World entities
    private final double[][] clouds = { { 180, 55 }, { 470, 80 }, { 710, 45 } };
    private final double[][] pebbles = new double[24][3];
    private final List<Obstacle> obstacles = new ArrayList<Obstacle>();

    // Game state
    private double speed = INITIAL_SPEED;
    private double rawScore = 0;
    private int highScore = 0;
    private volatile boolean started = false;
    private volatile boolean gameOver = false;
    private volatile boolean paused = false;
    private volatile boolean isDucking = false;
    private volatile boolean running = false;
    private volatile boolean soundOn = true;

    private double animPhase = 0;
    private double flapTimer = 0;
    private double flashTimer = 0;
    private String flashScoreText = "00000";
    private double nextGap = 460;

    // Cached score strings
    private int cachedScoreVal = -1;
    private String cachedScoreStr = "00000";
    private int cachedHiVal = -1;
    private String cachedHiStr = "HI 00000";

    // Pre-scaled GPU-compatible sprites (loaded once at startup = zero scaling lag!)
    private BufferedImage rawIconImg;
    private BufferedImage dinoStandSprite;
    private BufferedImage dinoDuckSprite;
    private BufferedImage dinoJumpSprite;

    // Retro SFX & Custom Background Music Player (MP3 + WAV/AIFF/AU)
    private byte[] jumpPcm;
    private byte[] pointPcm;
    private byte[] hitPcm;
    private final ExecutorService soundExecutor = Executors.newSingleThreadExecutor(new ThreadFactoryDaemon("DinoSFX"));
    private final CustomMusicPlayer musicPlayer = new CustomMusicPlayer();

    // Optional UI callback so Pause button text stays synced when ESC is pressed
    private Runnable onStateChangeCallback;

    private static class ThreadFactoryDaemon implements java.util.concurrent.ThreadFactory {
        private final String name;

        ThreadFactoryDaemon(String name) {
            this.name = name;
        }

        @Override
        public Thread newThread(Runnable r) {
            Thread t = new Thread(r, name);
            t.setDaemon(true);
            return t;
        }
    }

    /**
     * Background streaming music player supporting both .mp3 (via bundled JLayer)
     * and .wav / .aiff / .au (via javax.sound.sampled), with instant ESC pause/resume & looping.
     */
    private class CustomMusicPlayer {
        private final AtomicInteger trackGeneration = new AtomicInteger(0);
        private volatile File currentFile;

        public void loadAndPlay(final File file) {
            currentFile = file;
            final int myGen = trackGeneration.incrementAndGet();
            Thread t = new Thread(new Runnable() {
                @Override
                public void run() {
                    streamLoop(file, myGen);
                }
            }, "DinoCustomMusic");
            t.setDaemon(true);
            t.start();
        }

        public void stopAll() {
            trackGeneration.incrementAndGet();
        }

        private boolean shouldPauseMusic() {
            return !soundOn || paused || gameOver;
        }

        private void streamLoop(File file, int myGen) {
            String lower = file.getName().toLowerCase();
            while (runningOrStarting() && trackGeneration.get() == myGen) {
                boolean ok;
                if (lower.endsWith(".mp3")) {
                    ok = playMp3Pass(file, myGen);
                } else {
                    ok = playSampledPass(file, myGen);
                }
                if (!ok) {
                    // Unsupported file or audio hardware unavailable; stop retrying
                    break;
                }
            }
        }

        private boolean runningOrStarting() {
            return true;
        }

        private boolean waitWhilePaused(SourceDataLine line, int myGen) {
            if (!shouldPauseMusic()) return true;
            if (line != null && line.isRunning()) {
                line.stop();
            }
            while (shouldPauseMusic() && trackGeneration.get() == myGen) {
                try {
                    Thread.sleep(25);
                } catch (InterruptedException e) {
                    return false;
                }
            }
            if (trackGeneration.get() != myGen) return false;
            if (line != null && !line.isRunning()) {
                line.start();
            }
            return true;
        }

        // Pure-Java MP3 streaming using JLayer classes bundled in DinoRun.jar
        private boolean playMp3Pass(File file, int myGen) {
            InputStream fis = null;
            Object bitstream = null;
            SourceDataLine line = null;
            try {
                Class<?> bsClass = Class.forName("javazoom.jl.decoder.Bitstream");
                Class<?> decClass = Class.forName("javazoom.jl.decoder.Decoder");
                Class<?> hdrClass = Class.forName("javazoom.jl.decoder.Header");
                Class<?> sbClass = Class.forName("javazoom.jl.decoder.SampleBuffer");

                Constructor<?> bsCtor = bsClass.getConstructor(InputStream.class);
                Method readFrame = bsClass.getMethod("readFrame");
                Method closeFrame = bsClass.getMethod("closeFrame");
                Method closeBs = bsClass.getMethod("close");

                Object decoder = decClass.getConstructor().newInstance();
                Method decodeFrame = decClass.getMethod("decodeFrame", hdrClass, bsClass);

                Method getFreq = sbClass.getMethod("getSampleFrequency");
                Method getCh = sbClass.getMethod("getChannelCount");
                Method getBuf = sbClass.getMethod("getBuffer");
                Method getLen = sbClass.getMethod("getBufferLength");

                fis = new BufferedInputStream(new FileInputStream(file), 65536);
                bitstream = bsCtor.newInstance(fis);
                byte[] pcmBytes = new byte[8192];

                while (trackGeneration.get() == myGen) {
                    if (!waitWhilePaused(line, myGen)) break;

                    Object header = readFrame.invoke(bitstream);
                    if (header == null) {
                        // End of MP3 -> return true so outer loop replays seamlessly!
                        return true;
                    }

                    Object sampleBuf = decodeFrame.invoke(decoder, header, bitstream);
                    if (line == null) {
                        int freq = ((Integer) getFreq.invoke(sampleBuf)).intValue();
                        int ch = ((Integer) getCh.invoke(sampleBuf)).intValue();
                        AudioFormat fmt = new AudioFormat(freq, 16, ch, true, false);
                        line = AudioSystem.getSourceDataLine(fmt);
                        line.open(fmt, 8192);
                        line.start();
                    }

                    short[] samples = (short[]) getBuf.invoke(sampleBuf);
                    int len = ((Integer) getLen.invoke(sampleBuf)).intValue();
                    int byteCount = len * 2;
                    if (pcmBytes.length < byteCount) {
                        pcmBytes = new byte[byteCount];
                    }

                    for (int i = 0; i < len; i++) {
                        int scaled = (int) (samples[i] * 0.55); // Balanced background music volume
                        pcmBytes[i * 2] = (byte) (scaled & 0xff);
                        pcmBytes[i * 2 + 1] = (byte) ((scaled >> 8) & 0xff);
                    }

                    line.write(pcmBytes, 0, byteCount);
                    closeFrame.invoke(bitstream);
                }
                return true;
            } catch (Throwable t) {
                return false;
            } finally {
                if (line != null) {
                    try {
                        line.stop();
                        line.close();
                    } catch (Throwable ignored) {
                    }
                }
                if (bitstream != null) {
                    try {
                        bitstream.getClass().getMethod("close").invoke(bitstream);
                    } catch (Throwable ignored) {
                    }
                }
                if (fis != null) {
                    try {
                        fis.close();
                    } catch (Throwable ignored) {
                    }
                }
            }
        }

        // WAV / AIFF / AU streaming
        private boolean playSampledPass(File file, int myGen) {
            AudioInputStream rawIn = null;
            AudioInputStream pcmIn = null;
            SourceDataLine line = null;
            try {
                rawIn = AudioSystem.getAudioInputStream(file);
                AudioFormat base = rawIn.getFormat();
                AudioFormat decodedFmt = new AudioFormat(
                        AudioFormat.Encoding.PCM_SIGNED,
                        base.getSampleRate(),
                        16,
                        base.getChannels(),
                        base.getChannels() * 2,
                        base.getSampleRate(),
                        false
                );
                pcmIn = AudioSystem.getAudioInputStream(decodedFmt, rawIn);
                line = AudioSystem.getSourceDataLine(decodedFmt);
                line.open(decodedFmt, 8192);
                line.start();

                byte[] buf = new byte[4096];
                int n;
                while (trackGeneration.get() == myGen) {
                    if (!waitWhilePaused(line, myGen)) break;
                    n = pcmIn.read(buf, 0, buf.length);
                    if (n < 0) {
                        return true; // Loop from start
                    }
                    // Scale 16-bit PCM slightly so jump SFX remain audible
                    for (int i = 0; i + 1 < n; i += 2) {
                        short s = (short) ((buf[i + 1] << 8) | (buf[i] & 0xff));
                        int scaled = (int) (s * 0.55);
                        buf[i] = (byte) (scaled & 0xff);
                        buf[i + 1] = (byte) ((scaled >> 8) & 0xff);
                    }
                    if (n > 0) {
                        line.write(buf, 0, n);
                    }
                }
                return true;
            } catch (Throwable t) {
                return false;
            } finally {
                if (line != null) {
                    try {
                        line.stop();
                        line.close();
                    } catch (Throwable ignored) {
                    }
                }
                if (pcmIn != null) {
                    try {
                        pcmIn.close();
                    } catch (Throwable ignored) {
                    }
                }
                if (rawIn != null) {
                    try {
                        rawIn.close();
                    } catch (Throwable ignored) {
                    }
                }
            }
        }
    }

    public DinoGame() {
        setPreferredSize(new Dimension(W, H));
        setSize(W, H);
        setBackground(COLOR_BG);
        setIgnoreRepaint(true);
        setFocusable(true);

        for (int i = 0; i < pebbles.length; i++) {
            pebbles[i][0] = i * 38 + Math.random() * 20;
            pebbles[i][1] = GROUND_Y + 5 + (int) (Math.random() * 10);
            pebbles[i][2] = 2 + (int) (Math.random() * 6);
        }

        loadAndPrescaleSprites();
        initRetroSounds();

        addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                requestFocusInWindow();
                if (paused) {
                    togglePause();
                } else {
                    triggerJump();
                }
            }
        });
    }

    private void notifyUiStateChanged() {
        if (onStateChangeCallback != null) {
            SwingUtilities.invokeLater(onStateChangeCallback);
        }
    }

    private void loadAndPrescaleSprites() {
        Image loaded = null;
        if (getClass().getResource("/dino.png") != null) {
            loaded = new ImageIcon(getClass().getResource("/dino.png")).getImage();
        } else if (new File("dino.png").exists()) {
            loaded = new ImageIcon("dino.png").getImage();
        } else if (new File("src/dino.png").exists()) {
            loaded = new ImageIcon("src/dino.png").getImage();
        }

        if (loaded != null && loaded.getWidth(null) > 0) {
            rawIconImg = toCompatibleImage(loaded, loaded.getWidth(null), loaded.getHeight(null), 0);
            dinoStandSprite = toCompatibleImage(loaded, dinoW, dinoH, 0);
            dinoDuckSprite = toCompatibleImage(loaded, duckW, duckH, 0);
            dinoJumpSprite = toCompatibleImage(loaded, dinoW + 8, dinoH + 8, -0.05);
        }
    }

    private BufferedImage toCompatibleImage(Image src, int w, int h, double rotateRad) {
        BufferedImage img;
        if (!GraphicsEnvironment.isHeadless()) {
            GraphicsConfiguration gc = GraphicsEnvironment
                    .getLocalGraphicsEnvironment()
                    .getDefaultScreenDevice()
                    .getDefaultConfiguration();
            img = gc.createCompatibleImage(w, h, Transparency.TRANSLUCENT);
        } else {
            img = new BufferedImage(w, h, BufferedImage.TYPE_INT_ARGB);
        }
        Graphics2D g2 = img.createGraphics();
        g2.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_BILINEAR);
        g2.setRenderingHint(RenderingHints.KEY_RENDERING, RenderingHints.VALUE_RENDER_QUALITY);
        g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        if (rotateRad != 0) {
            g2.rotate(rotateRad, w / 2.0, h / 2.0);
            g2.drawImage(src, 4, 4, w - 8, h - 8, null);
        } else {
            g2.drawImage(src, 0, 0, w, h, null);
        }
        g2.dispose();
        return img;
    }

    private void initRetroSounds() {
        jumpPcm = buildToneSequence(new int[] { 530 }, new int[] { 75 }, true);
        pointPcm = buildToneSequence(new int[] { 780, 1040 }, new int[] { 70, 130 }, true);
        hitPcm = buildToneSequence(new int[] { 190, 135 }, new int[] { 100, 180 }, false);
    }

    private byte[] buildToneSequence(int[] freqs, int[] durationsMs, boolean squareWave) {
        int sampleRate = 22050;
        int totalSamples = 0;
        for (int d : durationsMs) {
            totalSamples += (sampleRate * d) / 1000;
        }
        byte[] pcm = new byte[totalSamples];
        int idx = 0;
        for (int n = 0; n < freqs.length; n++) {
            int samples = (sampleRate * durationsMs[n]) / 1000;
            double period = (double) sampleRate / freqs[n];
            for (int i = 0; i < samples && idx < pcm.length; i++) {
                double env = 1.0 - ((double) i / samples) * 0.75;
                double phase = (i % period) / period;
                double wave = squareWave ? (phase < 0.5 ? 1.0 : -1.0) : (2.0 * phase - 1.0);
                pcm[idx++] = (byte) (wave * 26 * env);
            }
        }
        return pcm;
    }

    private void playSound(final byte[] pcm) {
        if (!soundOn || pcm == null) return;
        soundExecutor.execute(new Runnable() {
            @Override
            public void run() {
                try {
                    AudioFormat fmt = new AudioFormat(22050f, 8, 1, true, false);
                    SourceDataLine line = AudioSystem.getSourceDataLine(fmt);
                    line.open(fmt, 4096);
                    line.start();
                    line.write(pcm, 0, pcm.length);
                    line.drain();
                    line.close();
                } catch (Throwable ignored) {
                }
            }
        });
    }

    private static String pad5(int num) {
        String s = Integer.toString(num);
        while (s.length() < 5) {
            s = "0" + s;
        }
        return s;
    }

    private synchronized void spawnObstacle(double startX, boolean forceFirst) {
        int scoreVal = (int) rawScore;
        if (forceFirst) {
            int h = 48;
            obstacles.add(new Obstacle(1, startX, GROUND_Y - h, 24, h));
            nextGap = 420 + Math.random() * 220;
            return;
        }

        double roll = Math.random();
        if (scoreVal > 15 && roll < 0.28) {
            int[] heights = { 202, 162, 126 };
            int py = heights[(int) (Math.random() * heights.length)];
            obstacles.add(new Obstacle(4, startX, py, 46, 34));
        } else if (roll < 0.56) {
            int h = 44;
            obstacles.add(new Obstacle(3, startX, GROUND_Y - h, 70, h));
        } else if (roll < 0.78) {
            int h = 48;
            obstacles.add(new Obstacle(2, startX, GROUND_Y - h, 48, h));
        } else {
            int h = 48 + (int) (Math.random() * 6);
            obstacles.add(new Obstacle(1, startX, GROUND_Y - h, 24, h));
        }

        nextGap = 400 + speed * 18 + Math.random() * 270;
    }

    private synchronized void resetGame() {
        dinoY = GROUND_Y - dinoH;
        dinoVy = 0;
        obstacles.clear();
        spawnObstacle(W + 220, true);
        speed = INITIAL_SPEED;
        rawScore = 0;
        gameOver = false;
        paused = false;
        started = true;
        isDucking = false;
        flashTimer = 0;
        notifyUiStateChanged();
    }

    public synchronized void togglePause() {
        if (!started || gameOver) return;
        paused = !paused;
        if (paused) {
            isDucking = false;
        }
        notifyUiStateChanged();
    }

    public synchronized void setPaused(boolean p) {
        if (!started || gameOver) return;
        if (paused != p) {
            paused = p;
            if (paused) {
                isDucking = false;
            }
            notifyUiStateChanged();
        }
    }

    public synchronized void triggerJump() {
        if (paused) {
            // While paused, wait for ESC or click to unpause cleanly without accidental jump
            return;
        }
        if (!started) {
            resetGame();
            dinoVy = JUMP_VELOCITY;
            playSound(jumpPcm);
            return;
        }
        if (gameOver) {
            resetGame();
            playSound(jumpPcm);
            return;
        }
        if (dinoY >= GROUND_Y - dinoH - 1) {
            isDucking = false;
            dinoVy = JUMP_VELOCITY;
            playSound(jumpPcm);
        }
    }

    public synchronized void setDuck(boolean active) {
        if (!started || gameOver || paused) return;
        isDucking = active;
    }

    public synchronized void updateGame(double dt) {
        if (!started || gameOver || paused) return;

        animPhase += dt * 0.16;
        flapTimer += dt;

        // Midpoint jump & fast-drop physics
        boolean inAir = dinoY < GROUND_Y - dinoH - 0.5;
        double currentGravity = (isDucking && inAir) ? GRAVITY * 3.2 : GRAVITY;
        double prevVy = dinoVy;
        dinoVy += currentGravity * dt;
        dinoY += ((prevVy + dinoVy) * 0.5) * dt;

        if (dinoY >= GROUND_Y - dinoH) {
            dinoY = GROUND_Y - dinoH;
            dinoVy = 0;
        }

        // Drift clouds
        for (int i = 0; i < clouds.length; i++) {
            clouds[i][0] -= 0.75 * dt;
            if (clouds[i][0] < -60) {
                clouds[i][0] = W + 40;
            }
        }

        // Scroll ground pebbles
        for (int i = 0; i < pebbles.length; i++) {
            pebbles[i][0] -= speed * dt;
            if (pebbles[i][0] < -10) {
                pebbles[i][0] = W + Math.random() * 30;
                pebbles[i][1] = GROUND_Y + 5 + (int) (Math.random() * 10);
            }
        }

        // Move & spawn obstacles
        Iterator<Obstacle> it = obstacles.iterator();
        while (it.hasNext()) {
            Obstacle ob = it.next();
            ob.x -= speed * dt;
            if (ob.x + ob.w < -40) {
                it.remove();
            }
        }

        if (obstacles.isEmpty()) {
            spawnObstacle(W + 40, false);
        } else {
            Obstacle lastOb = obstacles.get(obstacles.size() - 1);
            if (W - lastOb.x >= nextGap) {
                spawnObstacle(W + 20, false);
            }
        }

        // Score & 100-point flash milestone
        int prevDisplay = (int) rawScore;
        rawScore += speed * 0.025 * dt;
        int currDisplay = (int) rawScore;

        if (currDisplay > highScore) {
            highScore = currDisplay;
        }

        if (currDisplay > 0 && currDisplay % 100 == 0 && currDisplay != prevDisplay) {
            flashTimer = 48;
            flashScoreText = pad5(currDisplay);
            playSound(pointPcm);
        }

        if (flashTimer > 0) {
            flashTimer = Math.max(0, flashTimer - dt);
        }

        if (speed < MAX_SPEED) {
            speed = Math.min(MAX_SPEED, speed + ACCELERATION * dt);
        }

        // Fair Hitbox check
        boolean onGround = dinoY >= GROUND_Y - dinoH - 1;
        int dBoxX = (isDucking && onGround) ? (dinoX + 22) : (dinoX + 26);
        int dBoxY = (isDucking && onGround) ? (GROUND_Y - duckH + 10) : ((int) dinoY + 14);
        int dBoxW = (isDucking && onGround) ? 76 : (dinoW - 44);
        int dBoxH = (isDucking && onGround) ? (duckH - 12) : (dinoH - 18);

        for (int i = 0; i < obstacles.size(); i++) {
            Obstacle ob = obstacles.get(i);
            int oBoxX = (int) ob.x + 3;
            int oBoxY = ob.y + 4;
            int oBoxW = ob.w - 6;
            int oBoxH = ob.h - 6;

            boolean hit = dBoxX < oBoxX + oBoxW
                    && dBoxX + dBoxW > oBoxX
                    && dBoxY < oBoxY + oBoxH
                    && dBoxY + dBoxH > oBoxY;

            if (hit) {
                gameOver = true;
                playSound(hitPcm);
                notifyUiStateChanged();
                break;
            }
        }
    }

    private void drawSingleCactus(Graphics2D g, int x, int y, int h) {
        g.fillRect(x + 8, y, 8, h);
        g.fillRect(x, y + 20, 24, 6);
        g.fillRect(x, y + 10, 5, 14);
        g.fillRect(x + 19, y + 6, 5, 18);
    }

    private void drawFlyingDino(Graphics2D g, int x, int y, boolean wingUp) {
        g.fillRect(x, y + 10, 14, 3);
        g.fillRect(x + 3, y + 15, 11, 2);
        g.fillRect(x + 10, y + 7, 8, 9);
        g.fillRect(x + 14, y + 4, 8, 4);
        g.fillRect(x + 16, y + 13, 20, 7);
        g.fillRect(x + 36, y + 15, 10, 3);

        if (wingUp) {
            g.fillRect(x + 18, y + 7, 13, 6);
            g.fillRect(x + 20, y + 1, 9, 6);
            g.fillRect(x + 22, y - 4, 5, 5);
        } else {
            g.fillRect(x + 18, y + 20, 12, 5);
            g.fillRect(x + 20, y + 25, 8, 5);
            g.fillRect(x + 21, y + 30, 5, 4);
        }
    }

    public synchronized void renderFrame(Graphics2D g) {
        g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);

        // Clear background
        g.setColor(COLOR_BG);
        g.fillRect(0, 0, W, H);

        // 1. Clouds
        g.setColor(COLOR_CLOUD);
        for (int i = 0; i < clouds.length; i++) {
            int cx = (int) clouds[i][0];
            int cy = (int) clouds[i][1];
            g.fillRect(cx + 8, cy, 28, 8);
            g.fillRect(cx, cy + 6, 46, 8);
        }

        // 2. Ground line & pebbles
        g.setColor(COLOR_DARK);
        g.setStroke(GROUND_STROKE);
        g.drawLine(0, GROUND_Y, W, GROUND_Y);

        g.setColor(COLOR_PEBBLE);
        for (int i = 0; i < pebbles.length; i++) {
            g.fillRect((int) pebbles[i][0], (int) pebbles[i][1], (int) pebbles[i][2], 2);
        }

        // 3. Obstacles
        g.setColor(COLOR_DARK);
        boolean wingUp = (((int) (flapTimer / 11.0)) % 2) == 0;
        for (int i = 0; i < obstacles.size(); i++) {
            Obstacle ob = obstacles.get(i);
            int ox = (int) Math.round(ob.x);
            if (ob.kind == 1) {
                drawSingleCactus(g, ox, ob.y, ob.h);
            } else if (ob.kind == 2) {
                drawSingleCactus(g, ox, ob.y, ob.h);
                drawSingleCactus(g, ox + 24, ob.y + 4, ob.h - 4);
            } else if (ob.kind == 3) {
                drawSingleCactus(g, ox, ob.y + 2, ob.h - 2);
                drawSingleCactus(g, ox + 23, ob.y - 2, ob.h + 2);
                drawSingleCactus(g, ox + 46, ob.y + 4, ob.h - 4);
            } else if (ob.kind == 4) {
                drawFlyingDino(g, ox, ob.y, wingUp);
            }
        }

        // 4. Player Dino
        boolean onGround = dinoY >= GROUND_Y - dinoH - 1;
        int runBob = (started && !gameOver && !paused && onGround) ? (int) Math.round(Math.sin(animPhase) * 1.5) : 0;

        if (dinoStandSprite != null) {
            if (!onGround) {
                g.drawImage(dinoJumpSprite, dinoX - 4, (int) Math.round(dinoY) + 2, null);
            } else if (isDucking) {
                int dy = GROUND_Y - duckH + 6 + (runBob / 2);
                g.drawImage(dinoDuckSprite, dinoX, dy, null);
            } else {
                g.drawImage(dinoStandSprite, dinoX, (int) Math.round(dinoY) + 6 + runBob, null);
            }
        } else {
            g.setColor(new Color(46, 125, 50));
            int dh = (isDucking && onGround) ? duckH : dinoH;
            int dy = (isDucking && onGround) ? (GROUND_Y - duckH) : (int) Math.round(dinoY);
            g.fillRect(dinoX, dy, dinoW, dh);
        }

        // 5. High Score & 5-digit Score
        g.setFont(FONT_SCORE);
        FontMetrics fmScore = g.getFontMetrics();

        if (highScore > 0) {
            if (highScore != cachedHiVal) {
                cachedHiVal = highScore;
                cachedHiStr = "HI " + pad5(highScore);
            }
            g.setColor(COLOR_HI);
            g.drawString(cachedHiStr, W - 115 - fmScore.stringWidth(cachedHiStr), 34);
        }

        boolean showScore = flashTimer <= 0 || (((int) (flashTimer / 8.0)) % 2 == 0);
        if (showScore) {
            int currInt = (int) rawScore;
            if (currInt != cachedScoreVal) {
                cachedScoreVal = currInt;
                cachedScoreStr = pad5(currInt);
            }
            String txt = flashTimer > 0 ? flashScoreText : cachedScoreStr;
            g.setColor(COLOR_DARK);
            g.drawString(txt, W - 28 - fmScore.stringWidth(txt), 34);
        }

        // 6. Start / Pause / Game Over Overlays (matches HTML version 1:1)
        if (!started) {
            g.setColor(COLOR_DARK);
            g.setFont(FONT_START);
            String msg = "PRESS SPACE OR CLICK TO START";
            int mw = g.getFontMetrics().stringWidth(msg);
            g.drawString(msg, (W - mw) / 2, 118);
        } else if (paused && !gameOver) {
            g.setColor(COLOR_PAUSE_VEIL);
            g.fillRect(0, 0, W, H);

            g.setColor(COLOR_DARK);
            g.setFont(FONT_OVER);
            String pMsg = "P A U S E D";
            int pw = g.getFontMetrics().stringWidth(pMsg);
            g.drawString(pMsg, (W - pw) / 2, 108);

            // Resume Play icon box
            g.fillRect(W / 2 - 18, 124, 36, 32);
            g.setColor(Color.WHITE);
            Polygon playTri = new Polygon(
                    new int[] { W / 2 - 5, W / 2 - 5, W / 2 + 8 },
                    new int[] { 132, 148, 140 },
                    3
            );
            g.fillPolygon(playTri);

            g.setColor(COLOR_SUB);
            g.setFont(FONT_SUB);
            String subMsg = "Press ESC or Click to Resume";
            int sw = g.getFontMetrics().stringWidth(subMsg);
            g.drawString(subMsg, (W - sw) / 2, 178);
        } else if (gameOver) {
            g.setColor(COLOR_DARK);
            g.setFont(FONT_OVER);
            String overMsg = "G A M E   O V E R";
            int ow = g.getFontMetrics().stringWidth(overMsg);
            g.drawString(overMsg, (W - ow) / 2, 108);

            // Replay icon button
            g.fillRect(W / 2 - 18, 124, 36, 32);
            g.setColor(Color.WHITE);
            Stroke oldStroke = g.getStroke();
            g.setStroke(REPLAY_STROKE);
            g.drawArc(W / 2 - 9, 131, 18, 18, 35, 285);
            g.setStroke(oldStroke);
            Polygon arrow = new Polygon(
                    new int[] { W / 2 + 5, W / 2 + 12, W / 2 + 7 },
                    new int[] { 130, 132, 138 },
                    3
            );
            g.fillPolygon(arrow);

            g.setColor(COLOR_SUB);
            g.setFont(FONT_SUB);
            String subMsg = "Press SPACE or Click to Play Again";
            int sw = g.getFontMetrics().stringWidth(subMsg);
            g.drawString(subMsg, (W - sw) / 2, 178);
        }
    }

    public void startGameLoop() {
        if (running) return;
        running = true;
        Thread gameThread = new Thread(this, "DinoRenderLoop");
        gameThread.setDaemon(true);
        gameThread.start();
    }

    public void stopGameLoop() {
        running = false;
        musicPlayer.stopAll();
    }

    @Override
    public void run() {
        createBufferStrategy(2);
        BufferStrategy bs = getBufferStrategy();

        long lastTime = System.nanoTime();
        final long targetFrameNs = 8_333_333L; // ~120 FPS smooth rendering, physics locked to 60 FPS via dt

        while (running) {
            long now = System.nanoTime();
            long elapsedNs = now - lastTime;
            lastTime = now;

            double dt = elapsedNs / 16_666_667.0;
            if (dt < 0) dt = 0;
            if (dt > 2.5) dt = 2.5;

            updateGame(dt);

            try {
                if (!isDisplayable()) break;
                do {
                    do {
                        Graphics2D g = (Graphics2D) bs.getDrawGraphics();
                        try {
                            renderFrame(g);
                        } finally {
                            g.dispose();
                        }
                    } while (running && bs.contentsRestored());
                    if (running) bs.show();
                } while (running && bs.contentsLost());

                Toolkit.getDefaultToolkit().sync();
            } catch (Throwable ignored) {
                break;
            }

            long frameTime = System.nanoTime() - now;
            long sleepNs = targetFrameNs - frameTime;
            if (sleepNs > 2_000_000L) {
                try {
                    Thread.sleep((sleepNs - 1_500_000L) / 1_000_000L);
                } catch (InterruptedException ignored) {
                }
            }
            while (running && System.nanoTime() - now < targetFrameNs) {
                LockSupport.parkNanos(250_000L);
            }
        }
    }

    private static JButton createBarButton(String text, boolean primary) {
        JButton btn = new JButton(text);
        btn.setFont(new Font("Monospaced", Font.BOLD, 12));
        if (primary) {
            btn.setForeground(Color.WHITE);
            btn.setBackground(COLOR_DARK);
            btn.setOpaque(true);
            btn.setBorder(BorderFactory.createEmptyBorder(6, 14, 6, 14));
        } else {
            btn.setForeground(COLOR_DARK);
            btn.setBackground(Color.WHITE);
            btn.setOpaque(true);
            btn.setBorder(BorderFactory.createCompoundBorder(
                    BorderFactory.createLineBorder(new Color(195, 195, 195), 1),
                    BorderFactory.createEmptyBorder(5, 10, 5, 10)
            ));
        }
        btn.setFocusPainted(false);
        btn.setFocusable(false);
        btn.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
        return btn;
    }

    private static String shortenTrackName(String name) {
        if (name.length() <= 20) return name;
        return name.substring(0, 17) + "...";
    }

    public static void main(String[] args) {
        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                final JFrame frame = new JFrame("Dino Run");
                final DinoGame game = new DinoGame();

                if (game.rawIconImg != null) {
                    frame.setIconImage(game.rawIconImg);
                }

                JPanel root = new JPanel(new BorderLayout());
                root.setBackground(Color.WHITE);

                // Top bar: Title + Track Indicator + [+ MUSIC] + [PAUSE (ESC)] + [SOUND: ON]
                JPanel topBar = new JPanel(new BorderLayout(10, 0));
                topBar.setBackground(new Color(239, 239, 239));
                topBar.setBorder(BorderFactory.createCompoundBorder(
                        BorderFactory.createMatteBorder(0, 0, 1, 0, new Color(220, 220, 220)),
                        new EmptyBorder(8, 16, 8, 16)
                ));

                JPanel leftTitleBox = new JPanel(new FlowLayout(FlowLayout.LEFT, 8, 0));
                leftTitleBox.setOpaque(false);
                JLabel titleLbl = new JLabel("DINO RUN");
                titleLbl.setFont(new Font("Monospaced", Font.BOLD, 14));
                titleLbl.setForeground(new Color(68, 68, 68));

                final JLabel musicTrackLbl = new JLabel("");
                musicTrackLbl.setFont(new Font("Monospaced", Font.PLAIN, 12));
                musicTrackLbl.setForeground(new Color(110, 110, 110));

                leftTitleBox.add(titleLbl);
                leftTitleBox.add(musicTrackLbl);

                JPanel topActions = new JPanel(new FlowLayout(FlowLayout.RIGHT, 6, 0));
                topActions.setOpaque(false);

                final JButton musicBtn = createBarButton("\u266A + MUSIC", false);
                final JButton pauseBtn = createBarButton("PAUSE (ESC)", false);
                final JButton soundBtn = createBarButton("SOUND: ON", false);

                game.onStateChangeCallback = new Runnable() {
                    @Override
                    public void run() {
                        pauseBtn.setText(game.paused ? "RESUME (ESC)" : "PAUSE (ESC)");
                    }
                };

                musicBtn.addActionListener(new ActionListener() {
                    @Override
                    public void actionPerformed(ActionEvent e) {
                        boolean wasPlayingRun = game.started && !game.gameOver && !game.paused;
                        if (wasPlayingRun) {
                            game.setPaused(true); // Auto-pause while choosing song!
                        }

                        JFileChooser chooser = new JFileChooser();
                        chooser.setDialogTitle("Select Background Music (.mp3, .wav, .aiff)");
                        FileNameExtensionFilter filter = new FileNameExtensionFilter(
                                "Audio Files (*.mp3, *.wav, *.aiff, *.au)", "mp3", "wav", "aiff", "au");
                        chooser.setFileFilter(filter);

                        int result = chooser.showOpenDialog(frame);
                        if (result == JFileChooser.APPROVE_OPTION && chooser.getSelectedFile() != null) {
                            File chosen = chooser.getSelectedFile();
                            musicTrackLbl.setText("\u266A " + shortenTrackName(chosen.getName()));
                            musicBtn.setText("\u266A CHANGE");
                            game.musicPlayer.loadAndPlay(chosen);
                        }
                        game.requestFocusInWindow();
                    }
                });

                pauseBtn.addActionListener(new ActionListener() {
                    @Override
                    public void actionPerformed(ActionEvent e) {
                        game.togglePause();
                        game.requestFocusInWindow();
                    }
                });

                soundBtn.addActionListener(new ActionListener() {
                    @Override
                    public void actionPerformed(ActionEvent e) {
                        game.soundOn = !game.soundOn;
                        soundBtn.setText(game.soundOn ? "SOUND: ON" : "SOUND: OFF");
                        game.requestFocusInWindow();
                    }
                });

                topActions.add(musicBtn);
                topActions.add(pauseBtn);
                topActions.add(soundBtn);

                topBar.add(leftTitleBox, BorderLayout.WEST);
                topBar.add(topActions, BorderLayout.EAST);

                // Bottom controls bar
                JPanel bottomBar = new JPanel(new BorderLayout());
                bottomBar.setBackground(new Color(250, 250, 250));
                bottomBar.setBorder(BorderFactory.createCompoundBorder(
                        BorderFactory.createMatteBorder(1, 0, 0, 0, new Color(236, 236, 236)),
                        new EmptyBorder(10, 16, 10, 16)
                ));
                JLabel hintLbl = new JLabel("SPACE/UP: Jump \u2022 DOWN: Duck \u2022 ESC: Pause");
                hintLbl.setFont(new Font("Monospaced", Font.PLAIN, 13));
                hintLbl.setForeground(COLOR_DARK);

                JPanel btnGroup = new JPanel(new FlowLayout(FlowLayout.RIGHT, 8, 0));
                btnGroup.setOpaque(false);

                final JButton duckBtn = createBarButton("DUCK (\u2193)", false);
                duckBtn.addMouseListener(new MouseAdapter() {
                    @Override
                    public void mousePressed(MouseEvent e) {
                        if (game.paused) {
                            game.togglePause();
                        } else if (!game.started || game.gameOver) {
                            game.triggerJump();
                        } else {
                            game.setDuck(true);
                        }
                    }

                    @Override
                    public void mouseReleased(MouseEvent e) {
                        game.setDuck(false);
                    }
                });

                final JButton jumpBtn = createBarButton("JUMP (\u2191)", true);
                jumpBtn.addMouseListener(new MouseAdapter() {
                    @Override
                    public void mousePressed(MouseEvent e) {
                        if (game.paused) {
                            game.togglePause();
                        } else {
                            game.triggerJump();
                        }
                    }
                });

                btnGroup.add(duckBtn);
                btnGroup.add(jumpBtn);

                bottomBar.add(hintLbl, BorderLayout.WEST);
                bottomBar.add(btnGroup, BorderLayout.EAST);

                root.add(topBar, BorderLayout.NORTH);
                root.add(game, BorderLayout.CENTER);
                root.add(bottomBar, BorderLayout.SOUTH);

                // Global window keyboard handler (SPACE/UP/W = Jump, DOWN/S = Duck, ESC/P = Pause)
                KeyboardFocusManager.getCurrentKeyboardFocusManager().addKeyEventDispatcher(new KeyEventDispatcher() {
                    private boolean jumpKeyHeld = false;
                    private boolean escKeyHeld = false;

                    @Override
                    public boolean dispatchKeyEvent(KeyEvent e) {
                        // Do not intercept keys if a modal dialog (like JFileChooser) is currently active!
                        Window activeWin = KeyboardFocusManager.getCurrentKeyboardFocusManager().getActiveWindow();
                        if (activeWin != null && activeWin != frame) {
                            return false;
                        }

                        int code = e.getKeyCode();
                        if (e.getID() == KeyEvent.KEY_PRESSED) {
                            if (code == KeyEvent.VK_ESCAPE || code == KeyEvent.VK_P) {
                                if (!escKeyHeld) {
                                    escKeyHeld = true;
                                    game.togglePause();
                                }
                                return true;
                            } else if (code == KeyEvent.VK_SPACE || code == KeyEvent.VK_UP || code == KeyEvent.VK_W) {
                                if (!jumpKeyHeld) {
                                    jumpKeyHeld = true;
                                    game.triggerJump();
                                }
                                return true;
                            } else if (code == KeyEvent.VK_DOWN || code == KeyEvent.VK_S) {
                                game.setDuck(true);
                                return true;
                            }
                        } else if (e.getID() == KeyEvent.KEY_RELEASED) {
                            if (code == KeyEvent.VK_ESCAPE || code == KeyEvent.VK_P) {
                                escKeyHeld = false;
                                return true;
                            } else if (code == KeyEvent.VK_SPACE || code == KeyEvent.VK_UP || code == KeyEvent.VK_W) {
                                jumpKeyHeld = false;
                                return true;
                            } else if (code == KeyEvent.VK_DOWN || code == KeyEvent.VK_S) {
                                game.setDuck(false);
                                return true;
                            }
                        }
                        return false;
                    }
                });

                frame.addWindowListener(new WindowAdapter() {
                    @Override
                    public void windowClosing(WindowEvent e) {
                        game.stopGameLoop();
                    }
                });

                frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
                frame.setContentPane(root);
                frame.setResizable(false);
                frame.pack();
                frame.setLocationRelativeTo(null);
                frame.setVisible(true);

                game.requestFocusInWindow();
                game.startGameLoop();
            }
        });
    }
}
