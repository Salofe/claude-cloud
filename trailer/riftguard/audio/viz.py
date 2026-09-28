import numpy as np, sys
from scipy.io import wavfile
from scipy import signal
from PIL import Image, ImageDraw
sr, x = wavfile.read(sys.argv[1]); x = x.astype(float).mean(1) / 32768
f, t, S = signal.spectrogram(x, sr, nperseg=2048, noverlap=1536)
S = 10 * np.log10(S + 1e-12)
# log-frequency rows 30 Hz..16 kHz
H, W = 300, 1200
fl = np.geomspace(30, 16000, H)
rows = np.array([S[np.argmin(np.abs(f - q))] for q in fl])[::-1]
cols = np.linspace(0, rows.shape[1] - 1, W).astype(int); img = rows[:, cols]
img = np.clip((img + 110) / 80, 0, 1)
rgb = (np.stack([img ** 0.7, img ** 1.5, img ** 3], -1) * 255).astype(np.uint8)
im = Image.fromarray(rgb).convert('RGB'); d = ImageDraw.Draw(im)
dur = len(x) / sr
for s in range(0, int(dur) + 1): d.line([(s / dur * W, 0), (s / dur * W, 8)], fill=(255, 255, 255))
# loudness strip
win = int(sr * 0.05); r = np.sqrt(np.convolve(x ** 2, np.ones(win) / win, 'same'))
db = 20 * np.log10(r + 1e-9)
strip = Image.new('RGB', (W, 120), (10, 10, 10)); d2 = ImageDraw.Draw(strip)
pts = [(i, 120 - np.clip((db[int(i / W * (len(x) - 1))] + 50) / 50, 0, 1) * 115) for i in range(W)]
d2.line(pts, fill=(80, 220, 255), width=2)
for s in range(0, int(dur) + 1): d2.line([(s / dur * W, 110), (s / dur * W, 120)], fill=(255, 255, 255))
out = Image.new('RGB', (W, H + 120)); out.paste(im, (0, 0)); out.paste(strip, (0, H)); out.save(sys.argv[2])
for a, b in [(0, 4), (4, 12), (12, 16), (16, 24), (24, 24.5), (24.5, 30)]:
    seg = x[int(a * sr):int(b * sr)]; print(f'{a:5}-{b:5}s  rms {20*np.log10(np.sqrt(np.mean(seg**2))+1e-9):6.1f} dB  peak {20*np.log10(np.max(np.abs(seg))+1e-9):6.1f}')
