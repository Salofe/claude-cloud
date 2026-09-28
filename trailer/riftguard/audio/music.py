# Riftguard trailer score: fully synthesized, 30.0 s, 120 BPM, D minor.
import numpy as np
from scipy import signal
from scipy.io import wavfile
SR = 48000; DUR = 30.0; N = int(SR * DUR)
BPM = 120; BEAT = 60 / BPM; BAR = BEAT * 4
rng = np.random.default_rng(7)
def T(n): return np.arange(n) / SR
def midi(m): return 440.0 * 2 ** ((m - 69) / 12)
NOTE = {'C':0,'C#':1,'D':2,'Eb':3,'E':4,'F':5,'F#':6,'G':7,'Ab':8,'A':9,'Bb':10,'B':11}
def nm(s):  # 'D3' -> midi
    return 12 * (int(s[-1]) + 1) + NOTE[s[:-1]]

class Bus:
    def __init__(s): s.L = np.zeros(N + SR * 8); s.R = np.zeros(N + SR * 8)
    def add(s, t0, x, gain=1.0, pan=0.0):
        i = int(round(t0 * SR));
        if x.ndim == 1: x = np.stack([x, x])
        l, r = x[0] * gain * np.sqrt((1 - pan) / 2) * 1.414, x[1] * gain * np.sqrt((1 + pan) / 2) * 1.414
        j = min(len(s.L), i + len(l)); n = j - i
        if n <= 0 or i < 0: return
        s.L[i:j] += l[:n]; s.R[i:j] += r[:n]
    def arr(s): return np.stack([s.L[:N], s.R[:N]])

def env_adsr(n, a=0.005, d=0.1, sus=0.7, r=0.1, hold=None):
    t = T(n); hold = (n / SR - r) if hold is None else hold
    e = np.where(t < a, t / max(a, 1e-6), sus + (1 - sus) * np.exp(-(t - a) / max(d, 1e-6)))
    rel = np.clip((t - hold) / max(r, 1e-6), 0, 1)
    return e * (1 - rel)
def saw(f, n, ph=0.0):
    # band-limited-ish saw via polyBLEP
    f = np.broadcast_to(np.asarray(f, float), (n,))
    inc = f / SR; p = (np.cumsum(inc) + ph) % 1.0
    y = 2 * p - 1
    t = p; dt = np.maximum(inc, 1e-9)
    m1 = t < dt; x = t[m1] / dt[m1]; y[m1] -= x + x - x * x - 1
    m2 = t > 1 - dt; x = (t[m2] - 1) / dt[m2]; y[m2] -= x * x + x + x + 1
    return y
def sine(f, n, ph=0.0):
    f = np.broadcast_to(np.asarray(f, float), (n,))
    return np.sin(2 * np.pi * (np.cumsum(f) / SR) + ph)
def noise(n): return rng.standard_normal(n)
def lp(x, fc, q=0.707):
    b, a = signal.butter(2, min(fc, SR * 0.45) / (SR / 2), 'low'); return signal.lfilter(b, a, x)
def hp(x, fc):
    b, a = signal.butter(2, fc / (SR / 2), 'high'); return signal.lfilter(b, a, x)
def bp(x, lo, hi):
    b, a = signal.butter(2, [lo / (SR / 2), min(hi, SR * 0.45) / (SR / 2)], 'band'); return signal.lfilter(b, a, x)
def svf_sweep(x, fc_curve, res=0.3):
    # time-varying state-variable lowpass (per-sample cutoff)
    y = np.zeros_like(x); lo = bd = 0.0
    fcs = np.clip(fc_curve, 20, SR * 0.2); f = 2 * np.sin(np.pi * fcs / SR); q = 1 - res
    for i in range(len(x)):
        hi_ = x[i] - lo - q * bd; bd += f[i] * hi_; lo += f[i] * bd; y[i] = lo
    return y
def reverb_ir(sec=2.5, damp=3.0, seed=1):
    r = np.random.default_rng(seed); n = int(SR * sec); t = T(n)
    irs = []
    for c in range(2):
        e = r.standard_normal(n) * np.exp(-t * damp)
        e = lp(e, 6000) ; e[:int(0.012 * SR)] *= np.linspace(0, 1, int(0.012 * SR))
        irs.append(e / np.sqrt(np.sum(e ** 2)))
    return irs
IR_BIG = reverb_ir(3.2, 2.2, 1); IR_MED = reverb_ir(1.6, 4.0, 2)
def verb(st, ir, wet):
    out = []
    for c in range(2):
        w = signal.fftconvolve(st[c], ir[c])[:len(st[c]) + len(ir[c]) - 1]
        d = np.zeros_like(w); d[:len(st[c])] = st[c]
        out.append(d + w * wet)
    return np.stack(out)

# ---------------- instruments ----------------
def kick(big=False):
    n = int(SR * (1.2 if big else 0.45)); t = T(n)
    f = 42 + 110 * np.exp(-t * (18 if not big else 10)); a = np.exp(-t * (7 if not big else 2.6))
    x = np.tanh(2.2 * sine(f, n) * a) 
    click = hp(noise(n), 2000) * np.exp(-t * 400) * 0.35
    return x + click
def impact():
    n = int(SR * 3.0); t = T(n)
    body = np.tanh(2.5 * sine(38 + 90 * np.exp(-t * 7), n) * np.exp(-t * 3.2)) * 0.8
    crack = lp(noise(n), 3500) * np.exp(-t * 12) * 1.0
    boom = lp(noise(n), 160) * np.exp(-t * 4.0) * 1.0
    x = np.stack([body + crack + boom, body + crack * 0.9 + boom])
    return verb(x, IR_BIG, 0.3)[:, :n + SR]
def snare():
    n = int(SR * 0.5); t = T(n)
    tone = sine(185 * (1 + 0.5 * np.exp(-t * 40)), n) * np.exp(-t * 22)
    nz = bp(noise(n), 900, 9000) * np.exp(-t * 14)
    return np.tanh(1.5 * (tone * 0.7 + nz))
def clap():
    n = int(SR * 0.4); t = T(n); e = np.zeros(n)
    for k, dt in enumerate([0, 0.011, 0.023, 0.034]):
        i = int(dt * SR); e[i:] += np.exp(-(t[: n - i]) * (60 if k < 3 else 16))
    return bp(noise(n), 1000, 6000) * e
def hat(open_=False):
    n = int(SR * (0.35 if open_ else 0.06)); t = T(n)
    return hp(noise(n), 7000) * np.exp(-t * (9 if open_ else 70))
def taiko(f=70):
    n = int(SR * 1.0); t = T(n)
    return np.tanh(2 * (sine(f * (1 + 0.4 * np.exp(-t * 30)), n) * np.exp(-t * 5) + lp(noise(n), 600) * np.exp(-t * 25) * 0.8))
def braam(root, dur=2.2, bright=1.0):
    n = int(SR * dur); t = T(n)
    notes = [root - 12, root, root + 7, root + 12]
    x = np.zeros(n)
    for m in notes:
        for d in (-0.12, 0.0, 0.11):
            x += saw(midi(m) * 2 ** (d / 12), n, rng.random())
    fc = 120 + 2600 * bright * np.exp(-t * 1.8) * (1 - np.exp(-t * 40))
    y = svf_sweep(x / 12, fc, 0.25)
    y = np.tanh(2.5 * y) * np.minimum(1, t / 0.02) * np.exp(-np.maximum(0, t - dur + 0.8) * 4)
    sub = sine(midi(root), n) * np.exp(-t * 1.5) * 0.35
    return np.stack([y + sub, y * 0.95 + sub])
def pluck(m, dur=0.22, cut=3500):
    n = int(SR * dur); t = T(n)
    x = (saw(midi(m), n) + saw(midi(m) * 1.006, n) + 0.5 * saw(midi(m) * 0.5, n)) / 2.5
    y = lp(x * np.exp(-t * 3), 800) * 0.2 + svf_sweep(x, 300 + cut * np.exp(-t * 18), 0.35)
    return y * env_adsr(n, 0.002, 0.08, 0.3, 0.05)
def lead(m, dur, vib=True):
    n = int(SR * dur); t = T(n)
    f = midi(m) * (1 + (0.006 * np.sin(2 * np.pi * 5.5 * t) * np.clip((t - 0.15) / 0.2, 0, 1) if vib else 0))
    x = sum(saw(f * 2 ** (d / 1200), n, rng.random()) for d in (-9, -3, 3, 9)) / 4 + 0.35 * sine(f / 2, n)
    y = lp(np.tanh(1.4 * x), 5200)
    return y * env_adsr(n, 0.01, 0.2, 0.75, 0.08)
def bass_note(m, dur):
    n = int(SR * dur); t = T(n)
    x = saw(midi(m), n) + 0.35 * sine(midi(m), n)
    y = svf_sweep(x, 180 + 900 * np.exp(-t * 14), 0.3)
    return np.tanh(1.6 * y) * env_adsr(n, 0.003, 0.1, 0.8, 0.04)
def pad(ms, dur, cut=1800):
    n = int(SR * dur); t = T(n); ms = [nm(m) if isinstance(m, str) else m for m in ms]
    x = np.zeros(n)
    for m in ms:
        for d in (-7, 0, 7): x += saw(midi(m) * 2 ** (d / 1200), n, rng.random())
    y = lp(x / (3 * len(ms)), cut)
    e = np.minimum(1, t / 0.6) * np.minimum(1, (dur - t) / 0.8)
    return y * e
def stab(ms, dur=0.45):
    n = int(SR * dur); t = T(n); x = np.zeros(n)
    for m in ms:
        for d in (-10, 0, 10): x += saw(midi(m) * 2 ** (d / 1200), n, rng.random())
    y = svf_sweep(x / (3 * len(ms)), 400 + 5000 * np.exp(-t * 9), 0.2)
    return np.tanh(2 * y) * env_adsr(n, 0.004, 0.15, 0.3, 0.1)
def riser(dur):
    n = int(SR * dur); t = T(n); k = t / dur
    nz = noise(n); y = np.zeros(n)
    # sweeping bandpass via blocks
    B = 1024
    for i in range(0, n, B):
        c = 300 * (40 ** k[i]); seg = nz[max(0, i - 256): i + B]
        f = bp(seg, c * 0.7, c * 1.4)[-min(B, n - i):]
        y[i:i + len(f)] = f
    tone = saw(midi(nm('D3')) * 2 ** (2 * k), n) * 0.25
    return (y * 1.5 + svf_sweep(tone, 2000 + 6000 * k, 0.2)) * (k ** 2.2)
def rev_cymbal(dur):
    n = int(SR * dur); t = T(n); k = t / dur
    return hp(noise(n), 3000) * (k ** 3) * 0.9
def whoosh(dur=0.5, up=True):
    n = int(SR * dur); t = T(n); k = t / dur
    nz = noise(n); y = np.zeros(n); B = 512
    for i in range(0, n, B):
        c = (400 * (12 ** k[i])) if up else (5000 * (0.08 ** k[i]))
        seg = nz[max(0, i - 256): i + B]; f = bp(seg, c * 0.6, c * 1.6)[-min(B, n - i):]; y[i:i + len(f)] = f
    return y * np.sin(np.pi * k) ** 1.5
def tick():
    n = int(SR * 0.03); t = T(n)
    return hp(noise(n), 4000) * np.exp(-t * 200) + sine(2400, n) * np.exp(-t * 300) * 0.3

# ---------------- arrangement ----------------
drums = Bus(); music = Bus(); fx = Bus(); bass = Bus(); lead_b = Bus()
b = lambda bar, beat=0.0: bar * BAR + beat * BEAT   # bar index from 0
PROG = [('D', ['D4','F4','A4']), ('Bb', ['Bb3','D4','F4']), ('F', ['F3','A3','C4']), ('C', ['C4','E4','G4'])]
ROOT = {'D':'D2','Bb':'Bb1','F':'F2','C':'C2'}

# HOOK 0-4s: three braams on 0,1,2 s; ticking clock; riser into 4.0
for i, (tt, r, br) in enumerate([(0.0, nm('D2'), 0.9), (1.0, nm('D2'), 1.0), (2.0, nm('F2'), 1.1)]):
    music.add(tt, braam(r, 0.95, br), 0.5)
    drums.add(tt, impact(), 0.8)
for k in range(24):
    tt = 0.25 + k * 0.125
    if tt < 3.0: fx.add(tt, tick(), 0.18 if k % 2 == 0 else 0.1, pan=(-0.3 if k % 2 else 0.3))
fx.add(2.9, riser(1.1), 0.55)
fx.add(3.0, rev_cymbal(1.0), 0.6)
for k in range(8): drums.add(3.0 + k * 0.125, snare(), 0.10 + k * 0.04)   # snare roll
for k in range(8): drums.add(3.5 + k * 0.0625, snare(), 0.25 + k * 0.03)

def beat_bar(bar, full=True, hats=True, fill=False):
    t0 = b(bar)
    # hybrid trailer groove: kick on 1, &2, 3 (+ ghost), clap/snare on 2 and 4
    for bt in [0, 1.5, 2, 3.75] if full else [0, 2]:
        drums.add(t0 + bt * BEAT, kick(), 0.95)
    for bt in [1, 3]:
        drums.add(t0 + bt * BEAT, snare(), 0.55); drums.add(t0 + bt * BEAT, clap(), 0.35)
    if hats:
        for k in range(16):
            drums.add(t0 + k * BEAT / 4, hat(k % 4 == 2), 0.12 if k % 2 else 0.2, pan=0.25)
    if fill:
        for k, f in enumerate([90, 80, 70, 62, 55, 50]):
            drums.add(t0 + 2.5 * BEAT + k * BEAT / 4, taiko(f), 0.5)
def bass_bar(bar, chord, dens=8):
    r = nm(ROOT[chord])
    for k in range(dens):
        bass.add(b(bar) + k * BAR / dens, bass_note(r + (12 if k % 2 else 0), BAR / dens * 0.9), 0.5)
def arp_bar(bar, notes, oct_=0, g=0.22):
    seq = [0, 1, 2, 1, 0, 2, 1, 2] * 2
    for k in range(16):
        m = nm(notes[seq[k]]) + 12 + oct_
        music.add(b(bar) + k * BEAT / 4, pluck(m, 0.2), g, pan=(0.35 if k % 2 else -0.35))

# DROP / ACT 1 (bars 2-5 = 4.0-12.0)
drums.add(4.0, impact(), 1.0); music.add(4.0, braam(nm('D2'), 1.8, 1.2), 0.45)
for i, bar in enumerate(range(2, 6)):
    ch, notes = PROG[i % 4]
    beat_bar(bar, fill=(bar in (3, 5)))
    bass_bar(bar, ch)
    arp_bar(bar, notes)
    music.add(b(bar), pad([n for n in notes], BAR, 1400), 0.18)
# cut accents act1 (every second)
for s in np.arange(5.0, 12.0, 1.0): fx.add(s - 0.18, whoosh(0.3), 0.12, pan=0.0)

# ROLL CALL (bars 6-7 = 12.0-16.0): stabs on every half-second cut, half-time drums, ticking
for k in range(8):
    tt = 12.0 + k * 0.5
    ch, notes = PROG[(k // 4) % 2]
    music.add(tt, stab([nm(n) for n in notes] + [nm(notes[0]) + 12], 0.42), 0.35)
    drums.add(tt, kick(), 0.8 if k % 2 == 0 else 0.55)
    drums.add(tt, taiko(75 if k % 2 else 60), 0.45)
    fx.add(tt - 0.08, whoosh(0.16), 0.1)
for bar in (6, 7):
    for bt in [1, 3]: drums.add(b(bar, bt), snare(), 0.45)
    for k in range(16): drums.add(b(bar) + k * BEAT / 4, hat(), 0.12, pan=-0.2)
    bass_bar(bar, PROG[bar - 6][0], 4)
fx.add(14.9, riser(1.1), 0.45); fx.add(15.2, rev_cymbal(0.8), 0.5)

# CLIMAX (bars 8-11 = 16.0-24.0)
drums.add(16.0, impact(), 1.0); music.add(16.0, braam(nm('D2'), 1.8, 1.3), 0.4)
MEL = [  # (beat offset from 16.0, note, beats)
    (0, 'A4', 1), (1, 'D5', 1), (2, 'F5', 1), (3, 'A5', 1),
    (4, 'G5', 1), (5, 'F5', 1), (6, 'D5', 1), (7, 'F5', 1),
    (8, 'A5', 1), (9, 'C6', 1), (10, 'A5', 1), (11, 'F5', 1),
    (12, 'G5', 1.5), (13.5, 'E5', 0.5), (14, 'C5', 0.5), (14.5, 'E5', 0.5), (15, 'G5', 1)]
for bar in range(8, 12):
    i = bar - 8; ch, notes = PROG[i]
    slow = (bar == 10 and False)
    beat_bar(bar, fill=(bar == 11))
    bass_bar(bar, ch)
    arp_bar(bar, notes, 12, 0.16)
    music.add(b(bar), pad(notes + [notes[0][:-1] + str(int(notes[0][-1]) + 1)], BAR, 2400), 0.22)
for off, n_, beats in MEL:
    lead_b.add(16.0 + off * BEAT, lead(nm(n_), beats * BEAT * 0.95), 0.34)
    lead_b.add(16.0 + off * BEAT, lead(nm(n_) - 12, beats * BEAT * 0.95, False), 0.14)
# maps section hits (19.0-21.0) and teamfight impact at 21.0
for s in (19.0, 19.5, 20.0, 20.5): fx.add(s - 0.12, whoosh(0.22), 0.14)
drums.add(21.0, impact(), 0.75)
drums.add(23.0, impact(), 0.7)
fx.add(23.3, riser(0.7), 0.4); fx.add(23.4, rev_cymbal(0.6), 0.5)

# OUTRO: 24.0-24.5 silence (breath), 24.5 logo braam, pad tail, final hit
music.add(24.5, braam(nm('D2'), 3.2, 1.25), 0.65)
drums.add(24.5, impact(), 1.1)
music.add(24.5, pad(['D3', 'A3', 'D4', 'F4', 'A4'], 5.5, 1600), 0.3)
music.add(26.5, pad(['Bb2', 'F3', 'Bb3', 'D4', 'F4'], 3.5, 1300), 0.0)
for k in range(10):  # heartbeat pulse under the CTA
    tt = 26.5 + k * 0.5
    if tt < 29.3: drums.add(tt, kick(), 0.32 if k % 2 == 0 else 0.18)
    if tt < 29.3: fx.add(tt + 0.25, tick(), 0.08)
drums.add(29.35, impact(), 0.6)

# ---------------- mix ----------------
def sidechain(x, kick_times, depth=0.6, rel=0.18):
    g = np.ones(x.shape[1]); t = T(x.shape[1])
    for kt in kick_times:
        i = int(kt * SR); n = min(len(g) - i, int(rel * 3 * SR))
        if n <= 0: continue
        tt = t[:n]; g[i:i + n] = np.minimum(g[i:i + n], 1 - depth * np.exp(-tt / rel))
    return x * g
kt = []
for bar in list(range(2, 6)) + list(range(8, 12)):
    for bt in [0, 1.5, 2, 3.75]: kt.append(b(bar, bt))
D = verb(drums.arr(), IR_MED, 0.18)[:, :N]
M = verb(sidechain(music.arr(), kt, 0.45), IR_BIG, 0.22)[:, :N]
Bs = sidechain(bass.arr(), kt, 0.7)
L = lead_b.arr()
# ping-pong delay on lead
dl = int(SR * BEAT * 0.75); Ld = np.zeros_like(L)
for k in range(1, 5):
    g = 0.35 ** k; src = L[(k + 1) % 2]
    Ld[k % 2, dl * k:] += src[:-dl * k] * g
L = verb(L + Ld, IR_BIG, 0.3)[:, :N]
F = verb(fx.arr(), IR_BIG, 0.25)[:, :N]
mix = D * 0.85 + M * 0.95 + Bs * 0.5 + L * 1.1 + F * 0.9
# breath: duck everything 24.0-24.5 except tails of the riser
t = T(N); gate = np.ones(N)
gate[(t >= 24.05) & (t < 24.5)] = 0.08
mix *= gate
# gentle glue compression (RMS follower) + soft limiter
rms = np.sqrt(signal.lfilter([0.002], [1, -0.998], (mix ** 2).mean(0)) + 1e-9)
gain = np.minimum(1, (0.3 / rms) ** 0.18)
mix *= gain
mix = hp(mix[0], 32)[None, :] * 0 + np.stack([hp(mix[0], 32), hp(mix[1], 32)])
mix = np.stack([c - 0.45 * lp(c, 70) for c in mix])   # low-shelf cut on the sub
mix /= np.max(np.abs(mix)) + 1e-9
mix = np.tanh(mix * 2.2) / np.tanh(2.2)
mix /= np.max(np.abs(mix)) + 1e-9; mix *= 0.93
fade = np.minimum(1, (DUR - t) / 0.4); mix *= fade
wavfile.write('score.wav', SR, (mix.T * 32767).astype(np.int16))
print('wrote score.wav', mix.shape, 'peak', np.max(np.abs(mix)))
