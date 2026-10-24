# Digitises the rPsi4 curves of G3 Figs 39, 49, 78, 84 and Gravitas II Fig 54 from the
# PNG files of the TeX sources and compares them on a common time grid.
# Calibration: pixel positions of the labelled major ticks, read with axes_probe.py.
# Run from the repository root: python3 -I scripts/python/digitise_rpsi4.py
# Output: results/phase2_continuum/digitise_rpsi4.out
# Requires numpy and Pillow.
import os

import numpy as np
from PIL import Image

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
G3 = os.path.join(ROOT, "papers", "tex_2102") + os.sep
GII = os.path.join(ROOT, "papers", "tex_2401") + os.sep
BLUE, ORANGE, GREEN = (94, 129, 181), (225, 156, 36), (143, 176, 50)

# name: file, x tick px for t=2 and t=12, y tick px for two values, plot column range
PLOTS = {
    "G3 Fig39 CCZ4 Schw": (G3 + "NumericalRelativity104.png", (161, 615), ((64, 0.004), (380, -0.004)), (72, 640)),
    "G3 Fig49 CCZ4 Kerr": (G3 + "NumericalRelativity132.png", (162, 616), ((51, 0.004), (319, -0.002)), (73, 640)),
    "G3 Fig78 WM Schw": (G3 + "NumericalRelativity177.png", (133, 619), ((86, 0.004), (354, -0.004)), (76, 645)),
    "G3 Fig84 WM Kerr": (G3 + "NumericalRelativity178.png", (131, 617), ((63, 0.004), (353, -0.004)), (74, 645)),
    "GII Fig54 Schw": (GII + "GravitasFigure104.png", (192, 735), ((40, 0.004), (429, -0.004)), (85, 760)),
}

def trace(name, colour, tol=45):
    path, (x2, x12), ((ya, va), (yb, vb)), (c0, c1) = PLOTS[name]
    a = np.asarray(Image.open(path).convert("RGB")).astype(int)
    d = np.sqrt(((a - np.array(colour)) ** 2).sum(axis=2))
    ts, vs = [], []
    for c in range(c0 + 1, c1):
        rows = np.nonzero(d[:, c] < tol)[0]
        if len(rows) == 0:
            continue
        r = rows.mean()
        ts.append(2 + 10 * (c - x2) / (x12 - x2))
        vs.append(va + (vb - va) * (r - ya) / (yb - ya))
    return np.array(ts), np.array(vs)

grid = np.arange(1.4, 11.8, 0.02)

def on_grid(name, colour):
    t, v = trace(name, colour)
    return np.interp(grid, t, v), (t.min(), t.max(), len(t))

def smooth(v, width):
    k = np.ones(width) / width
    return np.convolve(v, k, mode="same")

curves = {}
for name in PLOTS:
    col = BLUE if name.startswith("GII") else GREEN
    v, info = on_grid(name, col)
    curves[name] = v
    i = np.argmax(v)
    j = np.argmin(v)
    print(f"{name}: columns {info[2]}, t range {info[0]:.2f}-{info[1]:.2f}, max {v[i]:.5f} at t={grid[i]:.2f}, min {v[j]:.5f} at t={grid[j]:.2f}", flush=True)

def compare(a, b, sm=1):
    x, y = smooth(curves[a], sm), smooth(curves[b], sm)
    sl = slice(sm, len(grid) - sm)
    x, y = x[sl], y[sl]
    r = np.corrcoef(x, y)[0, 1]
    rms = np.sqrt(np.mean((x - y) ** 2))
    print(f"{a} vs {b} (moving average {sm * 0.02:.2f} M): Pearson r = {r:.3f}, RMS difference = {rms:.2e}, RMS of first = {np.sqrt(np.mean(x ** 2)):.2e}", flush=True)

pairs = [("G3 Fig39 CCZ4 Schw", "GII Fig54 Schw"), ("G3 Fig39 CCZ4 Schw", "G3 Fig78 WM Schw"),
         ("G3 Fig49 CCZ4 Kerr", "G3 Fig84 WM Kerr"), ("G3 Fig39 CCZ4 Schw", "G3 Fig49 CCZ4 Kerr"),
         ("G3 Fig78 WM Schw", "G3 Fig84 WM Kerr"), ("G3 Fig39 CCZ4 Schw", "G3 Fig84 WM Kerr"),
         ("G3 Fig49 CCZ4 Kerr", "G3 Fig78 WM Schw")]
for a, b in pairs:
    compare(a, b, 1)
    compare(a, b, 15)

# Time-rescaling test: Gravitas II masses M each, separation 2M is G3's system (0.5M, 1M) scaled by 2.
# Correlation of the Gravitas II curve against the G3 CCZ4 curve with the time axis stretched by s.
tg, vg = trace("GII Fig54 Schw", BLUE)
t3, v3 = trace("G3 Fig39 CCZ4 Schw", GREEN)
for s in (0.5, 1.0, 2.0):
    g = np.arange(1.4, 11.8, 0.02)
    ok = (g / s >= t3.min()) & (g / s <= t3.max()) & (g >= tg.min()) & (g <= tg.max())
    if ok.sum() < 50:
        print(f"stretch {s}: overlap too short ({ok.sum()} points)", flush=True)
        continue
    x = np.interp(g[ok], tg, vg)
    y = np.interp(g[ok] / s, t3, v3)
    print(f"stretch {s}: Pearson r = {np.corrcoef(x, y)[0, 1]:.3f} over {ok.sum()} points", flush=True)
