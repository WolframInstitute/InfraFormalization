# Prints candidate axis rows/columns and tick positions of a Mathematica Plot PNG.
# Usage: python3 -I scripts/python/axes_probe.py papers/tex_2102/NumericalRelativity104.png ...
# The tick pixels in the PLOTS table of digitise_rpsi4.py were read with this script.
import sys
import numpy as np
from PIL import Image

def gray_mask(a):
    r, g, b = a[..., 0].astype(int), a[..., 1].astype(int), a[..., 2].astype(int)
    return (abs(r - g) < 12) & (abs(g - b) < 12) & (r < 200) & (r > 40)

for path in sys.argv[1:]:
    a = np.asarray(Image.open(path).convert("RGB"))
    h, w, _ = a.shape
    m = gray_mask(a)
    rows = m.sum(axis=1)
    cols = m.sum(axis=0)
    ar = int(np.argmax(rows))
    ac = int(np.argmax(cols[: w // 3]))
    print(path, "size", w, h, "axis row", ar, "count", rows[ar], "axis col", ac, "count", cols[ac], flush=True)
    # x ticks: gray pixels in the rows just above the axis row, outside the axis column
    above = [c for c in range(w) if m[ar - 2, c] and m[ar - 3, c] and c != ac]
    lens = {}
    for c in above:
        L = 0
        while ar - 1 - L >= 0 and m[ar - 1 - L, c]:
            L += 1
        lens[c] = L
    print(" x tick cols (len):", [(c, lens[c]) for c in above], flush=True)
    right = [r for r in range(h) if m[r, ac + 2] and m[r, ac + 3] and r != ar]
    rl = {}
    for r in right:
        L = 0
        while ac + 1 + L < w and m[r, ac + 1 + L]:
            L += 1
        rl[r] = L
    print(" y tick rows (len):", [(r, rl[r]) for r in right], flush=True)
