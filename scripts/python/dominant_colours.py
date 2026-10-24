# Prints the most frequent non-white colours of each image (quantised to 8 levels per channel).
# Usage: python3 -I scripts/python/dominant_colours.py <image files>. Output for the files cited in
# notes/gravitas_close_reading.md: results/phase2_continuum/dominant_colours.out
import sys
import numpy as np
from PIL import Image
for path in sys.argv[1:]:
    a = np.asarray(Image.open(path).convert("RGB")).reshape(-1, 3).astype(int)
    a = a[(a.sum(axis=1) < 720)]
    q = (a // 32) * 32 + 16
    keys, counts = np.unique(q, axis=0, return_counts=True)
    order = np.argsort(-counts)[:6]
    print(path.split("/")[-1], [(tuple(int(x) for x in keys[i]), int(counts[i])) for i in order], flush=True)
