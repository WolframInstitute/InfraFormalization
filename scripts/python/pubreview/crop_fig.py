"""Crops and enlarges the bottom row of a figure for counting. Arguments: input, output,
top fraction, left fraction, right fraction."""
import sys
from PIL import Image

im = Image.open(sys.argv[1])
w, h = im.size
top, left, right = (float(a) for a in sys.argv[3:6])
c = im.crop((int(left * w), int(top * h), int(right * w), h))
c = c.resize((c.size[0] * 2, c.size[1] * 2))
c.save(sys.argv[2])
