"""Imports the hgevolve client of the engine checkout and caps memory.

The address space is capped by the caller (ulimit -v, at most 4 GB). Every evolution passes
"MemoryLimit" at 0.8 of that cap through the "Tuning" option."""
import os
import sys

ENGINE = "/home/fly/my_projects/efficient_rewriting_final"
sys.path.insert(0, os.path.join(ENGINE, "python"))

import hgevolve as hg  # noqa: E402

CAP_BYTES = 4 * 1024 ** 3
TUNING = {"MemoryLimit": int(0.8 * CAP_BYTES)}


def evolve(rules, initial, steps, **options):
    options.setdefault("tuning", TUNING)
    options.setdefault("threads", 1)
    return hg.evolve(rules, initial, steps, **options)
