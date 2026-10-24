"""Check the Hamiltonian-constraint convergence tables of arXiv:2102.09363 (G3,
Tables 1-7) and arXiv:2303.07282 (G4, Tables 1-4) against the norm definitions
of the papers.

G3 eqs. 180-181 (papers/gorard_2102.09363.txt lines 2671-2687) and G4 eqs.
186-187 (papers/gorard_2303.07282.txt lines 2955-2968) define

    L1 = sum_i m_i |H_i|,  L2 = (sum_i m_i H_i^2)^(1/2),  Linf = max_i m_i |H_i|

with m_i = V_i / V_tot, so m_i >= 0 and sum_i m_i <= 1. Every term of L1 is
non-negative, so Linf <= L1, and the Cauchy-Schwarz inequality gives
L1^2 <= (sum_i m_i)(sum_i m_i H_i^2) <= L2^2. Every row must satisfy
Linf <= L1 <= L2.

A row line of the text files has the vertex count (100 to 1600), three norms
written as "a × 10−b" (L1, L2, Linf) and the printed orders. A table starts at
its 100-vertex row. Each order is recomputed as log2 of the ratio of a norm to
the norm at the next vertex count, rounded to 0.01, and compared with the
printed order.

Run from the repository root: python3 -I scripts/python/check_convergence_tables.py
Output: results/phase2_continuum/convergence_tables.out
"""
import math
import os
import re

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
FILES = {"G3": os.path.join(ROOT, "papers", "gorard_2102.09363.txt"),
         "G4": os.path.join(ROOT, "papers", "gorard_2303.07282.txt")}
NUM = r"([0-9.]+) × 10−([0-9]+)"
ROW = re.compile(r"^\s*(100|200|400|800|1600)\s+" + NUM + r"\s+" + NUM + r"\s+" + NUM + r"(.*)$")
NAMES = ("L1", "L2", "Linf")


def main():
    for tag, path in FILES.items():
        table = 0
        prev = None
        rows = {}
        bad = {}
        mismatches = []
        with open(path, encoding="utf-8") as f:
            lines = f.read().split("\n")
        for i, line in enumerate(lines, 1):
            m = ROW.match(line)
            if not m:
                continue
            n = int(m.group(1))
            if n == 100:
                table += 1
                prev = None
            v = [float(m.group(2 + 2 * k)) * 10 ** -int(m.group(3 + 2 * k)) for k in range(3)]
            printed = [float(x) for x in m.group(8).split() if re.match(r"^[0-9.]+$", x)]
            computed = [round(math.log2(prev[k] / v[k]), 2) for k in range(3)] if prev else []
            ordered = v[2] <= v[0] <= v[1]
            rows[table] = rows.get(table, 0) + 1
            if not ordered:
                bad[table] = bad.get(table, 0) + 1
            for k, (c, p) in enumerate(zip(computed, printed)):
                if abs(c - p) > 0.011:
                    mismatches.append((table, i, n, NAMES[k], c, p))
            print(f"{tag} table {table} line {i} n {n} L1 {v[0]:.3g} L2 {v[1]:.3g} Linf {v[2]:.3g} "
                  f"Linf<=L1<=L2 {ordered} orders computed {computed} printed {printed}", flush=True)
            prev = v
        total = sum(rows.values())
        nbad = sum(bad.values())
        print(f"{tag}: {nbad} of {total} rows violate Linf <= L1 <= L2; per table: "
              + ", ".join(f"table {t} {bad.get(t, 0)} of {rows[t]}" for t in sorted(rows)), flush=True)
        print(f"{tag}: {len(mismatches)} printed orders differ from the recomputed orders by more than 0.01", flush=True)
        for t, i, n, name, c, p in mismatches:
            print(f"{tag}: table {t} line {i} n {n} {name} order computed {c} printed {p}", flush=True)


if __name__ == "__main__":
    main()
