"""Run the rule {{x,y},{y,z},{z,w},{w,v}} -> {{y,u},{u,v},{w,x},{x,u}} with the
event order of the SetReplace 0.3.196 WL method (Kernel/setSubstitutionSystem$wl.m,
toNormalRules): the chosen match is the one whose last element in the state list
has the smallest position (Shortest over the matched prefix); outputs are appended
at the end of the list and unconsumed expressions keep their order.

Ties (equal last position) are broken by one of two candidate rules, selected by
--tie: "perm" (permutation index of the LHS order, then positions) or "pos"
(positions in list order, lexicographic).

Prints events, causal edge count (one per mediating expression, initial
expressions excluded) and C(r) for r >= 1 from event 1, plus the exponent fitted
over r in [r_max/4, 3 r_max/4], the window used by scripts/causal_dimension.wl.

Usage: python3 setreplace_order.py --tie pos
"""
import argparse
import itertools
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rewriter import seed  # noqa: E402

LHS = [("x", "y"), ("y", "z"), ("z", "w"), ("w", "v")]
PERMS = list(itertools.permutations(range(4)))


def matches(state):
    """All matches as tuples (p0, p1, p2, p3) of list positions for LHS edges 0..3."""
    by_src = {}
    for i, (_, (a, b)) in enumerate(state):
        by_src.setdefault(a, []).append(i)
    out = []
    for i0, (_, (x, y)) in enumerate(state):
        for i1 in by_src.get(y, []):
            if i1 == i0:
                continue
            z = state[i1][1][1]
            for i2 in by_src.get(z, []):
                if i2 in (i0, i1):
                    continue
                w = state[i2][1][1]
                for i3 in by_src.get(w, []):
                    if i3 in (i0, i1, i2):
                        continue
                    out.append((i0, i1, i2, i3))
    return out


def key(m, tie):
    last = max(m)
    order = tuple(sorted(range(4), key=lambda k: m[k]))  # LHS indices in list order
    if tie == "perm":
        return (last, PERMS.index(order), tuple(sorted(m)))
    return (last, tuple(sorted(m)), PERMS.index(order))


def run(init, max_events, tie):
    state = [(i, e) for i, e in enumerate(init)]  # (expression id, edge)
    creator = {i: 0 for i in range(len(init))}
    consumer = {}
    next_id = len(init)
    fresh = max(v for e in init for v in e) + 1
    events = 0
    while events < max_events:
        ms = matches(state)
        if not ms:
            break
        m = min(ms, key=lambda mm: key(mm, tie))
        events += 1
        (_, (x, y)), (_, (_, z)), (_, (_, w)), (_, (_, v)) = (state[p] for p in m)
        u = fresh
        fresh += 1
        for p in m:
            consumer[state[p][0]] = events
        keep = [s for k, s in enumerate(state) if k not in m]
        new = []
        for e in [(y, u), (u, v), (w, x), (x, u)]:
            creator[next_id] = events
            new.append((next_id, e))
            next_id += 1
        state = keep + new
    edges = [(creator[i], consumer[i]) for i in consumer if creator[i] != 0]
    return events, len(state), edges


def cone(events, edges, start=1):
    adj = {}
    for a, b in set(edges):
        adj.setdefault(a, []).append(b)
    dist = {start: 0}
    front = [start]
    while front:
        nxt = []
        for a in front:
            for b in adj.get(a, []):
                if b not in dist:
                    dist[b] = dist[a] + 1
                    nxt.append(b)
        front = nxt
    rmax = max(dist.values())
    return [(r, sum(1 for d in dist.values() if d <= r)) for r in range(1, rmax + 1)]


def fit(cr):
    if not cr:
        return None
    rmax = cr[-1][0]
    pts = [(r, c) for r, c in cr if rmax / 4 <= r <= 3 * rmax / 4]
    if len(pts) < 3:
        return None
    xs = [math.log(r) for r, _ in pts]
    ys = [math.log(c) for _, c in pts]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    return sum((a - mx) * (b - my) for a, b in zip(xs, ys)) / sum((a - mx) ** 2 for a in xs)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--tie", choices=["perm", "pos"], default="perm")
    a = p.parse_args()
    runs = [("4cycle", 200), ("5path", 200), ("6cycle", 500), ("8cycle", 500), ("10path", 500),
            ("20cycle", 1000), ("grid3_3", 300), ("grid3_4", 1000), ("grid3_5", 2000)]
    for name, n in runs:
        ev, size, edges = run(seed(name), n, a.tie)
        cr = cone(ev, edges) if ev > 1 else []
        f = fit(cr)
        print(f"{name:8s} events={ev:5d} state={size:4d} causal_edges={len(edges):5d} "
              f"exponent={'-' if f is None else f'{f:.3f}'} C(r)={[c for _, c in cr[:12]]}", flush=True)


if __name__ == "__main__":
    main()
