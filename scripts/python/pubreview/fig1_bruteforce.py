"""Independent count of the multiway states of Figure 1 of arXiv:2105.10822.

Rule {{x,y},{y,z}} -> {{w,y},{y,z},{z,w},{x,w}} from {{0,0},{0,0}}, 3 steps. A match is an
ordered pair of distinct edge occurrences (e1, e2) with e1[1] = e2[0]; x, y, z may coincide.
w is a new vertex. States are identified up to vertex relabelling by brute force over all
vertex permutations (at most 4 vertices at step 3)."""
import itertools
import json


def canon(state):
    vs = sorted({v for e in state for v in e})
    best = None
    for perm in itertools.permutations(range(len(vs))):
        m = dict(zip(vs, perm))
        key = tuple(sorted(tuple(m[v] for v in e) for e in state))
        if best is None or key < best:
            best = key
    return best


def successors(state):
    out = []
    n = max(v for e in state for v in e) + 1
    for i, j in itertools.permutations(range(len(state)), 2):
        (x, y), (y2, z) = state[i], state[j]
        if y != y2:
            continue
        rest = [e for k, e in enumerate(state) if k not in (i, j)]
        w = n
        out.append(rest + [(w, y), (y, z), (z, w), (x, w)])
    return out


def main():
    level = {canon([(0, 0), (0, 0)]): [(0, 0), (0, 0)]}
    counts = [1]
    pairs_into = []
    for _ in range(3):
        nxt, pairs = {}, set()
        for c, s in level.items():
            for t in successors(s):
                ct = canon(t)
                nxt.setdefault(ct, t)
                pairs.add((c, ct))
        counts.append(len(nxt))
        pairs_into.append(len(pairs))
        level = nxt
    out = {"states_per_step": counts, "distinct_state_pairs_into_step": pairs_into}
    print(json.dumps(out))
    with open("../../../results/publication_review/fig1_bruteforce.json", "w") as f:
        json.dump(out, f)


if __name__ == "__main__":
    main()
