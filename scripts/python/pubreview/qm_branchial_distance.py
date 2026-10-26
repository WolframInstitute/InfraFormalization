"""Branchial distance against common-ancestor depth, Complex Systems 29(2) 537-598.

Lines 1504-1516 of papers/gorard_complexsystems_29_2.txt: two states of a branchlike
hypersurface that both follow from a common state by one event are at distance one, "and
otherwise they are separated by the number of levels back in the multiway hierarchy that one
must traverse in order to find their common ancestor state"; disconnections "generally only"
happen with more than one initial condition or when the hypersurface outgrows the maximum
entanglement rate.

The branchial graph at step n joins two distinct states of step n that are one-step successors
of a common state (the paper's definition of a branch pair, lines 1508-1510). The ancestor depth
of a pair is the least k such that some state of step n-k reaches both. Both are computed on the
HGEvolve multiway graph with "CanonicalizeStates" -> "Full" (states identified up to
isomorphism) and on the multiway tree without canonicalisation. Every run has one initial state.
"""
import collections
import json

from hg_env import evolve

CASES = [
    ("wolfram_signature_rule", ([["x", "y"], ["x", "z"]],
                                [["x", "y"], ["x", "w"], ["y", "w"], ["z", "w"]]),
     [[1, 2], [1, 3]], 3),
    ("path_growth", ([["x", "y"]], [["x", "y"], ["y", "z"]]), [[1, 2], [2, 3]], 4),
    ("gorard_g3_rule", ([["x", "y"], ["y", "z"], ["z", "w"], ["w", "v"]],
                        [["y", "u"], ["u", "v"], ["w", "x"], ["x", "u"]]),
     [[i, i + 1] for i in range(1, 9)], 3),
]


def analyse(r, canonical):
    key_in = "CanonicalInputState" if canonical else "InputState"
    key_out = "CanonicalOutputState" if canonical else "OutputState"
    sid = "CanonicalId" if canonical else "Id"
    step = {}
    for s in r.states.records():
        step.setdefault(s[sid], s["Step"])
        step[s[sid]] = min(step[s[sid]], s["Step"])
    children = collections.defaultdict(set)
    for e in r.events.records():
        children[e[key_in]].add(e[key_out])
    nmax = max(step.values())
    level = collections.defaultdict(set)
    for s, k in step.items():
        level[k].add(s)
    # Descendants at the final level of each state, by level.
    desc = {}
    for k in range(nmax, -1, -1):
        for s in level[k]:
            if k == nmax:
                desc[s] = {s}
            else:
                desc[s] = set().union(*[desc[c] for c in children[s] if step.get(c) == k + 1]) \
                    if children[s] else set()
    final = sorted(level[nmax])
    adj = collections.defaultdict(set)
    for p in level[nmax - 1]:
        kids = [c for c in children[p] if step.get(c) == nmax]
        for a in kids:
            for b in kids:
                if a != b:
                    adj[a].add(b)

    def bfs(src):
        d = {src: 0}
        q = collections.deque([src])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v not in d:
                    d[v] = d[u] + 1
                    q.append(v)
        return d

    counts = collections.Counter()
    examples = []
    for i, a in enumerate(final):
        da = bfs(a)
        for b in final[i + 1:]:
            depth = next(k for k in range(1, nmax + 1)
                         if any(a in desc[s] and b in desc[s] for s in level[nmax - k]))
            dist = da.get(b)
            if dist is None:
                counts["disconnected_with_common_ancestor"] += 1
                if len(examples) < 3:
                    examples.append({"pair": [a, b], "ancestor_depth": depth, "distance": None})
            elif dist == depth:
                counts["distance_equals_depth"] += 1
            else:
                counts["distance_differs_from_depth"] += 1
                if len(examples) < 6:
                    examples.append({"pair": [a, b], "ancestor_depth": depth, "distance": dist})
    return {"final_step": nmax, "final_states": len(final), "pairs": dict(counts),
            "examples": examples}


def main():
    out = {}
    for name, rule, init, steps in CASES:
        for canonical in (True, False):
            r = evolve([rule], init, steps,
                       canonicalize_states="Full" if canonical else None)
            res = analyse(r, canonical)
            key = f"{name}/{'Full' if canonical else 'tree'}"
            out[key] = res
            print(key, json.dumps(res), flush=True)
    with open("../../../results/publication_review/qm_branchial_distance.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
