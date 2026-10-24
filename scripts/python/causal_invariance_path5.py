"""Complete multiway evolution of the rule of arXiv:2102.09363 line 6202,
    {{x,y},{y,z},{z,w},{w,v}} -> {{y,u},{u,v},{w,x},{x,u}},
from the directed path of five edges {{1,2},{2,3},{3,4},{4,5},{5,6}}.

Matches are enumerated with `matches` of setreplace_order.py (every injective
assignment of four distinct state edges to the left-hand side). Every complete
history (a sequence of events that ends in a state with no match) is
enumerated, with hyperedge identities, and the script prints:

- each complete history: its events (consumed and created edge identities),
  its causal edges (event i -> event j when j consumes an edge created by i),
  and its terminal state with vertex and edge counts;
- the states up to isomorphism (brute force over vertex permutations), the
  transitions between isomorphism classes, and the terminal classes;
- for each class with two or more successor classes, whether each pair of
  successor classes has a common descendant class.

Standard library only. Run from the repository root:
    python3 -I scripts/python/causal_invariance_path5.py
Output: results/phase1_selfaudit/causal_invariance_path5.out
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from setreplace_order import matches  # noqa: E402

INIT = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]


def apply(state, m, next_id, next_vertex):
    """state: list of (edge id, (a, b)). m: positions for LHS edges 0..3."""
    x, y = state[m[0]][1]
    z = state[m[1]][1][1]
    w = state[m[2]][1][1]
    v = state[m[3]][1][1]
    u = next_vertex
    created = [(y, u), (u, v), (w, x), (x, u)]
    consumed = [state[p][0] for p in m]
    rest = [e for i, e in enumerate(state) if i not in m]
    new = [(next_id + k, e) for k, e in enumerate(created)]
    return rest + new, consumed, [i for i, _ in new], next_id + 4, next_vertex + 1


def canonical(edges):
    """Canonical form of a directed multigraph given as a list of (a, b)."""
    verts = sorted({a for e in edges for a in e})
    best = None
    for perm in itertools.permutations(range(len(verts))):
        rel = dict(zip(verts, perm))
        form = tuple(sorted((rel[a], rel[b]) for a, b in edges))
        if best is None or form < best:
            best = form
    return best


def histories(state, next_id, next_vertex, events):
    ms = matches(state)
    if not ms:
        yield events, state
        return
    for m in ms:
        s2, consumed, created, nid, nv = apply(state, m, next_id, next_vertex)
        yield from histories(s2, nid, nv, events + [(consumed, created)])


def causal_edges(events, initial_ids):
    creator = {i: None for i in initial_ids}
    out = []
    for j, (consumed, created) in enumerate(events, 1):
        for c in consumed:
            if creator.get(c) is not None:
                out.append((creator[c], j))
        for c in created:
            creator[c] = j
    return sorted(set(out))


def main():
    state0 = [(k + 1, e) for k, e in enumerate(INIT)]
    print("initial state:", INIT, flush=True)
    print("matches of the initial state (edge identities):",
          [[state0[p][0] for p in m] for m in matches(state0)], flush=True)

    terminal = {}
    for n, (events, final) in enumerate(histories(state0, 6, 7, []), 1):
        edges = [e for _, e in final]
        verts = sorted({a for e in edges for a in e})
        print(f"history {n}: {len(events)} events", flush=True)
        for j, (consumed, created) in enumerate(events, 1):
            print(f"  event {j}: consumes edges {consumed}, creates edges {created}", flush=True)
        print(f"  causal edges: {causal_edges(events, [i for i, _ in state0])}", flush=True)
        print(f"  terminal state: {sorted(edges)}, {len(verts)} vertices, {len(edges)} edges", flush=True)
        terminal.setdefault(canonical(edges), []).append(n)
    print(f"terminal isomorphism classes: {len(terminal)}; histories per class: {list(terminal.values())}", flush=True)

    # Isomorphism classes of all reachable states and the transitions between them.
    classes = {}
    succ = {}
    frontier = [(state0, 6, 7)]
    while frontier:
        state, nid, nv = frontier.pop()
        key = canonical([e for _, e in state])
        if key in classes:
            continue
        classes[key] = len(classes)
        succ[key] = set()
        for m in matches(state):
            s2, _, _, nid2, nv2 = apply(state, m, nid, nv)
            succ[key].add(canonical([e for _, e in s2]))
            frontier.append((s2, nid2, nv2))
    transitions = sum(len(s) for s in succ.values())
    print(f"state isomorphism classes: {len(classes)}, transitions between classes: {transitions}", flush=True)
    for key, idx in sorted(classes.items(), key=lambda kv: kv[1]):
        print(f"  class {idx}: {len(set(a for e in key for a in e))} vertices, successors "
              f"{sorted(classes[s] for s in succ[key])}", flush=True)

    def desc(key, seen=None):
        seen = set() if seen is None else seen
        if key in seen:
            return seen
        seen.add(key)
        for s in succ[key]:
            desc(s, seen)
        return seen

    pairs = resolved = 0
    for key in classes:
        for a, b in itertools.combinations(sorted(succ[key]), 2):
            pairs += 1
            ok = bool(desc(a) & desc(b))
            resolved += ok
            print(f"  branch pair from class {classes[key]}: classes {classes[a]} and {classes[b]}, "
                  f"common descendant: {ok}", flush=True)
    print(f"branch pairs: {pairs}, resolved: {resolved}", flush=True)


if __name__ == "__main__":
    main()
