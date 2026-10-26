"""Checks of the Complex Systems 29(2) 537-598 statements on confluence and causal invariance.

Statements checked (line numbers of papers/gorard_complexsystems_29_2.txt):
  lines 500-503: for a multiway system in which every branch terminates, convergence of all
    branch pairs is necessary and sufficient for causal invariance.
  lines 1333-1336: multiway invariance implies causal invariance for a non-infinite evolution,
    by Newman's lemma.
  lines 1815-1818: modularity of the multiway lattice is a sufficient condition for causal
    invariance.
Causal invariance is Def 12 (lines 324-326): the causal graphs of all evolution histories are
isomorphic. For terminating systems the complete histories are the maximal paths.

Each system is run with HGEvolve twice: without state canonicalisation (the multiway tree, whose
root-to-leaf paths are the complete histories with consistent edge ids), and with
"CanonicalizeStates" -> "Full" (the multiway graph of isomorphism classes of states). The causal
graph of a history has an edge i -> j when event j consumes an edge produced by event i.
"""
import itertools
import json

from hg_env import evolve

SYSTEMS = {
    # A -> B, A -> C as hypergraphs: {a} -> {a,a} and {a} -> {a,a,a}.
    "E1_two_normal_forms": {
        "rules": [([["a"]], [["a", "a"]]), ([["a"]], [["a", "a", "a"]])],
        "initial": [[1]],
    },
    # A -> B, A -> D, B -> D: terminating, one normal form.
    "E2_confluent_terminating": {
        "rules": [([["a"]], [["a", "a"]]), ([["a"]], [["a", "a", "a"]]),
                  ([["a", "a"]], [["a", "a", "a"]])],
        "initial": [[1]],
    },
    # A -> X, B -> Y, XB -> XY from AB, with A = {a}, X = {a,a}, B = {b,b,b}, Y = {b,b,b,b}.
    "E3_boolean_lattice": {
        "rules": [([["a"]], [["a", "a"]]), ([["b", "b", "b"]], [["b", "b", "b", "b"]]),
                  ([["a", "a"], ["b", "b", "b"]], [["a", "a"], ["b", "b", "b", "b"]])],
        "initial": [[1], [2, 2, 2]],
    },
}
STEPS = 6


def histories(r):
    ev = list(r.events.records())
    out_of = {}
    for e in ev:
        out_of.setdefault(e["InputState"], []).append(e)
    paths = []

    def walk(state, path):
        if state not in out_of:
            paths.append(path)
            return
        for e in out_of[state]:
            walk(e["OutputState"], path + [e])

    walk(0, [])
    return paths


def causal_graph(path):
    producer = {}
    edges = set()
    for j, e in enumerate(path):
        for c in e["ConsumedEdges"]:
            if c in producer:
                edges.add((producer[c], j))
        for p in e["ProducedEdges"]:
            producer[p] = j
    return len(path), sorted(edges)


def isomorphic(g1, g2):
    n1, e1 = g1
    n2, e2 = g2
    if n1 != n2 or len(e1) != len(e2):
        return False
    s2 = set(e2)
    for perm in itertools.permutations(range(n1)):
        if all((perm[a], perm[b]) in s2 for a, b in e1):
            return True
    return False


def lattice_report(rf):
    states = sorted({s["CanonicalId"] for s in rf.states.records()})
    succ = {s: set() for s in states}
    for e in rf.events.records():
        succ[e["CanonicalInputState"]].add(e["CanonicalOutputState"])
    reach = {}
    for s in states:
        seen, stack = {s}, [s]
        while stack:
            for t in succ[stack.pop()]:
                if t not in seen:
                    seen.add(t)
                    stack.append(t)
        reach[s] = seen
    leq = lambda a, b: b in reach[a]  # a <= b when b is reachable from a

    def join(a, b):
        ub = [c for c in states if leq(a, c) and leq(b, c)]
        least = [c for c in ub if all(leq(c, d) for d in ub)]
        return least[0] if len(least) == 1 else None

    def meet(a, b):
        lb = [c for c in states if leq(c, a) and leq(c, b)]
        great = [c for c in lb if all(leq(d, c) for d in lb)]
        return great[0] if len(great) == 1 else None

    is_lattice = all(join(a, b) is not None and meet(a, b) is not None
                     for a in states for b in states)
    modular = None
    if is_lattice:
        modular = all(join(a, meet(x, b)) == meet(join(a, x), b)
                      for a in states for b in states for x in states if leq(a, b))
    hasse_edges = {(a, b) for a in states for b in succ[a]}
    transitive = [(a, b) for a, b in hasse_edges
                  if any(c not in (a, b) and leq(a, c) and leq(c, b) for c in states)]
    return {"states": len(states), "is_lattice": is_lattice, "modular": modular,
            "transitive_edges": len(transitive)}


def main():
    report = {}
    for name, sysd in SYSTEMS.items():
        tree = evolve(sysd["rules"], sysd["initial"], STEPS, canonicalize_states=None)
        full = evolve(sysd["rules"], sysd["initial"], STEPS, canonicalize_states="Full")
        paths = histories(tree)
        graphs = [causal_graph(p) for p in paths]
        classes = []
        for g in graphs:
            if not any(isomorphic(g, c) for c in classes):
                classes.append(g)
        ev_full = list(full.events.records())
        has_out = {e["CanonicalInputState"] for e in ev_full}
        terminal = sorted({s["CanonicalId"] for s in full.states.records()
                           if s["CanonicalId"] not in has_out})
        terminates = max(len(p) for p in paths) < STEPS
        entry = {
            "histories": len(paths),
            "terminates_within_steps": terminates,
            "terminal_state_classes": len(terminal),
            "confluent": len(terminal) == 1 and terminates,
            "causal_graph_classes": [{"events": n, "causal_edges": e} for n, e in classes],
            "causal_invariant": len(classes) == 1,
            "multiway_graph": lattice_report(full),
        }
        report[name] = entry
        print(name, json.dumps(entry), flush=True)
    with open("../../../results/publication_review/qm_confluence_causal_invariance.json", "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
