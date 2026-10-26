"""Checks of the "Wolfram model rules" of arXiv:2111.03460 that are stated to turn a graph into a
small category and a groupoid (papers/tex_2111/homotopy1.tex lines 564-595).

Lines 573-578: {{a,b},{b,c}} -> {{a,b},{b,c},{a,c}} (transitivity) and {{a}} -> {{a,a}}
(reflexivity), "applied to any initial graph G", give its transitive closure with a self-loop at
every node. Line 592: {{a,b}} -> {{b,a}} adds the inverse edges of a groupoid.

Initial graph: the directed path {{1,2},{2,3},{3,4}}, whose transitive closure has 6 edges.
Each rule is run with HGEvolve, one evolution per rule set, with "Generational" -> True (every
non-overlapping match applied at each step) and also as a full multiway system where finite."""
import collections
import json

from hg_env import evolve

G = [[1, 2], [2, 3], [3, 4]]
TRANS = ([["a", "b"], ["b", "c"]], [["a", "b"], ["b", "c"], ["a", "c"]])
REFL = ([["a"]], [["a", "a"]])
INV = ([["a", "b"]], [["b", "a"]])


def last_state_edges(r):
    recs = list(r.states.records())
    last = max(recs, key=lambda s: (s["Step"], s["Id"]))
    return [tuple(e[1:]) for e in last["Edges"]], last["Step"]


def main():
    out = {}
    r = evolve([REFL], G, 5, canonicalize_states="Full")
    out["reflexivity_alone_events"] = r.num_events
    for k in range(1, 7):
        r = evolve([TRANS, REFL], G, k, generational=True, canonicalize_states=None)
        edges, step = last_state_edges(r)
        mult = collections.Counter(edges)
        out.setdefault("transitivity_generational", []).append({
            "steps": k, "reached_step": step, "edges": len(edges), "distinct_edges": len(mult),
            "self_loops": sum(1 for a, b in mult if a == b),
            "max_multiplicity": max(mult.values())})
    r = evolve([INV], G, 4, canonicalize_states="Full")
    states = list(r.states.records())
    two_way = 0
    for s in states:
        es = {tuple(e[1:]) for e in s["Edges"]}
        two_way = max(two_way, sum(1 for a, b in es if (b, a) in es and a != b))
    out["inverse_rule"] = {"states": len(states), "edges_per_state": sorted(
        {len(s["Edges"]) for s in states}), "max_two_way_pairs_in_a_state": two_way}
    print(json.dumps(out, indent=1))
    with open("../../../results/publication_review/homotopy_category_rules.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
