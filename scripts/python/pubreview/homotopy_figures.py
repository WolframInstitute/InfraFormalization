"""Checks of arXiv:2105.10822 (papers/tex_2105/act21.tex) and arXiv:2111.03460
(papers/tex_2111/homotopy1.tex) on their multiway examples.

1. Figure 1 of 2105.10822 (act21.tex line 108): the multiway graph of
   {{x,y},{y,z}} -> {{w,y},{y,z},{z,w},{x,w}} from {{0,0},{0,0}} for 3 steps. HGEvolve with
   "CanonicalizeStates" -> "Full"; states per step and edges between distinct state classes.
   The figure (ACTHomotopy1.png) shows 1, 1, 3 and 18 states and 20 edges into step 3.
2. The string rule A -> AB from AA (act21.tex lines 181-203): the number of paths from AA to
   ABBBABBB, and the edges that the five homotopy rules of lines 200-203 and their inverses add
   when they are appended to the rule set as string rewriting rules (line 198), against the five
   pairs that join the two highlighted paths of Figure 5.
3. The map p -> {(alpha, q) : p ->alpha q} (act21.tex line 112), called a bijective function
   from A to P(Lambda x A), sends every normal form to the empty set. The normal forms of
   AB -> A, BA -> B from ABA are computed by qm_string_figures.py.
"""
import collections
import json

from hg_env import evolve


def string_successors(s, rules):
    out = []
    for k, (lhs, rhs) in enumerate(rules):
        i = s.find(lhs)
        while i != -1:
            out.append((k, i, s[:i] + rhs + s[i + len(lhs):]))
            i = s.find(lhs, i + 1)
    return out


def fig1():
    rule = ([["x", "y"], ["y", "z"]], [["w", "y"], ["y", "z"], ["z", "w"], ["x", "w"]])
    r = evolve([rule], [[0, 0], [0, 0]], 3, canonicalize_states="Full")
    step = {}
    for s in r.states.records():
        step[s["CanonicalId"]] = min(step.get(s["CanonicalId"], 99), s["Step"])
    per_step = collections.Counter(step.values())
    pairs = {(e["CanonicalInputState"], e["CanonicalOutputState"]) for e in r.events.records()}
    into = collections.Counter(step[b] for a, b in pairs)
    events_into = collections.Counter(step[e["CanonicalOutputState"]] for e in r.events.records())
    return {"states_per_step": [per_step[k] for k in range(4)],
            "distinct_state_pairs_into_step": [into[k] for k in range(1, 4)],
            "events_into_step": [events_into[k] for k in range(1, 4)]}


def string_part():
    base = [("A", "AB")]
    hom = [("AAB", "ABA"), ("AABB", "ABBA"), ("AABBB", "ABBBA"), ("ABABBB", "ABBBAB"),
           ("ABBABBB", "ABBBABB")]
    inv = [(b, a) for a, b in hom]
    # Paths AA -> ABBBABBB under A -> AB: states A B^i A B^j.
    count = collections.Counter({"AA": 1})
    frontier = {"AA"}
    for _ in range(6):
        nxt = collections.Counter()
        for s in frontier:
            for _, _, t in string_successors(s, base):
                nxt[t] += count[s]
        count.update(nxt)
        frontier = set(nxt)
    paths = count["ABBBABBB"]
    # Multiway graph of the extended system on the states reachable from AA with at most 6 Bs.
    rules = base + hom + inv
    seen, stack = {"AA"}, ["AA"]
    edges = set()
    while stack:
        s = stack.pop()
        for k, i, t in string_successors(s, rules):
            if t.count("B") > 6:
                continue
            edges.add((s, t, k))
            if t not in seen:
                seen.add(t)
                stack.append(t)
    figure_pairs = set(hom) | set(inv)
    horizontal = sorted({(s, t) for s, t, k in edges if k >= 1})
    extra = [p for p in horizontal if p not in figure_pairs]
    new_states = sorted(s for s in seen
                        if not (s.startswith("A") and s.count("A") == 2
                                and "A" in s[1:] and set(s) <= {"A", "B"}
                                and s[1:].index("A") >= 0 and s == "A" + "B" * (s[1:].index("A"))
                                + "A" + "B" * (len(s) - 2 - s[1:].index("A"))))
    return {"paths_AA_to_ABBBABBB": paths,
            "states_with_at_most_6_B": len(seen),
            "states_not_of_form_AB^iAB^j": new_states,
            "homotopy_rule_edges": len(horizontal),
            "figure5_pairs": len(figure_pairs),
            "homotopy_rule_edges_not_in_figure5": len(extra),
            "examples_not_in_figure5": extra[:8]}


def main():
    out = {"fig1": fig1(), "string": string_part()}
    print(json.dumps(out, indent=1))
    with open("../../../results/publication_review/homotopy_figures.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
