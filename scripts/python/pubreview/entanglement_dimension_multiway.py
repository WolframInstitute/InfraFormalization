"""Number of matches per state for the two example rules of arXiv:2301.12455 Figures 6, 7 and
10-13 (papers/tex_2301_12455/EntanglementEntropy.tex lines 813, 821, 996, 1011), from three
initial conditions: {{0,0,0},{0,0,0}} (the analogue of the double self-loop used throughout G9),
{{0,0,0},{0,0,0},{0,0,0}} and {{0,1,1},{0,2,3},{2,1,1}}. HGEvolve multiway evolution without state
identification for 12 steps: states per step and the largest number of events applied to one
state. A state with one match at every step gives a causal graph that is a chain."""
import collections
import json

from hg_env import evolve

RULES = {
    "flat_rule": ([["x", "y", "y"], ["x", "z", "u"]], [["u", "v", "v"], ["v", "z", "y"], ["x", "y", "v"]]),
    "curved_rule": ([["x", "y", "x"], ["x", "z", "u"]], [["u", "v", "u"], ["v", "u", "z"], ["x", "y", "v"]]),
}
INITS = {
    "two_triple_self_loops": [[0, 0, 0], [0, 0, 0]],
    "three_triple_self_loops": [[0, 0, 0], [0, 0, 0], [0, 0, 0]],
    "mixed": [[0, 1, 1], [0, 2, 3], [2, 1, 1]],
}


def main():
    out = {}
    for rn, rule in RULES.items():
        for iname, init in INITS.items():
            r = evolve([rule], init, 12, canonicalize_states=None,
                       max_states_per_step=20000)
            per_step = collections.Counter(s["Step"] for s in r.states.records())
            fan = collections.Counter(e["InputState"] for e in r.events.records())
            key = f"{rn}/{iname}"
            out[key] = {"states_per_step": [per_step[k] for k in sorted(per_step)],
                        "max_events_from_one_state": max(fan.values()) if fan else 0,
                        "events": r.num_events}
            print(key, json.dumps(out[key]), flush=True)
    with open("../../../results/publication_review/entanglement_dimension_multiway.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
