"""Which rule produced the causal graph figure shared by G2, G3, G4 and G9.

The figure file is byte-identical in G2 (CausalSet6.png, caption at CausalSetPaper.tex line 107),
G3 (NumericalRelativity138.png), G4 (GravitationalCollapse169.png) and G9
(EntanglementEntropy39.png, caption at EntanglementEntropy.tex line 1767) (figure_reuse.py).
G2, G3 and G4 caption it with {{x,y},{x,z}} -> {{x,y},{x,w},{y,w},{z,w}}; G9 with
{{x,y},{y,z}} -> {{x,y},{x,w},{y,w},{z,w}}. The figure shows 6 events in 3 generations
(1, 2, 3) and 10 causal edges counted with multiplicity (4, 4 and 2 from the three generations).
This script runs both rules from {{0,0},{0,0}} for 3 steps with "Generational" -> True and counts
events per generation and causal edges with multiplicity (one per hyperedge produced by one event
and consumed by another)."""
import collections
import json

from hg_env import evolve

RULES = {
    "G2_G3_G4_caption": ([["x", "y"], ["x", "z"]], [["x", "y"], ["x", "w"], ["y", "w"], ["z", "w"]]),
    "G9_caption": ([["x", "y"], ["y", "z"]], [["x", "y"], ["x", "w"], ["y", "w"], ["z", "w"]]),
}


def main():
    out = {}
    for name, rule in RULES.items():
        r = evolve([rule], [[0, 0], [0, 0]], 3, generational=True, canonicalize_states=None)
        events = list(r.events.records())
        producer = {}
        for e in events:
            for p in e["ProducedEdges"]:
                producer[p] = e["Id"]
        per_gen = collections.Counter(e["OutputState"] for e in events)
        mult = 0
        out_by_gen = collections.Counter()
        for e in events:
            for c in e["ConsumedEdges"]:
                if c in producer:
                    mult += 1
                    src = next(x for x in events if x["Id"] == producer[c])
                    out_by_gen[src["OutputState"]] += 1
        out[name] = {"events_per_generation": [per_gen[k] for k in sorted(per_gen)],
                     "causal_edges_with_multiplicity": mult,
                     "causal_edges_from_generation": [out_by_gen[k] for k in sorted(per_gen)]}
        print(name, json.dumps(out[name]), flush=True)
    with open("../../../results/publication_review/shared_causal_figure.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
