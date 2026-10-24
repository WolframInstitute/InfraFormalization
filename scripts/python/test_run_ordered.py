"""rewriter.run_ordered against SetReplace's WolframModel.

setreplace_order_cases.json, beside this file, holds SetReplace 0.3.196's single histories under
"EventOrderingFunction" for 119 cases (6 rule sets, 2 or 3 initial states, 7 orderings, up to
200 events), recorded by reference/verify_setreplace_order.wls of the HypergraphRewritingEngine
repository. For each case the events (rule, input edges, output edges, numbered from 1 in
creation order), the edges up to a renaming of the vertices the evolution creates, and the
causal pairs must equal SetReplace's.

Run: python3 -m pytest scripts/python/test_run_ordered.py, or python3 scripts/python/test_run_ordered.py.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rewriter import Rule, run_ordered  # noqa: E402

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "setreplace_order_cases.json")


def load_cases():
    with open(DATA) as f:
        return json.load(f)


def to_rule(lhs, rhs):
    var = lambda e: tuple(f"v{a}" for a in e)
    return Rule(lhs=[var(e) for e in lhs], rhs=[var(e) for e in rhs])


def same_up_to_relabel(a, b):
    if len(a) != len(b):
        return False
    fwd, back = {}, {}
    for x, y in zip(a, b):
        if len(x) != len(y):
            return False
        for u, v in zip(x, y):
            if fwd.setdefault(u, v) != v or back.setdefault(v, u) != u:
                return False
    return True


def check(case):
    rules = [to_rule(lhs, rhs) for lhs, rhs in case["rules"]]
    h, event_rules = run_ordered([tuple(e) for e in case["init"]], rules, case["max_events"],
                                 case["ordering"])
    events = [[r, [i + 1 for i in ev.input_edge_ids], [o + 1 for o in ev.output_edge_ids]]
              for r, ev in zip(event_rules, h.events[1:])]
    causal = sorted({(h.creator[e], h.consumer[e]) for e in range(len(h.all_edges))
                     if h.creator[e] > 0 and h.consumer[e] > 0})
    return (events == case["events"],
            same_up_to_relabel([list(e) for e in h.all_edges], case["expressions"]),
            [list(p) for p in causal] == case["causal"])


def test_run_ordered_matches_setreplace():
    cases = load_cases()
    assert len(cases) == 119
    failed = [c["name"] for c in cases if not all(check(c))]
    assert failed == []


if __name__ == "__main__":
    cases = load_cases()
    bad = 0
    for c in cases:
        ok = check(c)
        if not all(ok):
            bad += 1
            print("FAIL", c["name"], ok, flush=True)
    print(len(cases), "cases,", bad, "failures", flush=True)
    sys.exit(1 if bad else 0)
