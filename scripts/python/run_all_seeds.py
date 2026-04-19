"""Run the independent Python rewriter on all seeds used in the SetReplace
refutation, print a comparison table, and emit a machine-readable JSON log.

Usage:
    python run_all_seeds.py [--json-out <path>]

The expected SetReplace values (reproduced from the earlier wolframscript
runs in `results/phase1_selfaudit/setreplace_reference.md`) are baked in
for at-a-glance comparison. Any disagreement in `events_fired`,
`final_state_size`, `|V|` or `|E|` flags a bug.
"""

from __future__ import annotations

import argparse
import json
from typing import Dict, Any

from rewriter import seed, gorard_rule, run, causal_edges, cone_growth, _loglog_dim_fit


# Expected values from the SetReplace runs on 2026-04-18 (see
# `results/phase1_selfaudit/setreplace_reference.md` for the log).
# SetReplace's reported |V| counts events *without* a virtual seed event,
# so our Python |V|, which includes event 0 (virtual seed), is off by +1.
# We subtract 1 in the comparison. SetReplace's |E| counts causal edges
# with multiplicity (one per mediating expression) which is our default
# `multi=True` convention.
SETREPLACE_EXPECTED: Dict[str, Dict[str, Any]] = {
    "4cycle":   {"max_events": 200,  "events_fired": 1,    "final_state_size": 4},
    "5path":    {"max_events": 200,  "events_fired": 1,    "final_state_size": 4},
    "6cycle":   {"max_events": 500,  "events_fired": 500,  "final_state_size": 6,  "cg_V": 500, "cg_E": 1994},
    "8cycle":   {"max_events": 500,  "events_fired": 500,  "final_state_size": 8,  "cg_V": 500, "cg_E": 1992},
    "10path":   {"max_events": 500,  "events_fired": 500,  "final_state_size": 10, "cg_V": 500, "cg_E": 1990},
    "20cycle":  {"max_events": 1000, "events_fired": 1000, "final_state_size": 20, "cg_V": 1000,"cg_E": 3980},
    "grid3_3":  {"max_events": 300,  "events_fired": 300,  "final_state_size": 54, "cg_V": 300, "cg_E": 1146},
    "grid3_4":  {"max_events": 1000, "events_fired": 1000, "final_state_size": 144,"cg_V": 1000,"cg_E": 3856},
    "grid3_5":  {"max_events": 2000, "events_fired": 2000, "final_state_size": 300,"cg_V": 2000,"cg_E": 7703},
}


def run_one(name: str) -> Dict[str, Any]:
    ref = SETREPLACE_EXPECTED[name]
    max_events = ref["max_events"]
    s = seed(name)
    h = run(s, gorard_rule(), max_events)
    ce = causal_edges(h)
    cg = cone_growth(h)
    dim = _loglog_dim_fit(cg)
    return {
        "seed": name,
        "seed_size": len(s),
        "max_events": max_events,
        "events_fired": len(h.events) - 1,
        "final_state_size": h.state_size(),
        "cg_V": len(h.events) - 1,   # exclude virtual seed to match SetReplace convention
        "cg_E": len(ce),
        "cone_log_log_dim_fit": dim,
        "cone_head": cg[:16],
    }


def check(py: Dict[str, Any], ref: Dict[str, Any]) -> Dict[str, str]:
    flags: Dict[str, str] = {}
    for k in ("events_fired", "final_state_size", "cg_V", "cg_E"):
        if k in ref and k in py and py[k] != ref[k]:
            flags[k] = f"{py[k]} != {ref[k]} (SetReplace)"
    return flags


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--json-out")
    args = p.parse_args(argv)

    rows = []
    any_fail = False
    print(f"{'seed':<10} {'events':>8} {'state':>6} {'|V|':>6} {'|E|':>6}  {'dim':>6}  {'vs SetReplace'}")
    print("-" * 80)
    for name in SETREPLACE_EXPECTED:
        r = run_one(name)
        flags = check(r, SETREPLACE_EXPECTED[name])
        if flags:
            any_fail = True
            note = "; ".join(f"{k}: {v}" for k, v in flags.items())
        else:
            note = "OK"
        dim = r["cone_log_log_dim_fit"]
        dim_s = f"{dim:.3f}" if dim is not None else "  -  "
        print(f"{name:<10} {r['events_fired']:>8} {r['final_state_size']:>6} "
              f"{r['cg_V']:>6} {r['cg_E']:>6}  {dim_s:>6}  {note}")
        rows.append({"py": r, "setreplace": SETREPLACE_EXPECTED[name], "flags": flags})

    print()
    if any_fail:
        print("** MISMATCHES DETECTED — bug-audit required **")
    else:
        print("All SetReplace-comparable quantities match. Self-audit PASSED.")

    if args.json_out:
        with open(args.json_out, "w") as f:
            json.dump(rows, f, indent=2)
        print(f"\nJSON log -> {args.json_out}")
    return 1 if any_fail else 0


if __name__ == "__main__":
    raise SystemExit(main())
