# SetReplace reference run log (2026-04-18)

The output of SetReplace 0.3.196 on the 9 seeds used for the measurements of the rule of arXiv:2102.09363 line 6202 (`notes/empirical_refutation.md`). SetReplace runs this rule with its Wolfram Language implementation, which chooses a match whose last edge in the state list is earliest. The "cone dimension" lines are the log-log slope of the cone count C(r); section 4 of `notes/empirical_refutation.md` gives the slopes under three other update orders.

## Commands

```
# Main per-seed table:
wolframscript -file scripts/run_seeds_v3.wl

# Cone-dimension fit:
wolframscript -file scripts/causal_dimension.wl

# 3D grid variants:
wolframscript -file scripts/grid3d_test.wl
```

## Rule

```
<|"PatternRules" -> {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}}
                     :> Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}]|>
```

## SetReplace output (verbatim, abridged)

```
=== 4-cycle seed (|init|=4, MaxEvents=200) ===
  Events fired: 1
  Final state size: 4
  Final state: {{2, v12}, {v12, 1}, {4, 1}, {1, v12}}

=== 5-path seed (|init|=4, MaxEvents=200) ===
  Events fired: 1
  Final state size: 4
  Final state: {{2, v14}, {v14, 5}, {4, 1}, {1, v14}}

=== 6-cycle seed (|init|=6, MaxEvents=500) ===
  Events fired: 500
  Final state size: 6
  Causal graph: vertices=500, edges=1994

=== 8-cycle seed (|init|=8, MaxEvents=500) ===
  Events fired: 500
  Final state size: 8
  Causal graph: vertices=500, edges=1992

=== 10-path seed (|init|=10, MaxEvents=500) ===
  Events fired: 500
  Final state size: 10
  Causal graph: vertices=500, edges=1990

=== 20-cycle seed (|init|=20, MaxEvents=1000) ===
  Events fired: 1000
  Final state size: 20
  Causal graph: vertices=1000, edges=3980

=== 3x3x3 grid, 300 events ===
  seed |E| = 54
  events fired: 300
  final state |E|: 54
  cg |V| = 300  |E| = 1146
  fit: log C(r) ~ 1.71 + 1.098 log r  =>  cone dimension ≈ 1.098

=== 4x4x4 grid, 1000 events ===
  seed |E| = 144
  events fired: 1000
  final state |E|: 144
  cg |V| = 1000  |E| = 3856
  fit: log C(r) ~ 2.25 + 0.985 log r  =>  cone dimension ≈ 0.985

=== 5x5x5 grid, 2000 events ===
  seed |E| = 300
  events fired: 2000
  final state |E|: 300
  cg |V| = 2000  |E| = 7703
  fit: log C(r) ~ 2.13 + 1.014 log r  =>  cone dimension ≈ 1.014
```

The numbers quoted in `scripts/python/run_all_seeds.py`
(`SETREPLACE_EXPECTED` dictionary) are drawn from this log.
