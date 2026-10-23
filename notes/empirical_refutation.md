# Measurements of the causal graph of the rule named in arXiv:2102.09363

## The rule under test

arXiv:2102.09363 (line 6202) uses
$$
\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\}\;\to\;\{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}
$$
(where `u` is a fresh vertex) and describes it as "a hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit" (abstract, lines 50-52). The paper gives no proof for this rule.

The SetReplace runs below use `scripts/run_seeds_v3.wl`, `scripts/causal_dimension.wl` and `scripts/grid3d_test.wl` through `wolframscript` with SetReplace 0.3.196. The Python runs use `scripts/python/run_all_seeds.py`. Each run is single-way, in the update order of its tool.

## Findings

### (1) On the 4-cycle and the 4-edge path the rule fires once

| Seed | Seed size | Events fired | Termination |
|---|---:|---:|---|
| directed 4-cycle `{{1,2},{2,3},{3,4},{4,1}}` | 4 | **1** | no match remains |
| directed 4-path  `{{1,2},{2,3},{3,4},{4,5}}` | 4 | **1** | no match remains |

After one firing on the 4-cycle the state is `{{2,v12},{v12,1},{4,1},{1,v12}}`, which contains no chain of four distinct edges `x→y→z→w→v`. The hand traces are in `results/phase1_selfaudit/README.md`.

### (2) The edge count is constant

The rule has `|LHS| = |RHS| = 4`, so each firing removes 4 edges and adds 4. Edge-count conservation is PROVED in Lean (`Refutations.gorardNamedRule_applications_preserve_size`, `Refutations/F7NamedRuleStructure.lean:41`).

| Seed | Events fired | Final state size | Causal graph \|V\| | Causal graph \|E\| |
|---|---:|---:|---:|---:|
| 6-cycle | 500 | 6 | 500 | 1994 |
| 8-cycle | 500 | 8 | 500 | 1992 |
| 10-path | 500 | 10 | 500 | 1990 |
| 20-cycle | 1000 | 20 | 1000 | 3980 |
| figure-8 | 1000 | 14 | 1000 | 3986 |

### (3) Cone-growth exponent

C(r) is the number of events within directed graph distance r of the first event. The exponent is the slope of a least-squares fit of log C(r) against log r over r in [r_max/4, 3 r_max/4].

| Seed | Seed edges | Events | Max cone distance (SetReplace) | SetReplace exponent | Python exponent |
|---|---:|---:|---:|---:|---:|
| 6-cycle | 6 | 500 | 250 | 0.995 | 0.995 |
| 6-cycle | 6 | 2000 | 1000 | 0.999 | not run |
| 8-cycle | 8 | 500 | 249 | 0.991 | 1.000 |
| 10-path | 10 | 500 | 167 | 1.014 | 0.995 |
| 20-cycle | 20 | 1000 | 494 | 0.995 | 1.028 |
| 3x3x3 grid | 54 | 300 | 36 | 1.098 | 1.081 |
| 4x4x4 grid | 144 | 1000 | 52 | 0.985 | 1.256 |
| 5x5x5 grid | 300 | 2000 | 45 | 1.014 | 1.055 |

The Python column was rerun on 2026-10-23. The SetReplace column is the recorded output in `results/phase1_selfaudit/setreplace_reference.md` and was not rerun. Section 4 gives the cause of the differences.

Cone counts recorded by SetReplace:

- 6-cycle: C(r) = 3, 5, 7, 9, 11, 13, ...
- 8-cycle: C(r) = 3, 6, 8, 10, 12, 14, ...
- 10-path: C(r) = 2, 4, 6, 9, 12, 15, 18, ...
- 4x4x4 grid: C(r) = 4, 11, 21, 33, 45, 55, 65, 74, 83, 92, 101, 110, 119, 128, 137, ...

Cone counts recorded by the Python rewriter for the 4x4x4 grid: C(r) = 1, 3, 7, 15, 26, 43, 61, 82, 99, 118, 138, 158, 178, 198, 218, 238.

### (4) Cause of the disagreement between the two tools

The two tools apply the rule in different update orders.

- `scripts/python/rewriter.py` (`find_match`, lines 140-178) takes the first match in lexicographic order of the state positions of the edges bound to the four left-hand-side edges, in left-hand-side order.
- SetReplace 0.3.196 runs a rule given as `"PatternRules"` with its Wolfram Language implementation (`Kernel/setSubstitutionSystem$wl.m`, function `toNormalRules`). The implementation matches `Shortest` over the ordered state with all 24 orderings of the left-hand side, so it chooses a match whose last edge in the state list is earliest.

Both tools append the created edges at the end of the state. Each event consumes 4 edges and creates 4, so the event counts agree on every seed, and the causal edge counts agree on 7 of 9 seeds although the evolutions differ.

`scripts/python/setreplace_order.py` reimplements the SetReplace order with two rules for ties between matches that share their last edge: by left-hand-side ordering (`--tie perm`) and by state positions (`--tie pos`). With `--tie pos` it reproduces the SetReplace cone counts and exponents on the 6-cycle, 8-cycle and 10-path. It does not reproduce the 20-cycle and grid runs, so `Shortest` over `Alternatives` breaks ties by a rule that differs from both.

Exponents under four update orders (MEASURED; Python columns rerun on 2026-10-23):

| Seed | SetReplace | rewriter.py | last edge earliest, `--tie perm` | last edge earliest, `--tie pos` |
|---|---:|---:|---:|---:|
| 6-cycle | 0.995 | 0.995 | 0.995 | 0.995 |
| 8-cycle | 0.991 | 1.000 | 1.000 | 0.991 |
| 10-path | 1.014 | 0.995 | 1.014 | 1.014 |
| 20-cycle | 0.995 | 1.028 | 0.991 | 0.998 |
| 3x3x3 grid | 1.098 | 1.081 | 0.963 | 0.767 |
| 4x4x4 grid | 0.985 | 1.256 | 1.080 | 1.140 |
| 5x5x5 grid | 1.014 | 1.055 | 1.011 | 0.988 |

Causal edge counts on the 3x3x3, 4x4x4 and 5x5x5 grids: SetReplace 1146, 3856, 7703; `rewriter.py` 1150, 3856, 7700; `setreplace_order.py` 1148, 3856, 7700 with either tie rule.

On the 3x3x3 grid the exponent ranges from 0.77 to 1.10 across the four orders, and on the 4x4x4 grid from 0.99 to 1.26. At 300 to 2000 events the fit depends on the update order and does not determine an exponent of the rule.

## Status

- PROVED: the rule conserves edge count. In every evolution from N hyperedges, with any update order, every antichain of the causal graph has at most N/4 events and at most 5^t events lie within directed distance t of an event (`CausalHistory.gorardNamedRule_antichain_card_le`, `CausalHistory.gorardNamedRule_ball_card_le`).
- MEASURED: on the seeds above the cone-growth exponent lies between 0.77 and 1.26 and depends on the update order (section 4).
- OPEN: linear cone growth, stated in Lean as `CausalHistory.GorardNamedRuleConeGrowthLinear` (O1 in `STATUS_OF_GORARD_CLAIMS.md`).
- Not run: the rule on a Poisson sprinkling of Brill-Lindquist initial data, which is the initial data arXiv:2102.09363 uses (lines 6148-6152, 6179).

A bounded spatial ball count holds on every finite hypergraph, so the constant edge count does not give the rule a spatial dimension that differs from any other rule run on a finite state. arXiv:2102.09363 compares runs at 200, 400, 800 and 1600 vertices, and edge-count conservation within a run does not constrain a sequence of initial states of growing size.

The largest run has 2000 events. The measurements do not determine the exponent at larger event counts.

## Relation to arXiv:2004.14810 §3.3

The §3.3 argument of arXiv:2004.14810 uses a causal-graph cone count of the form $C(t) = a\,t^n(1 - \ldots)$ with $n = 4$ for 3+1 dimensions. On the seeds above the measured exponent is between 0.77 and 1.26. Whether the cone growth of this rule is linear on all initial data is OPEN.
