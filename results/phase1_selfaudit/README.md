# Phase 1: comparison of the Python rewriter with SetReplace

The Python rewriter (`scripts/python/rewriter.py`) matches SetReplace on events fired, final state size and causal-graph vertex count for all 9 seeds, and on causal-graph edge count for 7 of 9. The two tools apply the rule in different update orders, so the causal graphs differ (section "Where they differ"). `scripts/python/run_all_seeds.py` (rerun 2026-10-23) reports the edge-count differences on the 3x3x3 and 5x5x5 grids and exits with status 0.

## What was audited

The measurements of the rule named in arXiv:2102.09363 line 6202,
$$
R: \;\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \;\longrightarrow\; \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\},
$$
was built on SetReplace runs. Phase 1A re-implements the rewriting semantics in Python from scratch (no SetReplace, no Wolfram Language at all) and checks the results agree.

See `scripts/python/rewriter.py` for the re-implementation; see `scripts/run_seeds_v3.wl` and `scripts/causal_dimension.wl` for the SetReplace runs being audited.

## Reproducing

```
cd scripts/python
python3 run_all_seeds.py
```

No dependencies outside the Python standard library.

## Results (2026-04-18 comparison)

| Seed | events fired | state size | \|V\| | \|E\| (py) | \|E\| (SR) | exponent (py) | exponent (SR) |
|---|---:|---:|---:|---:|---:|---:|---:|
| 4-cycle | 1 | 4 | 1 | — | — | — (too small) | — |
| 4-path  | 1 | 4 | 1 | — | — | — (too small) | — |
| 6-cycle | 500 | 6 | 500 | 1994 | 1994 | 0.995 | 0.995 |
| 8-cycle | 500 | 8 | 500 | 1992 | 1992 | 1.000 | 0.991 |
| 10-path | 500 | 10 | 500 | 1990 | 1990 | 0.995 | 1.014 |
| 20-cycle | 1000 | 20 | 1000 | 3980 | 3980 | 1.028 | 0.995 |
| grid3_3 | 300 | 54 | 300 | 1150 | 1146 | 1.081 | 1.098 |
| grid3_4 | 1000 | 144 | 1000 | 3856 | 3856 | 1.256 | 0.985 |
| grid3_5 | 2000 | 300 | 2000 | 7700 | 7703 | 1.055 | 1.014 |

The Python values were reproduced on 2026-10-23. The SetReplace exponents come from `notes/empirical_refutation.md` and `setreplace_reference.md`.

### What matches exactly
- **Events fired** across all 9 seeds. In particular, the 4-cycle and 4-path "die after 1 event" observation is confirmed.
- **Final state size** across all 9 seeds. Edge-conservation (`|LHS|=|RHS| ⇒ state size constant`) is a structural law independent of any scheduler.
- **Causal graph |V|** across all 9 seeds. (Once we align on the convention that SetReplace excludes the virtual-seed event, the two implementations produce equal event counts.)
- **Causal graph |E|** on 7 of 9 seeds exactly.
- **Cone exponent**: differs, because the update orders differ. Python gives 0.995 to 1.256 and SetReplace gives 0.985 to 1.098.

### Where they differ
Two dense 3D-grid seeds differ in |E| by ≤ 4 edges out of thousands:
- `grid3_3`: Python 1150 vs SetReplace 1146 (diff 4)
- `grid3_5`: Python 7700 vs SetReplace 7703 (diff 3)

Cause: the update orders differ. `rewriter.py` takes the first match in lexicographic order of the state positions of the matched edges (`find_match`). SetReplace runs `"PatternRules"` with its Wolfram Language implementation, which matches `Shortest` over the ordered state and chooses a match whose last edge is earliest (`Kernel/setSubstitutionSystem$wl.m`, `toNormalRules`). `scripts/python/setreplace_order.py` implements that order and reproduces the SetReplace cone counts and exponents on the 6-cycle, 8-cycle and 10-path; the exponents under four orders are tabulated in `notes/empirical_refutation.md`, section 4. Equal event and causal-edge counts do not imply equal causal graphs: on grid3_4 both counts agree and the exponents are 1.256 and 0.985.

## Conventions (for future readers)

- **Event indexing.** Our Python rewriter treats the initial state as having been produced by a virtual "event 0"; real rewriting events are 1, 2, …. SetReplace's `AllEventsCount` excludes the virtual event. The comparison table above uses SetReplace's convention for |V|.
- **Causal-edge multiplicity.** When an event $j$ consumes two expressions both produced by the same earlier event $i$, both contribute — so multiple causal edges $i \to j$ are counted with multiplicity. This matches SetReplace's `CausalGraph`.
- **Virtual-seed causal edges.** SetReplace's `CausalGraph` does **not** include causal edges whose creator is the virtual seed. Python matches this convention after the 2026-04-18 update. Without this exclusion, Python's |E| exceeds SetReplace's by exactly `seed_size − surviving_seed_edges`.
- **Cone-growth BFS.** For cone dimension, we start from the first real event (event 1) and do BFS on the causal DAG with virtual-seed edges *included*. Matching SetReplace's convention on this requires explicit use of `drop_virtual_seed=False` in `causal_edges`.

## Manual hand-traces (redundant check on the 4-cycle and 4-path dead ends)

### 4-cycle

Initial: `{{1,2},{2,3},{3,4},{4,1}}`.
The LHS pattern `{{x,y},{y,z},{z,w},{w,v}}` matches with $x=1,y=2,z=3,w=4,v=1$ (note $v=x$: pattern variables *can* repeat, and 1 → 2 → 3 → 4 → 1 is a valid length-4 directed chain of 4 distinct edges around the cycle). Fresh $u$; RHS = `{{2,u},{u,1},{4,1},{1,u}}`.

Can the rule fire again? Live edges: `2→u`, `u→1`, `4→1`, `1→u`. We need 4 *distinct* edges in a chain $x\!\to\!y\!\to\!z\!\to\!w\!\to\!v$. Enumerating:
- Starting at 2: `2→u→1→u` runs out of options after 3 edges (must re-use `u→1` or `1→u`).
- Starting at 4: `4→1→u→1` same issue.
No length-4 chain of distinct edges exists. The rule halts. This matches `events_fired = 1`.

### 4-path

Initial: `{{1,2},{2,3},{3,4},{4,5}}`.
Match $x=1,y=2,z=3,w=4,v=5$. Fresh $u$; RHS = `{{2,u},{u,5},{4,1},{1,u}}`. Live edges: `2→u`, `u→5`, `4→1`, `1→u`.

Chains of length 4: `4→1→u→5` is the longest directed chain and has only 3 edges. No length-4 chain exists. The rule halts.

## Status of the measured quantities

1. **Halting on the 4-cycle and 4-edge path.** Both tools fire one event. The hand traces above confirm it.
2. **Edge-count conservation.** PROVED in Lean (`Refutations.gorardNamedRule_applications_preserve_size`). Both tools report a constant state size.
3. **Cone exponent.** MEASURED between 0.77 and 1.26 on the seeds above across four update orders. PROVED: at most 5^t events within directed distance t, and antichains of at most N/4 events (`CausalHistory.lean`). Linear cone growth is OPEN (O1 in `STATUS_OF_GORARD_CLAIMS.md`).
