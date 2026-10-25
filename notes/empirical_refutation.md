# Measurements of the causal graph of the rule named in arXiv:2102.09363

## The rule under test

arXiv:2102.09363 (line 6202) uses
$$
\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\}\;\to\;\{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}
$$
(where `u` is a fresh vertex) and describes it as "a hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit" (abstract, lines 49-53). The paper gives no proof for this rule.

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

C(r) is the number of events within directed graph distance r of the first event. The exponent is the slope of a least-squares fit of log C(r) against log r. The Python column fits r from r_lo = max(2, ⌊r_max/4⌋) to max(r_lo + 3, ⌊3 r_max/4⌋) (`scripts/python/rewriter.py` lines 514-515). The SetReplace column fits r_max/4 ≤ r ≤ 3 r_max/4 (`scripts/causal_dimension.wl` line 29), and ⌊r_max/4⌋ ≤ r ≤ ⌊3 r_max/4⌋ on the grids (`scripts/grid3d_test.wl` line 40). With the window r_max/4 ≤ r ≤ 3 r_max/4, the Python exponents of the 3x3x3 and 4x4x4 grids are 1.077 and 1.238 in place of 1.081 and 1.256.

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

### (5) The rule is not causal invariant and not confluent

arXiv:2102.09363 restricts itself to confluent systems ("for the purposes of this article we shall consider only Wolfram model system that are (globally) confluent", lines 5011-5015), calls confluence "generally necessary (though not sufficient)" for causal invariance (lines 5036-5038), and puts gauge choices in bijection with evaluation orders through causal invariance (lines 5062-5066). arXiv:2303.07282 uses causal invariance as a hypothesis for the rule (lines 4693-4699, 4733-4735).

Counterexample on the directed path of five edges `{{1,2},{2,3},{3,4},{4,5},{5,6}}` (MEASURED, `scripts/python/causal_invariance_path5.py`, output `results/phase1_selfaudit/causal_invariance_path5.out`, run on 2026-10-24). The script enumerates every complete history with hyperedge identities.

- The initial state has two matches, on edges 1-4 and on edges 2-5. They share three edges.
- History 1 applies the first match (event 1 consumes edges 1, 2, 3, 4 and creates 6, 7, 8, 9). Event 1 creates a new match, and event 2 consumes edges 8, 9, 7 and 5. The history ends with 2 events, three causal edges from event 1 to event 2 (one related pair, through edges 7, 8 and 9), and a terminal state of 7 vertices and 5 edges.
- History 2 applies the second match (event 1 consumes edges 2, 3, 4, 5). No match remains. The history ends with 1 event, no causal edge, and a terminal state of 6 vertices and 5 edges.
- The two terminal states are not isomorphic, and the two complete causal graphs have 2 and 1 events.
- Up to isomorphism the multiway system has 4 state classes and 3 transitions. The initial class has two successor classes with no common descendant, so its one branch pair is not resolved.

The rule is therefore not confluent, and its complete causal graphs depend on the update order. The same counts (4 state classes, 3 events, 1 unresolved branch pair) were obtained with the HGEvolve engine (HypergraphRewritingEngine) with "CanonicalizeStates" -> Full.

Branch-pair resolution on other small initial states (MEASURED with HGEvolve, states identified up to isomorphism; a pair of successor classes of a class at depth at most D − 2 is resolved when the two have a common descendant class within depth D):

| Initial state | D | Resolved branch pairs |
|---|---:|---:|
| path of 5 edges | 7 | 0 of 1 |
| path of 6 edges | 7 | 1 of 6 |
| 5-cycle | 7 | 1 of 9 |
| 6-cycle | 7 | 11 of 26 |
| two 4-cycles sharing a vertex | 6 | 3429 of 5445 |
| four self-loops on one vertex | 7 | 0 of 1 |

Single histories of one Brill-Lindquist point cloud (MEASURED with HGEvolve; 3D periodic box [−10, 10]³, masses 0.5 at separation 1, link cut-off 1.25·(8000/n)^(1/3), cloud seed 1, one uniformly random match per step, "RandomSeed" 1 to 5): at n = 200 points (600 events) and n = 400 points (1000 events) the five causal graphs of equal length are pairwise non-isomorphic, with 1170 to 1190 and 1771 to 1828 causal pairs.

### (6) Calibration of the dimension and curvature measures

The measures below were applied to the rule's causal graphs and to Brill-Lindquist point clouds in the reproduction runs. Their calibration determines which readings describe the rule and which describe the instrument. A reading is UNCALIBRATED when the calibration does not validate the instrument at the sizes used. An UNCALIBRATED entry describes the instrument, and is not a finding about the papers.

Cone measure of a causal graph (the slope of log C(r) over r from R/4 to 3R/4, 40 sources from the first half of the events), MEASURED:

- Lattices: a chain of 300 events gives 0.99. The 1+1 lattice gives 1.89 at radius 60 and 1.97 at radius 200, the 2+1 lattice 2.45 at radius 15 and 2.76 at radius 40, and the 3+1 lattice 3.08 at radius 12. The measure reproduces lattice dimensions with a downward bias at finite radius.
- Sprinkled causal sets (uniform points in a causal diamond of 1+1, 2+1 and 3+1 Minkowski space, 500 to 5000 points, link graph): the cone measure gives 3.00, 3.28, 3.61 and 4.21 in 1+1 dimensions (1 to 14 sources with four radii in range, mean radius 7), and has no value in 2+1 and 3+1, where no source has four radii in the middle half of its cone. The Myrheim-Meyer value of the whole set gives 1.94 to 2.01 (1+1), 2.94 to 2.97 (2+1) and 3.96 to 4.09 (3+1). The median over sampled intervals gives 1.93 to 1.99, 2.81 to 2.89 and 3.31 to 3.60.

The cone measure does not reproduce the dimension of a sprinkled causal set. The cone exponents of findings (3) and (4) (0.77 to 1.26 on cycles, paths and grids) and the cone dimensions of the rule on Brill-Lindquist clouds (1.13 to 1.54 at 200 and 400 points) are therefore UNCALIBRATED. The statement that the exponent depends on the update order stands as a MEASURED property of the instrument's readings. On the 721 events before the first repeated state of the 200-point history, 7.6% of event pairs are related and no interval has 40 or more events, so the Myrheim-Meyer measure has no value there.

Ball measures of a spatial hypergraph (HGEvolve "VolumeGrowth": ball dimension and ball scalar curvature, means over all vertices), calibrated on random geometric graphs of known dimension and curvature (uniform points on tori, spheres and hyperbolic balls, links below a geodesic distance set by the mean degree):

- On uniform periodic 3D boxes the ball dimension reads 1.64 to 2.57 at 200 points and 2.05 to 2.38 at 1000 points (mean degree 6 to 24), and reads 3 within 0.1 only at 10,000 points with mean degree 6.
- Converted to length⁻² with the measured hop length, the ball scalar curvature reads −0.72 to −0.95 on uniform periodic 3D boxes at 200 points, −0.16 to −0.46 at 1000 points, and −0.04 to −0.11 at 5000 and 10,000 points, where the scalar curvature is 0. It reads the known curvature within 25% only at 10,000 points (2D sphere, 2D torus and 3D sphere at mean degree 12 and 24).

On the Brill-Lindquist clouds (c = 1.25) the ball dimension reads 1.72, 1.86, 2.02 and 2.24 at 200, 400, 800 and 1600 points, and the mean ball scalar curvature reads −0.46, −0.36, −0.28 and −0.21 hops⁻². These readings have the size of the readings on a uniform flat 3D box at the same sizes. They are UNCALIBRATED, describe the bias of the instrument at these sizes, and are not findings about the initial data of arXiv:2102.09363, whose Brill-Lindquist slice has zero scalar curvature (K̃_ij = 0, eq. 102, line 1421; H = R − K_ij K^ij + K², eq. 179, line 2659).

### (7) Runs on Brill-Lindquist point clouds

The reproduction runs use the HGEvolve engine (HypergraphRewritingEngine). Initial data: n points in the periodic box [−10, 10]³ with density proportional to ψ⁶, ψ = 1 + 0.25/r₁ + 0.25/r₂ (masses 0.5 at separation 1, arXiv:2102.09363 lines 6179-6181), horizons excised, two points linked when their coordinate distance is below c·(8000/n)^(1/3), each edge given a random direction. Evolution: single histories with one uniformly random match per step. All values are MEASURED unless marked.

Initial hypergraph against the link cut-off (seed 1):

| n | c | Edges | Directed walks of four edges |
|---:|---:|---:|---:|
| 200 | 1.0 | 458 | 14,412 |
| 200 | 1.25 | 877 | 102,695 |
| 200 | 1.5 | 1456 | 625,952 |
| 1600 | 1.0 | | 861,953 |
| 1600 | 1.25 | 7219 | 5,796,932 |
| 1600 | 1.5 | | 27,192,014 |

A walk may use one edge twice. The edge-distinct matches of the rule number 14,091 at n = 200, c = 1.0 and 623,255 at n = 200, c = 1.5. arXiv:2102.09363 gives no value of the cut-off (line 6176), and the cut-off changes the initial edge count and the number of matches of the rule by large factors.

- Vertex count. Each event creates a vertex u and removes the edges {y,z} and {z,w}, so z leaves the state when it has no other edge. At n = 200, c = 1.25, seed 1, with 877 edges throughout, the state has 200 vertices at step 0 and 828 at steps 1000 and 2000 on engine build 0f8f80e9, and 962 at step 1000 and 980 at step 2000 at engine master 9af852a4. At n = 1600 the vertex count goes from 1599 to 1699 over 100 events. arXiv:2102.09363 Tables 6-7 index the runs by a vertex count, which the rule changes.
- Components. The number of connected components at step 0, at the middle of the run and at the first repeated state: n = 200, c = 1.25, seeds 1, 2, 3: 1/3/40, 1/2/21, 1/2/41. n = 200, c = 1.0: 3/3/22. At n = 400, c = 1.25, the count rises from 1 to 11-12 by step 1000.
- Separation of the holes against the vertex spacing. The mean spacing is 3.42, 2.71, 2.15 and 1.71 for n = 200, 400, 800 and 1600, and the separation of the holes is 1. The points within 1.5 of a hole number 6, 11, 15 and 30.
- Graph distance between the neighbourhoods of the two holes (vertex sets within 1.5 of each hole). At n = 200, c = 1.25, seed 1 (2 and 4 vertices), on engine builds before cba811ca: distance 1 at steps 0 to 150, 2 at steps 200 to 550, 5 at step 600, 7 at steps 650 and 700. The history at engine master 9af852a4 gives distances 1 to 4. At n = 1600 (9 and 21 vertices): distance 1 at every fifth step from 0 to 100. The two neighbourhoods are adjacent at step 0 at both resolutions, so the distance starts at its smallest non-zero value and cannot register a merger. arXiv:2102.09363 lines 6192-6196 evolve the solution to t = 12M "with an intermediate check at time t = 6M, after which the two black holes merge".
- Events per initial edge. Before the first repeated state: 0.82 at n = 200 (721 events, 877 edges). With all events run: 0.55 at n = 400, 0.08 at n = 800, and 0.014 at n = 1600 (100 events, 7219 edges). One event per edge at n = 1600, c = 1.25 needs 7219 steps, about 3.5 hours at the measured 1.7 s per step.
- Repetition of the sampler. Single histories of the engine reach a state isomorphic to an earlier one at step 722, 648 and 697 (n = 200, c = 1.25, seeds 1-3), 300 (n = 200, c = 1.0) and 536 (n = 400, c = 1.0), and from that step every state is in one isomorphism class. The engine keys its "UniformRandom" choice on the canonical hash of the state and the canonical ranks of the matched edges (`canonical_transition_key` in `hypergraph/src/parallel_evolution.cpp` of HypergraphRewritingEngine), so the choice repeats with the class. The repetition is a property of the sampler.
- Update order (READ). The runs of this section apply one event per step on a single history. arXiv:2303.07282 lines 4640-4648 apply the rule "to every possible/matching (non-overlapping) subhypergraph at each step". The HGEvolve option "Generational" -> True (engine commit 0fac4f1c, 2026-10-24) applies at each step every match that shares no hyperedge with a match before it in the engine's standard order.
- Cost of a step (callgrind, one thread, engine builds before e5565f9c). One step costs a pass over all matches of the state: 335 × 10⁶ instructions per step at 877 edges (102,695 walks), 1.68 × 10⁹ at 1813 edges and 8.26 × 10⁹ at 3587 edges, 3.0 to 5.3 thousand instructions per match. Re-matching takes 63% at 877 edges.

The dimension and curvature readings of these runs are UNCALIBRATED (section 6).

## Status

- PROVED: the rule conserves edge count. In every evolution from N hyperedges, with any update order, every antichain of the causal graph has at most N/4 events and at most 5^t events lie within directed distance t of an event (`CausalHistory.gorardNamedRule_antichain_card_le`, `CausalHistory.gorardNamedRule_ball_card_le`).
- MEASURED: on the seeds above the cone-growth exponent lies between 0.77 and 1.26 and depends on the update order (section 4). The cone measure does not reproduce the dimension of sprinkled causal sets, so the values are UNCALIBRATED as dimensions (section 6).
- MEASURED: the rule is not confluent and not causal invariant. From the directed path of five edges, one complete history has 2 events and the other 1, with non-isomorphic terminal states of 7 and 6 vertices (section 5).
- OPEN: linear cone growth, stated in Lean as `CausalHistory.GorardNamedRuleConeGrowthLinear` (O1 in `STATUS_OF_GORARD_CLAIMS.md`).
- MEASURED: runs of the rule on Brill-Lindquist point clouds of 200 to 1600 points (section 7). They reach at most 0.82 events per initial edge before the sampler repeats a state at 200 points, and 0.014 at 1600 points. The graph distance between the neighbourhoods of the two holes does not fall.

A bounded spatial ball count holds on every finite hypergraph, so the constant edge count does not give the rule a spatial dimension that differs from any other rule run on a finite state. arXiv:2102.09363 compares runs at 100, 200, 400, 800 and 1600 vertices (Tables 6-7), and edge-count conservation within a run does not constrain a sequence of initial states of growing size.

The largest run has 2000 events. The measurements do not determine the exponent at larger event counts.

## Relation to arXiv:2004.14810 §3.3

The §3.3 argument of arXiv:2004.14810 uses a causal-graph cone count of the form $C(t) = a\,t^n(1 - \ldots)$ with $n = 4$ for 3+1 dimensions. On the seeds above the measured exponent is between 0.77 and 1.26. The cone measure is UNCALIBRATED on sprinkled causal sets (section 6). Whether the cone growth of this rule is linear on all initial data is OPEN.
