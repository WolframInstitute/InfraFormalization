# Candidates for universal theorems

Several results in the library are checked by `native_decide` at finitely many rules, seeds and depths. The three items below are statements that would replace such finite checks with a theorem for all parameters. Each has a task number.

Status labels follow `STATUS_OF_GORARD_CLAIMS.md`: PROVED, PROVED-WITH-NATIVE-DECIDE, MEASURED, READ, OPEN.

Operator note. `MultiwayExec.singleWayStep` applies a maximal set of edge-disjoint matches, chosen greedily in enumeration order. `MultiwayExec.fireAllStep` applies every match found in the input state, including matches that share edges, and is not a Wolfram model update when matches overlap. The modules `UniversalAdditivity` (multi-rule section), `StepZeroAncestor` and `PartitionClosure` state their results with the fire-all operator (`fireAllEvolve`, `tracedFireAllEvolve`, `causalDAGOfFireAll`). Their finite checks concern that operator and do not describe Wolfram model evolutions.

## #495: per-edge additivity

Statement (OPEN). For a rule `r` with a one-edge left-hand side (`r.lhs.length = 1`):

```
∀ seed d, knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ seed d)
            = (# distinct edges of seed) · knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ edge12 d)
```

`causalDAGOfEvolution` is built from `tracedSingleWayEvolve`. It relates events through hyperedge values (`causalDAGOfEvents`), which differs from the causal graph on hyperedge identities of `CausalHistory.lean` when a state holds two equal hyperedges.

Finite checks. The identity is checked at finitely many (rule, seed, depth) tuples in `UniversalAdditivity.lean` and `StableDiscoveredRules.lean` (PROVED-WITH-NATIVE-DECIDE). The multi-rule section of `UniversalAdditivity.lean` uses the fire-all operator (see the operator note).

The factor 7 in `per_edge_additivity_instances` is the number of edges of `twoTriangleSeed`, a 6-vertex graph of two triangles joined by one edge (`TwoTriangleSeed.lean`). This graph is not the Brill-Lindquist initial data of arXiv:2102.09363.

Attack path:

1. `knillEulerScaled` is additive over vertex-disjoint unions: PROVED (`PerEdgeAdditivityFramework.K1_proved`).
2. `knillEulerScaled` is invariant under a bijective relabelling of vertices: PROVED (`PerEdgeAdditivityFramework.K2_proved`).
3. The engine commutes with disjoint union for one-edge left-hand sides, up to relabelling of fresh vertices: OPEN.
4. Compose 1-3 into per-edge additivity for vertex-disjoint seeds: OPEN.
5. Apply to a seed whose edges have disjoint causal sub-DAGs: OPEN.

`twoTriangleSeed` is not vertex-disjoint. The relevant property is that the causal sub-DAGs rooted at distinct seed edges are disjoint. Lean: none. `EdgeCausallyDisjointBridge.lean` defines `predOf` and `stepZeroAncestorSet`, which compute the step-0 ancestors of an event, and contains no theorems.

Seeds that share vertices (`path123`, `triangle`) need a decomposition of the causal DAG itself: each step-0 match starts a sub-DAG of later events. Causal edges in `causalDAGOfEvents` are defined by produced and consumed edges, not by shared vertices.

### Sub-tasks of #495

- #498 (#495a), fresh-vertex partition: `FreshVertexPartition.fresh_slices_disjoint_across_matches` is PROVED for `FreshVertexPartition.innerFoldl`. That fold is a copy of the per-match fold of `tracedFireAllStep`, so the result concerns the fire-all operator.
- #499 (#495b), partition closure: `PartitionClosure.lean` states its results for `fireAllStep` (`partitionClosure_base`, `partitionPreserving_certified`). The corresponding statement for `singleWayStep` is OPEN.
- #500 (#495c), step-0 ancestor: `StepZeroAncestor.lean` defines `stepZeroAncestor` and proves `stepZeroAncestor_step_zero` and `step_zero_events_exist` for `tracedFireAllEvolve` (PROVED). OPEN: that every event has a unique step-0 ancestor, for `tracedFireAllEvolve` and for `tracedSingleWayEvolve`.
- #501 (#495d), disjointness of the causal sub-DAGs rooted at distinct step-0 events: OPEN.
- #502 (#495e), composition of K1 and K2 into per-edge additivity for seeds whose causal sub-DAGs are disjoint: OPEN. Lean: none.
- #503 (#495f), disjointness of the causal sub-DAGs of `twoTriangleSeed` at every depth: OPEN. Lean: none.

## #496: Knill's identity Σ_v K6(v) = 6·χ

Statement. `knillVertexK6 H v = 6 − 3·deg(v) + 2·T(v)`, where T(v) is the number of triangles at v. For every `H : ExecHG ℕ`, `knillEulerScaled H = 6 · eulerChar H` with `eulerChar H = V − E + T` (vertices, 1-skeleton edges, 3-cliques).

Status: PROVED as `KnillEulerCharIdentity.knill_eq_six_euler_char`, by summing degrees (`sum_degree_eq_twice_edges`) and triangle counts (`sum_triangle_count_eq_thrice_triangles`). This is Knill's theorem (arXiv:1009.2292, Theorem 1) for the 2-skeleton of the clique complex.

`eulerChar` counts cliques up to size 3. It equals the Euler characteristic of the clique complex when the graph has no 4-clique. For `K₅` (the 1-skeleton of ∂Δ⁴) it gives 5 − 10 + 10 = 5, while χ(S³) = 0. `KnillThreeManifold.lean` uses a separate sum `knillEulerScaled12` for that case.

Corollaries on the tetrahedron, octahedron and icosahedron compute `eulerChar = 2` by `native_decide` (PROVED-WITH-NATIVE-DECIDE). The earlier finite checks are in `KnillDiscreteGaussBonnet.lean`, `KnillHigherGenus.lean` (tori with n ∈ {4, 5, 6}) and `KnillThreeManifold.lean`.

## #497: closed forms for path, cycle and torus scalars

Statements (OPEN):

- `Forman(path_n) = 4` for all n ≥ 3;
- `Higuchi(path_n) = 2` for all n ≥ 3;
- `SquareCount(path_n) = 0` for all n ≥ 3;
- a closed form for `Forman(T^d(n, …, n))` for all d and n beyond the smallest cases;
- a closed form for `Higuchi(T^d)`.

Finite checks: `PathContinuumLimit.lean` (for example `path_3_forman_4` to `path_32_forman_4`), `CycleContinuumLimit.lean`, `NormalizedDensityLimits.lean`, `PolynomialDensityLimits.lean`, `GridContinuumLimit.lean` (PROVED-WITH-NATIVE-DECIDE). The forms above would give, for every n, the value of the scalar on `path_n` and `T^d`. The Forman scalar of a path or cycle is a sum over vertices determined by degree: path degrees are `[1, 2, …, 2, 1]` and cycle degrees are all 2.

## Statements not proposed for upgrade

- `LiteratureRules` annotations of the form "emergent 2D Euclidean space", "hyperbolic emergence", "square emergence". They describe pictures of runs and are not theorems.
- `RulePreservationClassification` ("any well-designed catalog"), which has no formal statement.
- H9 distinct-edge tripling (#492). The H9 modules (`H9Bridge`, `H9BridgeStepProof`, `H9Closure`, `H9StructuralProgress`, `DistinctEdgeAPI`, `DistinctEdgeIdentity`) state their results with the fire-all operator.

## Status

- #495: OPEN. K1 and K2 are PROVED. The remaining steps are listed above.
- #496: PROVED (`KnillEulerCharIdentity.knill_eq_six_euler_char`).
- #497: OPEN.
