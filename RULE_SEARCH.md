# Rule search with the Lean library

The Lean library can check and screen candidate Wolfram-model rules in a search for rules whose causal graph approximates a Lorentzian manifold. It does not generate rules beyond the small bounded families described below. It supplies decidable screening predicates and the theorems that hold for every rule.

Status labels follow `STATUS_OF_GORARD_CLAIMS.md`: PROVED (axioms at most `propext`, `Classical.choice`, `Quot.sound`), PROVED-WITH-NATIVE-DECIDE, MEASURED, READ, OPEN.

## Results available to a search

### Negative screening

| Mechanism | Lean result | Status | Content |
|---|---|---|---|
| Edge-count conservation | `Application.size_result_of_conservative`, `trajectory_size_invariant` | PROVED | A rule with \|LHS\| = \|RHS\| keeps the edge count of every state equal to the initial edge count. This does not bound the cone dimension of the causal graph. `Refutations.gorardNamedRule_applications_preserve_size` (F7) states it for the rule of arXiv:2102.09363. |
| Antichain bound | `CausalHistory.RuleHistory.antichain_card_le` | PROVED | For a rule with \|LHS\| = \|RHS\| = k and N initial hyperedges, every antichain A of the causal graph satisfies k·\|A\| ≤ N, for every update order. |
| Cone bound | `CausalHistory.RuleHistory.ball_card_le` | PROVED | At most (\|RHS\| + 1)^t events lie within directed distance t of an event. For the rule of arXiv:2102.09363 this is 5^t (`CausalHistory.gorardNamedRule_ball_card_le`). |
| Same-level antichain | `no_causal_edge_within_level`, `Infra.same_level_not_causal` | PROVED | Events at the same causal level have no causal edge between them (value-based causal relation of `CausalLevel.lean`). |
| Linear cone growth | `CausalHistory.GorardNamedRuleConeGrowthLinear` | OPEN | For every N there is c such that every valid `RuleHistory` of the rule of arXiv:2102.09363 with N initial hyperedges satisfies \|ball i t\| ≤ c·(t+1). |
| Cone-growth exponent | `scripts/python/run_all_seeds.py`, SetReplace scripts | MEASURED | For the rule of arXiv:2102.09363 on 9 seeds of up to 300 edges and 2000 events, exponents between 0.77 and 1.26 depending on the update order (`notes/empirical_refutation.md` §4). A measurement on finite seeds does not prove a bound. |

### Quantitative signatures

These per-rule observables would track dimension if the causal graph approximates a (d+1)-dimensional Minkowski space. They are definitions for a screener. No theorem connects them to a dimension.

1. Level growth: `|{j : j < N ∧ level τ j ≤ t}|`, compared against t^{d+1}. Lemmas used: `level_add_one_le_of_isCausalPred`, `level_eq` (PROVED).
2. Antichain width: `|{j : level τ j = k}|`, compared against k^d. Lemma used: `no_causal_edge_within_level` (PROVED).
3. Forward-cone volume: `|{j : causallyPrecedes τ i j ∧ level τ j ≤ level τ i + t}|`, compared against t^{d+1}. Lemmas used: `causallyPrecedes_implies_lattice_time_order`, `causallyPrecedes_implies_timelike` (PROVED; they map the causal order into the 1+0-dimensional Lorentz lattice).
4. Embedding consistency: given a spatial embedding `φ : event-index → Fin d → ℤ`, check that every pair with `causallyPrecedes τ i j` satisfies `Timelike d (fullEmbed φ i) (fullEmbed φ j)`. The check is decidable. In 1+0 dimensions it always holds (`causallyPrecedes_implies_timelike`, PROVED). In d spatial dimensions `fullEmbed_preserves_causal` (PROVED) gives it under the hypothesis `LightConeCompatible τ φ`.

### Screening on the executable engine

`RuleSignatureExecMetrics.lean` screens a candidate rule on the engine's states (`ExecHG ℕ`, lists of hyperedges over ℕ) without building an abstract `Trajectory`. `MultiwayExec.singleWayStep` applies a maximal set of edge-disjoint matches, chosen greedily in enumeration order. For a rule with a one-edge left-hand side every pair of matches on distinct edges is edge-disjoint.

For a rule `r`, seed `H` and horizon `n`:

1. `d := canonicalDossier r H n` records the run of `singleWayEvolve`. `canonicalDossier_isConsistent` and `consistent_dossier_eq_canonical` (PROVED) state that a dossier passes the consistency check exactly when it equals this run.
2. `d.signatureVerdict` returns the per-state triple of edge counts, vertex counts and Forman scalars.
3. Decidable predicates accept or reject: `d.formanScalarConstant`, `d.formanScalarReaches tgt`, `d.formanScalarPersistentGap tgt` (no state attains `tgt`).

The metric primitives are `execAdj`, `execAdjDegree`, `execTriangles`, `execFormanEdge` (equal to `Hypergraph.formanRicciEdgeTriangle`, `4 − deg u − deg w + 3·#triangles`) and `execFormanScalar` (equal to `Hypergraph.formanRicciTriangleDoubled`). Example: the edge-append rule from a single edge gives `⟨[1,2,4,8], [2,3,5,9], [4,4,0,-12]⟩` (PROVED-WITH-NATIVE-DECIDE).

The same triple, computed by these formulas, is the metric set to implement in the HypergraphRewritingEngine for runs at scale.

### Bounded search loop

`RuleSignatureExecSearch.lean` generates, runs, classifies and selects rules.

- Generate: `enumerateRules2_1 maxRHS` lists the rules with left-hand side `{0,1}` and right-hand side a nonempty subset, of size at most `maxRHS`, of the ordered pairs over `Fin 3` (two bound vertices and one fresh vertex). There are 21 rules at `maxRHS = 2`.
- Classify: `trendOf r seed n` reduces the Forman-scalar trace of `canonicalDossier` to a `CurvatureTrend`: `flat` if constant, otherwise the sign of the final scalar (`positive`, `negative`, `zero`).
- Select: `selectByTrend cands seed n tgt` keeps the rules with the target trend.

On the single-edge seed at two steps the 21 rules split into 13 flat, 4 zero and non-constant, 2 negative and 2 positive (PROVED-WITH-NATIVE-DECIDE). The trend is the sign of the final Forman scalar on a finite run. It is not a convergence statement.

### Multi-seed filter

A rule can show one trend on one seed and another trend on a different seed. `RuleSignatureExecSearch.lean` adds:

- `seedSet = [edge12, path123, cycle4]` (an edge, a path and a 4-cycle);
- `trendsAcross r seeds n`, the trend on each seed;
- `isStablyTrend r seeds n tgt`, true when every seed gives `tgt`;
- `stablyClassifiable r seeds n`, true when every seed gives the same trend;
- `stableSelect cands seeds n tgt`.

On `seedSet` at two steps: 7 rules are flat on every seed, 2 negative on every seed, 2 positive on every seed and 0 zero on every seed, so 11 rules have the same trend on all three seeds. The other 10 rules change trend with the seed (PROVED-WITH-NATIVE-DECIDE).

### Checking a candidate rule

For a candidate rule:

- Build a `Trajectory sys init` for sample runs.
- The level function `level τ` maps events into the 1+0-dimensional Lorentz lattice and preserves causal precedence (`trajectoryToEvent_preserves_causal`, PROVED). Events at the same level map to the same point (`trajectoryToEvent_lossy`, PROVED).
- These theorems hold for every rule, so no proof is repeated per rule.
- A chosen spatial embedding can be checked for `Timelike` consistency on every causal pair.

## Results the library does not supply

- Rule generation beyond the bounded families above. A separate generator is needed (`../efficient_rewriting_final/`, SetReplace, heuristic search).
- A spatial embedding constructed from a hypergraph. The library checks an embedding that the user supplies.
- Curvature of named metrics in general. Ricci tensors are computed for `warpedDiag2` (`WarpedDiag2C2.lean`) and FLRW (`FLRWRicci.lean`). The Schwarzschild Riemann and Ricci tensors are OPEN (B2, B3). The Ollivier and Gray identities are stated, and their leading terms are compared on S² and S³ (`Infra/OllivierStatement.lean`, `Infra/GrayTubeStatement.lean`).

## Pipeline

1. Generator: `../efficient_rewriting_final/` writes the initial hypergraph and the sequence of applications for each candidate rule.
2. Python screener: computes the level distribution, antichain widths and cone-volume growth from the trajectory data.
3. Growth filter: rejects rules whose growth differs from t^{d+1} and k^d for the target d.
4. Embedding search: for the remaining rules, tries embeddings into `Fin d → ℤ` (graph layout, spectral embedding, heuristics).
5. Lean check: imports the trajectory as a `Trajectory`, loads the embedding, and checks `Timelike` consistency on every causal pair.

## Scope

The pipeline checks that a candidate rule's causal graph is consistent with a chosen embedding into a Lorentz lattice. The following are OPEN:

- convergence of a rule's causal graph to a Lorentzian manifold, which needs a scaled-trajectory Gromov-Hausdorff theorem;
- curvature data for the rule's states compared against a continuum metric;
- that the limit satisfies the Einstein equations, which needs the convergence of the discrete action (F5 in `MAJOR_FLAWS.md`).

`MILESTONES.md` lists these under Phases 4, 5 and 6.

## References

- `lean/InfraFormalization/CausalLevel.lean`: level function, monotonicity, antichain.
- `lean/InfraFormalization/CausalHistory.lean`: causal graph on hyperedge identities, antichain and cone bounds, the open statement `ConeGrowthLinear`.
- `lean/InfraFormalization/Infra/TrajectoryLorentz.lean`: map into the 1+0-dimensional lattice.
- `lean/InfraFormalization/Infra/LorentzLattice.lean`: `CausalPrecedes`, `Timelike`, `Null`, `Spacelike`, `minkowskiIntervalSq`.
- `results/phase1_selfaudit/`, `notes/empirical_refutation.md`: cone-exponent measurements for the rule of arXiv:2102.09363.
- `MAJOR_FLAWS.md`: F1 (no metric construction in G1), F2 (orthonormality assumption), F5 (convergence notion not stated).
