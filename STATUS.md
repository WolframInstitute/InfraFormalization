# Status snapshot

Live document: what's proved, what's in progress, where we are on the
infrageometry research programme roadmap ([`INFRAGEOMETRY.md`](INFRAGEOMETRY.md)).

## Machine-verified theorems (axiom-clean)

**36 theorems**, all depending only on Lean's three standard axioms:
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no
`native_decide`, no `decide`, no custom axioms. Verified by
`#print axioms` in [`lean/InfraFormalization/AxiomCheck.lean`](lean/InfraFormalization/AxiomCheck.lean).

### Wolfram-model structural theorems (Phase 1)

| # | Theorem | File | Meaning |
|---|---|---|---|
| T1 | `Application.size_result_of_conservative` | Conservation.lean | Edge conservation. |
| T2 | `size_preserved_by_applications` | Conservation.lean | Trajectory-level edge conservation. |
| T3 | `edge_conservation`, `trajectory_preserves_size` | Demo.lean | Re-exports. |
| T4 | `growthExponentAtMost_of_linear` | Growth.lean | Linear ⇒ growth exponent ≤ 1. |
| T5 | `in_degree_eq_lhsSize` | ParallelSchedule.lean | In-degree = |LHS|. |
| T6 | `out_degree_eq_rhsSize` | ParallelSchedule.lean | Out-degree = |RHS|. |
| T7 | `balanced_of_conservative` | ParallelSchedule.lean | Conservative ⇒ per-event balance. |
| T8 | `total_in_degree_eq` | CausalLevel.lean | Sum of in-degrees = M·k. |
| T9 | `total_out_degree_eq` | CausalLevel.lean | Sum of out-degrees = M·k. |
| T10 | `total_in_eq_total_out` | CausalLevel.lean | Conservative ⇒ sums equal. |
| T11 | `level` | CausalLevel.lean | Causal-DAG level function. |
| T12 | `level_eq` | CausalLevel.lean | Level unfolding equation. |
| **T13** | **`level_add_one_le_of_isCausalPred`** | CausalLevel.lean | **★ Level monotonicity**: causal edge ⇒ level grows by ≥ 1. |
| T14 | `no_causal_edge_within_level` | CausalLevel.lean | Antichain property (forward direction). |
| T15 | `same_level_ordered_antichain` | CausalLevel.lean | Antichain alias. |

### Continuum-limit theorems (Phase 3)

| # | Theorem | File | Meaning |
|---|---|---|---|
| T16 | `cycleDist_{self,symm,triangle,le_half,zero_of_small,eq_zero_iff}` | Infra/ScaledCycle.lean | Cycle metric axioms. |
| T17 | `exists_lattice_index`, `lattice_one_over_n_dense`, `lattice_half_n_cover` | Infra/LatticeDensity.lean | Lattice density in [0,1). |
| T18 | `circleDist_{self,symm,nonneg,le_half}`, `latticeEmbed_mem_unit_interval` | Infra/Circle.lean | Circle metric axioms. |
| **T19** | **`latticeEmbed_covers`** | Infra/Circle.lean | **★ Cover bound** 1/(2n). |
| **T20** | **`latticeEmbed_isometry`** | Infra/Circle.lean | **★ Isometry**. |
| **T21** | **`cycle_circle_gh_bound`** | Infra/GHBound.lean | **★ Packaged cycle → circle GH convergence**. |
| T22 | `cycle_circle_eventual_epsilon_dense` | Infra/GHBound.lean | ε-convergence corollary. |
| T23 | `pathDist_{self,symm,triangle,le}` | Infra/ScaledPath.lean | Path metric axioms. |
| T24 | `pathEmbed_{mem_unit_interval,isometry,covers}` | Infra/ScaledPath.lean | Path embedding properties. |
| **T25** | **`path_interval_gh_bound`** | Infra/ScaledPath.lean | **★ Path → interval GH convergence**. |
| T26 | `GHApproximation`, `ghApprox_of_half_scale` | Infra/GHApprox.lean | Abstract GH-approximation structure. |

### Corrected continuum identities (Phase 2)

| # | Theorem | File | Meaning |
|---|---|---|---|
| T27 | `OllivierIdentityLeading`, `GorardMisstatedForm` | Infra/OllivierStatement.lean | Correct and Gorard-incorrect Ollivier. |
| T28 | `ollivier_vs_gorard_equivalence_requires_ric_eq_scalar` | Infra/OllivierStatement.lean | Coincidence condition. |
| T29 | `GrayTubeLeading`, `GorardTubeForm` | Infra/GrayTubeStatement.lean | Correct and Gorard-incorrect Gray tube. |
| T30 | `gray_vs_gorard_disagree_on_S2` | Infra/GrayTubeStatement.lean | Concrete disagreement: 1/6 ≠ 1/3. |
| T31 | `gray_vs_gorard_disagree_on_S3` | Infra/GrayTubeStatement.lean | Concrete disagreement: 1/3 ≠ 2. |

## Audit deliverables (Phase 0)

See [`INDEX.md`](INDEX.md) for the full document tree. Key artifacts:

- [`FINDINGS.md`](FINDINGS.md) — canonical one-line verdict summary
- [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) — S1–S6 classification
- [`notes/corpus_audit.md`](notes/corpus_audit.md) — cross-paper propagation
- [`notes/continuum_limit_claims.md`](notes/continuum_limit_claims.md) — per-claim verdict
- [`notes/claims_catalog.md`](notes/claims_catalog.md) — 184-row G1 audit
- [`notes/{2004,2102,2303}_close_reading.md`](notes/) — per-paper close readings
- [`results/phase1_selfaudit/`](results/phase1_selfaudit/) — SetReplace ↔ Python agreement
- [`results/phase2_continuum/`](results/phase2_continuum/) — four-rail refutations of Eq 342 and Eq 344

## Path on the infrageometry roadmap

- **Phase 0 (audit)**: ✅ done.
- **Phase 1 (structural theorems)**: in flight. Edge conservation, in/out degrees, level monotonicity, same-level antichain property done. Full parallel-layer bound (|layer_s| ≤ N/k) requires state-at-each-level tracking.
- **Phase 2 (correct continuum identities)**: analytical refutations done; Lean statement-level formalisation of correct Ollivier and Gray forms done, with proven disagreement from Gorard's forms on concrete cases (S², S³).
- **Phase 3 (continuum-limit theorems)**: **two complete examples** — cycle → circle, path → interval — both packaged under the common `GHApproximation` abstraction.
- **Phase 4 (discrete geometric structures library)**: not started.
- **Phase 5 (Wolfram-specific convergence)**: not started.
- **Phase 6 (causal-set infrageometry)**: not started.

## Next concrete directions

1. **2D continuum limit**: scaled 2D lattice → flat torus or unit square. Same template as cycle and path; the product structure adds some work.
2. **Full parallel-layer bound**: requires an additional trajectory-structure lemma (events only consume earlier-produced expressions); then the state-size tracking argument.
3. **Start Phase 4**: define `DirectedHypergraph` with a metric-measure-space instance; begin porting Eidi–Jost directed-Ollivier-Ricci.
4. **A Wolfram-model rule with a proved continuum limit**: even a very simple one (e.g., a rule that builds up a cycle graph) would be a first Phase-5 exemplar.
