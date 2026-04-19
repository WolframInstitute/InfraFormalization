# Status snapshot

Live document of what's proved, what's in progress, and where we are on the infrageometry research programme roadmap ([`INFRAGEOMETRY.md`](INFRAGEOMETRY.md)).

## Machine-verified theorems (axiom-clean)

All proofs in Lean 4 + Mathlib 4.29.1, depending only on Lean's three standard axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`, no `decide`, no custom axioms. Verified by `#print axioms` (see [`lean/InfraFormalization/AxiomCheck.lean`](lean/InfraFormalization/AxiomCheck.lean)).

### Wolfram-model structural theorems (Phase 1)

| # | Theorem | File | Meaning |
|---|---|---|---|
| T1 | `Application.size_result_of_conservative` | Conservation.lean | Edge Conservation: \|LHS\|=\|RHS\| rule preserves state size. |
| T2 | `size_preserved_by_applications` | Conservation.lean | Trajectory-level extension of T1. |
| T3 | `edge_conservation`, `trajectory_preserves_size` | Demo.lean | Re-exports. |
| T4 | `growthExponentAtMost_of_linear` | Growth.lean | Auxiliary: f(n) ≤ Cn ⇒ growth exponent ≤ 1. |
| T5 | `in_degree_eq_lhsSize` | ParallelSchedule.lean | Every event has exactly \|LHS\| incoming expressions. |
| T6 | `out_degree_eq_rhsSize` | ParallelSchedule.lean | Every event has exactly \|RHS\| outgoing expressions. |
| T7 | `balanced_of_conservative` | ParallelSchedule.lean | Conservative rule ⇒ each event's consumption = production. |

### Infrageometry continuum-limit theorems (Phase 3)

Cycle-to-circle Gromov–Hausdorff: the two key theorems needed for GH convergence of the scaled n-cycle to the unit circle ℝ/ℤ.

| # | Theorem | File | Meaning |
|---|---|---|---|
| T8 | `cycleDist_self` | ScaledCycle.lean | Cycle-graph metric: d(i,i)=0. |
| T9 | `cycleDist_symm` | ScaledCycle.lean | Symmetric. |
| T10 | `cycleDist_le_half` | ScaledCycle.lean | Diameter ≤ n/2. |
| T11 | `cycleDist_zero_of_small` | ScaledCycle.lean | Degenerate for n ≤ 1. |
| T12 | `cycleDist_triangle` | ScaledCycle.lean | Triangle inequality (8-case analysis closed by `omega`). |
| T13 | `cycleDist_eq_zero_iff` | ScaledCycle.lean | d(i,j)=0 ⇔ i=j (for n ≥ 2). |
| T14 | `exists_lattice_index` | LatticeDensity.lean | For x ∈ [0,1) there is i ∈ Fin n with i/n ≤ x < (i+1)/n. |
| T15 | `lattice_one_over_n_dense` | LatticeDensity.lean | Lattice {i/n} is (1/n)-dense in [0,1). |
| T16 | `lattice_half_n_cover` | LatticeDensity.lean | For x ∈ [0,1), either x is within 1/(2n) right of i/n, or within 1/(2n) left of (i+1)/n. |
| T17 | `circleDist_{self,symm,nonneg,le_half}` | Circle.lean | Circle-distance on ℝ/ℤ: basic metric axioms. |
| T18 | `latticeEmbed_mem_unit_interval` | Circle.lean | φ_n(i) = i/n ∈ [0,1). |
| **T19** | **`latticeEmbed_covers`** | Circle.lean | **★** Every x ∈ [0,1) is within circle-distance 1/(2n) of some φ_n(i). |
| **T20** | **`latticeEmbed_isometry`** | Circle.lean | **★** φ_n is an isometry: circleDist(i/n, j/n) = cycleDist(i,j)/n. |

**T19 and T20 together are the two key ingredients for the Gromov–Hausdorff convergence of the scaled n-cycle to the unit circle.** T19 bounds the Hausdorff distance between the embedded image and the circle; T20 says the embedding preserves the scaled metric exactly. Together they give:

> **GH_dist( (Fin n, cycleDist/n), (ℝ/ℤ, circleDist) ) ≤ 1/(2n).**

This is the first formally-verified continuum-limit theorem ingredients in the project — the signature Phase 3 target of the infrageometry program. Packaging into a single named theorem pending.

## Audit deliverables (Phase 0)

| Artifact | Purpose |
|---|---|
| [`notes/claims_catalog.md`](notes/claims_catalog.md) | 184-row audit of every equation in G1 |
| [`notes/corpus_audit.md`](notes/corpus_audit.md) | Cross-paper map of repeated errors (G1–G4) |
| [`notes/continuum_limit_claims.md`](notes/continuum_limit_claims.md) | Every continuum-limit claim in the corpus, per-claim verdict |
| [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) | S1–S6 error classification |
| [`notes/{2004,2102,2303}_close_reading.md`](notes/) | Per-paper close readings |
| [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) | Why Gorard uses single-way; null tetrad explainer |
| [`notes/empirical_refutation.md`](notes/empirical_refutation.md) | Named rule → 1D causal graph empirically |
| [`results/phase1_selfaudit/`](results/phase1_selfaudit/) | Python rewriter ↔ SetReplace agreement |
| [`results/phase2_continuum/`](results/phase2_continuum/) | Eq 342 and Eq 344 four-rail refutations |

## Not-yet-done

| Target | Notes |
|---|---|
| Package T19+T20 into a single named theorem | Mechanical. |
| Parallel-layer bound (Theorem B) in Lean | Requires `level` function via well-founded recursion; earlier attempt got stuck. Try structural induction on the trajectory list. |
| Correct Ollivier identity in Lean | Requires Riemannian + optimal-transport Mathlib infrastructure. Partial. |
| Correct Gray tube formula in Lean | Requires Fermi normal coordinates (not yet in Mathlib). |
| Discrete Ollivier–Ricci convergence on directed hypergraphs | Trillos–Slepčev-style. Substantial. |
| First Wolfram-specific convergence theorem | Phase 5. Research-level. |

## Path on the infrageometry roadmap

- **Phase 0 (audit)**: ✅ done.
- **Phase 1 (structural theorems)**: partial. T1–T7 done; parallel-layer bound pending.
- **Phase 2 (correct identities)**: analytical corrections done (refutation files); Lean formalisation pending.
- **Phase 3 (first continuum-limit theorem)**: **essentially done** at the proof-ingredient level — T19+T20. Packaging pending.
- **Phase 4 (discrete geometric structures library)**: not started.
- **Phase 5 (Wolfram-specific convergence)**: not started.
- **Phase 6 (causal-set infrageometry)**: not started.
