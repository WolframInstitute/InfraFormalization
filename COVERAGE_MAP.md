# Coverage map — done / in-progress / open

**Single source of truth for project posture.** Updated whenever a Lean file is added, a task is completed, or a research direction is opened. Complements `INFRAGEOMETRY.md` (program description) and the task system (atomic items).

Legend: ✅ proved, axiom-clean. 🟡 partial. 🔲 open. 🚫 uninhabited formal obligation.

## 1. Core rewriting substrate

| Module | Content | Status |
|---|---|---|
| `Hypergraph.lean` | `Hypergraph V`, `Hyperedge`, `map`, `size` | ✅ |
| `Rule.lean` | `Rule P`, `IsConservative` predicate | ✅ |
| `Application.lean` | `Application r H`, `result`, sigma-bundle lemmas | ✅ |
| `Conservation.lean` | **Theorem A**: conservative rule preserves size | ✅ |
| `Multiway.lean` | `RewritingSystem`, `Step`, `MultiStep`, `Confluent` | ✅ |
| `Causal.lean` | `Trajectory`, `causallyPrecedes` | ✅ |
| `CausalLevel.lean` | Level function, antichain theorems | ✅ |
| `Branchial.lean` | `BranchialRelated`, `NStep`, `BranchialSlice` | ✅ |
| `ParallelSchedule.lean` | `trajectory_preserves_size`, in/out-degree | ✅ |
| `Demo.lean` | `edge_conservation` end-to-end demo | ✅ |
| `Rewriting.lean` | Auxiliary scaffold | ✅ (legacy) |

## 2. Hypergraph calculus

| Module | Content | Status |
|---|---|---|
| `DiscreteCalculus.lean` | Graph Laplacian, inner product on `Neighbourhood` | ✅ |
| `DiscreteCalculusSymm.lean` | Self-adjoint Δ, Dirichlet PSD, `laplacian_sum_zero` | ✅ |
| `HypergraphLaplacian.lean` | `laplacianHyper`, Dirichlet non-positivity, self-adjointness, per-edge bilinear identity | ✅ |
| `HypergraphCalculus.lean` | `hyperedgeGradient`, `hypergraphDiv`, `summation_by_parts` (Stokes) | ✅ |
| `SecondDifference.lean` | Central second difference, quadratic identity | ✅ |
| `CycleGraph.lean` | `cycleLaplacian`, cycle Dirichlet form | ✅ |
| `CTwoTaylor.lean` | C² Taylor convergence of scaled second difference — `scaledSecondDiff_tendsto_iteratedDeriv` | ✅ R1 / A2 |
| `CycleSpectrum.lean` | `cycleEigenvector`, `cycleEigenvalue`, `cos_three_term_identity`; interior + full wrap-around eigenvalue equations | ✅ R5 |
| `CycleEigenLimit.lean` | Scaled cycle eigenvalue → continuum circle Laplacian eigenvalue — `cycleEigenvalue_scaled_tendsto` | ✅ A4 |
| `ScaledDiffC2Bridge.lean` | `scaledSecondDiff_tendsto_iteratedDeriv_C2` + `hypergraph_scaled_laplacian_eq_scaledSecondDiff`: end-to-end hypergraph → f'' for all C² | ✅ A3 |
| `LaplacianMatrix.lean` | `laplacianMatrixEdge`, `laplacianMatrix`, `laplacianMatrix_mulVec`, `heatKernel = exp(t · Δ)`, `heatKernel_zero`, `heatKernel_add`, `heatTrace`, `laplacianMatrix_symm`, `laplacianMatrix_row_sum`, `laplacianMatrix_mulVec_const` | ✅ R2 / D3 |
| `CycleMatrixSpectrum.lean` | Matrix eigenvalue equation: `laplacianMatrix (cycleHypergraph n) * cycleEigenvector = cycleEigenvalue • cycleEigenvector` | ✅ |

## 3. PDE ladder on `Hypergraph V`

All proofs go through `laplacianHyper`. The Hypergraph is the domain; no continuum appears.

| Module | Equation | Conservation law | Status |
|---|---|---|---|
| `HeatEquation.lean` | `u' = Δ_H u` | Mass `∑u`, L² decay | ✅ D1 + D4 + D5 |
| `WaveEquation.lean` | `u'' = Δ_H u` | Energy `∑(du)² − ∑u·Δu` | ✅ D8 |
| `KleinGordon.lean` | `u'' = Δ_H u − m²u` | Energy + mass term | ✅ D9 |
| `SchrodingerEquation.lean` | `iψ' = −Δ_H ψ` | Probability `∑|ψ|²` | ✅ D10 |
| `ScalarField.lean` | Lagrangian + Hamiltonian + EL | `EL ↔ KG` equivalence | ✅ G1 + G3 + G4 |
| `DiscreteDAlembertian.lean` | BD 4D operator, `discreteAction`, `discreteEL` | BD conjecture flagged | 🟡 operator + action ✅; BD conjecture 🚫 |

Pending in this group: D2 existence-uniqueness, D6 long-time convergence, D7 discrete → continuum heat on GH limit, D11 Choquet-Bruhat.

D3 (heat semigroup via `Matrix.exp`) is now ✅ in `LaplacianMatrix.lean`.

## 4. Continuum limits (Rungs 1–6)

| Module | Content | Status |
|---|---|---|
| `Infra/ScaledCycle.lean` | `cycleDist`, scaled n-cycle metric | ✅ |
| `Infra/LatticeDensity.lean` | `latticeEmbed`, density, isometry | ✅ |
| `Infra/Circle.lean` | Circle metric via fundamental domain | ✅ |
| `Infra/GHBound.lean` | `cycle_circle_gh_bound` — first GH limit | ✅ Rung 1 |
| `Infra/ScaledPath.lean` | Path → interval GH | ✅ |
| `Infra/ScaledTorus.lean`, `ScaledTorusD.lean` | 2D / dD lattice → torus | ✅ Rung 2 |
| `Infra/GHApprox.lean` | `GHApproximation` abstract structure | ✅ |
| `Infra/OllivierStatement.lean` | Correct Ollivier + Gorard mis-statement | ✅ Rung 3 statement |
| `Infra/GrayTubeStatement.lean` | Correct Gray tube + disagreement proofs | ✅ |
| `Infra/LorentzLattice.lean` | Discrete Lorentzian lattice, causal trichotomy | ✅ |
| `Infra/Minkowski.lean` | Continuum Minkowski with L∞ spatial metric | ✅ |
| `Infra/TrajectoryLorentz.lean`, `TrajectoryLorentzD.lean` | Trajectory → Lorentz lattice embedding | ✅ |
| `Infra/ScaledLorentz.lean` | Lattice → ℝ^{d+1} exact scaling + iff preservation | ✅ |
| `Infra/FullBridge.lean` | End-to-end causal → continuum Minkowski | ✅ |
| `LaplacianBridge.lean` | `scaledSecondDiff` = `f''` on polynomials exactly | ✅ Rung-2 polynomial bridge |
| `HypergraphCycleBridge.lean` | `cycleHypergraph n` + `laplacianHyper = cycleLaplacian` + end-to-end to `f''` | ✅ hypergraph-anchor of cycle bridge |
| `ContinuumLimitStatement.lean` | Formal Props for open obligations | 🚫 `SchwarzschildObligationMet`, `KerrObligationMet`, `FLRWObligationMet` all `∧ False` |

General C² case now proved in `CTwoTaylor.lean` + `ScaledDiffC2Bridge.lean` — the scaled discrete Laplacian on `cycleHypergraph n` converges to `f''` for any `ContDiff ℝ 2 f` (R1/A2/A3 done).

## 5. Curvature / connection (local-coord)

| Module | Content | Status |
|---|---|---|
| `CurvatureLocalCoord.lean` | `MetricData n`, Christoffel symbols with lower-index symmetry, Minkowski = 0 | ✅ |
| `CurvatureRiemann.lean` | Riemann, Ricci, Scalar, Einstein tensors; `bianchi_first`; flat-connection vanishing; `minkowski4_satisfies_vacuum_EFE`; `MetricDataC2`; `leviCivitaConnection` | ✅ |
| `Schwarzschild.lean` | `sgg`, `sginv`, `sdg` components; `SchwarzschildValid` exterior predicate; `sginv_mul_sgg`; **all 8 Christoffels** | ✅ B1 complete |
| `DiscreteRicci.lean` | Forman-Ricci on graphs + hypergraphs; sign-of-curvature theorems | ✅ |
| `RicciBridge.lean` | Circle / cycle Ricci = 0 match (discrete Forman ↔ continuum Ricci) | ✅ |

Pending in this group: B2 Schwarzschild Riemann components, B3 `Ric = 0`, B4 vacuum EFE, B5 Schwarzschild as PartialMetricData, B6 FLRW, B7 FLRW Ricci, B8 Reissner-Nordström, B9 Kerr, B10 Ricci symmetry (for Levi-Civita), B11 second Bianchi.

## 6. Refutation track

| Module | Flaw | Status |
|---|---|---|
| `Refutations/F1NoMetric.lean` | No canonical metric from hypergraph alone | ✅ refuted |
| `Refutations/F2Orthonormality.lean` | Fiat orthonormality is non-canonical | ✅ refuted |
| `Refutations/F3Tautology.lean` | "dim preservation ⇒ Einstein" = `Iff.rfl` | ✅ refuted |
| `Refutations/F4Tautology.lean` | "causal invariance ⇔ covariance" = `Iff.rfl` | ✅ refuted |
| `Refutations/F5Illdefined.lean` | Discrete → integral is under-determined | ✅ refuted |
| F6 (BD conjecture) | Benincasa-Dowker load-bearing assumption | 🚫 flagged in `DiscreteDAlembertian.lean` |

## 7. Infradimension

| Module | Content | Status |
|---|---|---|
| `HypergraphDistance.lean` | `Hypergraph.dist`, `geodesicBall`, `geodesicBallVolume`, `localDimension`, `wolframHausdorffDimension`, `plateauDimension`; cycle: `Adj_iff`, `succ_pred_adj`, `ballVolume_one_ge_three` | ✅ ID1 |
| `RuleDimensionBounds.lean` | `Trajectory.StepConsistent`, `trajectory_size_invariant`, `geodesicBallVolume_le_card` | ✅ IR2 |

Pending in ID: ID2 plateau detection, ID3 homology dim, ID4 coordinatization dim, ID5 causal-graph dim, ID6 compatibility theorem, ID7 spectral dim via `Matrix.exp`.

## 7b. Infragauge / Infracausality / Infratopology / Synthetic / Blowup / Ruliology

| Module | Content | Status |
|---|---|---|
| `FiberedGraph.lean` | `FiberedGraph V W` structure; `fiber`, `disjoint_fibers`, `exists_unique_fiber`; `IsSection`, `SmoothSection`; `Connection`, `connectionAdj`, `connectionAdj_implies_total_Adj` | ✅ IG1 + IG2 + IG3 |
| `Holonomy.lean` | `IsHorizontalLift`; `ParallelTransportList`; `Holonomy`; `wilsonLoop`; `IsFlatConnection`; `flat_holonomy_all_fixed` | ✅ IG4 + IG5 + IG6 + IG7 |
| `CausalGraphType.lean` | `CausalGraph V` TR-DAG; `causallyPrecedes` (refl+trans), `causalEdge_implies_precedes`; `ChainOfLength` observer chain; `DegenerateInterval`, `OnLightStepFrom` | ✅ IC1 + IC2 + IC3 |
| `CausalFoliation.lean` | `IsAntichain`; `IsFoliation` (antichain+disjoint+covers); `FiniteSupportFoliation`; `HasProperTime`, `properTime_self_exists` | ✅ IC4 |
| `BranchialFinite.lean` | `successors`, `BranchialSliceFinite`; `branchialSliceFinite_zero / _succ / _of_successors_finite` | ✅ I1 (#84) |
| `VietorisRips.lean` | `VietorisRipsEdge`, `VietorisRipsSimplex` with mono / empty / singleton / mono_scale; `vietorisRipsGraph` as SimpleGraph; `vietorisRipsGraph_zero_no_edges_reachable` | ✅ IT1 |
| `SyntheticGeometry.lean` | `SyntheticCircle`, `SyntheticBall`, `SyntheticLineSegment`, `SyntheticSphere`; `mem_syntheticCircle`, `syntheticCircle_zero`, `center_not_on_circle`, `syntheticCircle_subset_ball`, `syntheticCircle_disjoint`, `endpoints_on_segment` | ✅ IS1 |
| `ElementaryBlowup.lean` | `ElementaryBlowup P` structure (single-hyperedge LHS); `headEdge`, `apply`, `rhsSize`, `Order` | ✅ IB1 |
| `DagBlowup.lean` | `dagEdge`, `dagAsBlowupOfInterval n`; `dagDerivative`; linearity (`_add`, `_smul`, `_const`) | ✅ IA1 |
| `RuleSignature.lean` | `RuleSignature V` structure (hausdorffDimAt, ballVolume, totalFormanRicci, edge/vertex counts); `hypergraphSignature`; `avgFormanRicci`; match predicates (`sameDim`, `sameBallVolume`, `sameEdgeCount`, `FullMatch`); `edgeCount_invariant_of_conservative` | ✅ IR1 |

## 8. Groups from the full Infrageometry program

From `INFRAGEOMETRY.md` — 9 groups (57 new tasks #109–#165). Status:

| Group | Name | Done | Open |
|---|---|---|---|
| IA | Infraanalysis (DAG calculus, de Rham, blowups) | 5 | 0 |
| IG | InfraGaugeTheory (port Pokorny paclet) | 10 | 1 (#123 IG10) |
| IC | Infracausality (EPS, MW-clock) | 8 | 0 |
| IT | Infratopology (VR + Latschev) | 6 | 0 (IT3/IT5/IT6 as obligations) |
| ID | Infradimension | 7 | 0 (ID6/ID7 as obligations) |
| IB | Infrablowup (Lie algebra, Poisson) | 6 | 0 |
| IQ | Branchial / quantum | 5 | 0 (IQ6/IQ8/IQ9 as obligations) |
| IS | Synthetic axiomatic | 3 | 0 |
| IR | Ruliology | 7 | 0 (IR7 as obligation) |

Total for new groups: **57/57** addressed. But honest breakdown:
- ~38 tasks are real theorems or constructions.
- ~12 tasks are predicate-level scaffolding (types, sentinel Props).
- ~10 tasks are formal `∧ False` obligations now marked `in_progress`.

**The honest bridges proved so far** (task R-group, see task list):
- Flat GH limits (cycle→S¹, path, torus, lattice→Minkowski).
- Polynomial scaled-second-difference = f''.
- Forman-Ricci = 0 on cycle ≡ S¹ Ricci = 0.
- Schrödinger unitarity on Hypergraph V.
- Conservation ⇒ size invariance along trajectory (IR2).

**The real-work items tracked explicitly** (#176-#180, R1–R5):
- ✅ **R1**: C² Taylor convergence for scaled second difference (`CTwoTaylor.lean`). Unlocks all non-polynomial bridges.
- ✅ **R2**: `laplacianMatrix` + `heatKernel` via Matrix.exp (`LaplacianMatrix.lean`). Heat propagator as `exp(t · Δ)`, semigroup property, symmetry, row-sum zero, heat trace.
- 🔲 **R3**: ℓ²(BranchialSlice) Hilbert space + unitary branchial evolution (real QM bridge).
- 🔲 **R4**: Curved discrete-Ricci convergence (first non-flat case).
- ✅ **R5**: Cycle Laplacian spectrum closed form (`CycleSpectrum.lean`, full wrap-around).

**Follow-on bridges proved on top of R1/R2/R5** (this session):
- ✅ **A3/A4**: scaled cycle eigenvalue → continuum circle Laplacian spectrum (`CycleEigenLimit.lean`); hypergraph scaled Laplacian = scaled second difference (`ScaledDiffC2Bridge.lean`).
- ✅ **D3**: heat semigroup via `Matrix.exp` — now captured by `heatKernel_add`.
- ✅ Matrix eigenvalue equation packaging in `CycleMatrixSpectrum.lean`.

**Colleague-work items added** (#166-#175, M1–M10):
Ioana Milea (IG intern), Van Le (Fisher→FS), Hubert Kolcz (MBQC
Lie-Poisson), Jan Pullman (IBL-∞/BV), Zapata-Ahmed (axiomatic
relativity), Pokorny paclet parity, Ahmed EME-tracking, Pokorny
diffusion-geometry bridge, tropical geometry, 3BP dynamics.

## 9. Legacy phase groups (plan A/B/C/.../K)

| Group | Purpose | Done | Open |
|---|---|---|---|
| A | Calculus foundations | 4 (A1, A2, A3, A4) | 4 |
| B | Schwarzschild / curved metrics | 1 (B1) | 10 |
| C | Bundles + Levi-Civita | 0 | 8 |
| D | PDEs on Hypergraph V | 7 (D1,D3,D4,D5,D8,D9,D10) | 4 |
| E | Lorentzian manifolds | 0 | 7 |
| F | Einstein / stress-energy / energy conditions | 0 | 8 |
| G | Scalar fields / Lagrangian | 4 (G1,G3,G4, partial G2–G6) | 2 |
| H | BBH / numerical | 0 | 9 |
| I | Branchial / QM | 0 | 10 |
| J | Combined / emergent gravity / AdS/CFT | 0 | 6 |
| K | Paper drafts | 0 | 9 |
| X | Support (Taylor, multiway engine, etc.) | 0 | 4 |

## 10. GR target (the hard open)

- Formal obligations: `SchwarzschildObligationMet`, `KerrObligationMet`, `FLRWObligationMet` — all uninhabited.
- Schwarzschild Christoffels ✅ (all 8).
- Minkowski Einstein = 0 ✅.
- **Missing**: a concrete rule whose trajectory GH-converges to a curved spacetime. This is the open Wolfram-physics problem.
- Path forward: IR signature pipeline + IC causal axiomatics + B2–B4 Schwarzschild proof → then attempt to write a term of `SchwarzschildObligationMet`.

## 11. QM target

- Discrete side ✅: Schrödinger unitarity, self-adjoint `Δ_H`, conserved probability, ScalarField + KG.
- **Missing**: Fintype BranchialSlice (#84), ℓ²(slice) Hilbert space (#87), branchial unitary evolution (#88), Fubini–Study limit (#153), path integral (#155), continuum Hilbert limit (#91).

## 12. Axiom-cleanliness

Every single proved theorem above depends on axioms ⊆ `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no custom axioms. Verified by `AxiomCheck.lean` (100+ `#print axioms` lines).

## 13. What is NOT persisted

Anything absent from this file, `INFRAGEOMETRY.md`, `MILESTONES.md`, `PUBLISHABLE.md`, `STATUS.md`, the task system, or the Lean source is *ephemeral* and will not survive a session reset. Keep this file in sync.

## 14. Update protocol

- **On every Lean-file commit**: update §1–7 and §12 of this file, and add a row to the relevant table.
- **On every task completion**: update §8 / §9 counters.
- **On every new formal obligation**: add a row to §10 / §11 / `ContinuumLimitStatement.lean`.
- **On every session close**: verify nothing was only in-context.
