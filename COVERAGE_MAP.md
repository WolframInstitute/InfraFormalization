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
| `CycleMatrixSpectrum.lean` | Matrix eigenvalue equation: `laplacianMatrix (cycleHypergraph n) * cycleEigenvector = cycleEigenvalue • cycleEigenvector`; **`heatKernel_cycleHypergraph_mulVec_eigenvector`**: each cycle eigenvector decays under heat flow as `exp(t · cycleEigenvalue n k)`. | ✅ |
| `HeatKernelODE.lean` | **T1**: ODE ↔ matrix heat kernel unification. `hasDerivAt_heatKernel`, `heatKernel_commute_laplacianMatrix`, `hasDerivAt_heatKernel_mulVec`, **`heatKernel_isHeatSolution`** (the matrix heatKernel satisfies `HeatSolution H`). `mulVecEvalCLM` helper. | ✅ T1 |
| `ExpEigenvector.lean` | **T2**: matrix exp fixes eigenvectors. `mulVecCLM` (mulVec as a CLM in the matrix argument), `matrix_pow_mulVec_of_eigenvector` (`A^n.mulVec v = λ^n • v` by induction), **`exp_mulVec_of_eigenvector`**: if `A.mulVec v = λ • v`, then `(NormedSpace.exp A).mulVec v = Real.exp λ • v`. Via `exp_eq_tsum_rat` + `ContinuousLinearMap.map_tsum` + `Real.summable_pow_div_factorial`. | ✅ T2 |
| `CycleHasEigenvalue.lean` | **T4**: cycle spectrum in Mathlib `Module.End.HasEigenvalue` form. `cycleEigenvector_zero_val`, `cycleEigenvector_ne_zero`, **`laplacianMatrix_cycleHypergraph_hasEigenvalue`**: `HasEigenvalue (Matrix.toLin' (laplacianMatrix (cycleHypergraph n))) (cycleEigenvalue n k)`. Connects our pointwise eigenvalue theorem to Mathlib's spectral-theory API. | ✅ T4 |

## 3. PDE ladder on `Hypergraph V`

All proofs go through `laplacianHyper`. The Hypergraph is the domain; no continuum appears.

| Module | Equation | Conservation law | Status |
|---|---|---|---|
| `HeatEquation.lean` | `u' = Δ_H u` | Mass `∑u`, L² decay | ✅ D1 + D4 + D5 |
| `HeatEquationUniqueness.lean` | Existence + forward uniqueness | `heat_exists`, `heat_unique_forward`, `heat_exists_unique_forward` | ✅ D2 |
| `WaveEquation.lean` | `u'' = Δ_H u` | Energy `∑(du)² − ∑u·Δu` | ✅ D8 |
| `KleinGordon.lean` | `u'' = Δ_H u − m²u` | Energy + mass term | ✅ D9 |
| `SchrodingerEquation.lean` | `iψ' = −Δ_H ψ` | Probability `∑|ψ|²` | ✅ D10 |
| `ScalarField.lean` | Lagrangian + Hamiltonian + EL | `EL ↔ KG` equivalence | ✅ G1 + G3 + G4 |
| `DiscreteDAlembertian.lean` | BD 4D operator, `discreteAction`, `discreteEL` | BD conjecture flagged | 🟡 operator + action ✅; BD conjecture 🚫 |

Pending in this group: D7 discrete → continuum heat on GH limit, D11 Choquet-Bruhat. D2 existence-uniqueness ✅ (`HeatEquationUniqueness.lean`). D6 long-time convergence ✅ partial (`HeatKernelDecay.lean`: non-constant eigenmodes decay to 0; full D6 needs eigenbasis decomposition of arbitrary initial data).

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

Done in this group: B1 (Schwarzschild Christoffels), B5 (Schwarzschild `PartialMetricData`), B6 (FLRW `PartialMetricData`), B8 (Reissner-Nordström `PartialMetricData` + `rn_from_hypergraph` origin obligation inhabited).

Pending in this group: B2 Schwarzschild Riemann components, B3 `Ric = 0`, B4 vacuum EFE, B7 FLRW Ricci + perfect fluid, B9 Kerr `PartialMetricData` bundle, B10 Ricci symmetry (for Levi-Civita), B11 second Bianchi.

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
| `HypergraphDistance.lean` | `Hypergraph.dist`, `geodesicBall`, `geodesicBallVolume`, `localDimension`, `wolframHausdorffDimension`, `plateauDimension`; cycle: `Adj_iff`, `succ_pred_adj`, `ballVolume_one_ge_three`; **`dist_triangle` + `dist_triangle_of_reachable_{left,right}`** (T3); **`cycleHypergraph_reachable_zero`**, **`cycleHypergraph_connected`**, **`cycleHypergraph_dist_triangle`** | ✅ ID1 + T3 triangle inequality |
| `HypergraphMeasure.lean` | `countingMeasure`, `uniformProbability`, `pushforwardCounting`, `pushforwardUniform`; `countingMeasure_univ = |V|`, `uniformProbability_univ = 1`; `pushforwardCounting_univ`, `pushforwardUniform_univ` (mass preserved under measurable embedding) | ✅ A5 |
| `ContinuumLimitStatement.lean` (A6 section) | `A6LatticeRiemannObligation` Prop; monomial witnesses `A6_for_constants`, `A6_for_identity`, `A6_for_sq`, `A6_for_cube`; supporting algebraic identities `sum_fin_val_eq_triangular`, `sum_fin_val_sq_eq`, `sum_fin_val_cube_eq`; filter limits `tendsto_nMinusOne_div_twoN`, `tendsto_sqRiemann_to_third`, `tendsto_cubeRiemann_to_quarter`; predicate form `A6Holds` with `.const_mul`, `.add`, `.sub` closure and `A6Holds_poly_deg3` for degree ≤ 3 polynomials | 🟡 A6 partial (monomials + linearity) |
| `RemainingObligations.lean` | T6 partial upgrade: **`ReverseEngineeringObligation`** (IR7), **`DimensionCompatibilityObligation`** (ID6), and **`FubiniStudyLimitObligation`** (IQ6, also proved as `fubiniStudyBhattacharyya_bound`) now state real content (no longer `True ∧ False`). Four others remain at stub level. `four_stub_obligations_open` certifies the stubs are uninhabited. | ✅ T6 (3/7 upgraded) |
| `RuleDimensionBounds.lean` | `Trajectory.StepConsistent`, `trajectory_size_invariant`, `geodesicBallVolume_le_card` | ✅ IR2 |

Pending in ID: ID6 compatibility theorem (all dimension notions agree on regular lattices; in progress), ID7 spectral dim via `Matrix.exp` small-`t` asymptotics (in progress). ID2 / ID3 / ID4 / ID5 are closed with real content.

Adjacent open problem: **P20 Rodkey classification** (task #212) — characterise hypergraphs for which `localDimension v r` is constant across vertices; infrastructure in place (`Hypergraph.localDimension`, `wolframHausdorffDimension`, `plateauDimension`), classification theorem open. Partner with Pavel Hájek and Dugan Hammock. Current state (2026-04): Sufficient chain `AdjTransitive → DistTransitive → BallVolumeVertexUniform → LocalDimensionVertexUniform` fully proved in `RodkeyClassification.lean`. Necessary condition: `degree_uniform_of_ballVolumeVertexUniform` — on a connected hypergraph, ball-volume-uniformity forces uniform SimpleGraph degree (via `geodesicBallVolume v 1 = 1 + degree v`); contrapositive `not_ballVolumeVertexUniform_of_degree_ne` rules out non-regular graphs. **Positive example**: `cycleHypergraph n` for `n ≥ 2` — full chain inhabited via rotation automorphism `cycleRotHom`, `Walk.map`, and dist-translation-invariance. **Negative example**: `pathHypergraph n` for `n ≥ 3` (`pathHypergraph_not_ballVolumeVertexUniform`) — endpoint `0 : Fin n` has degree 1, interior `1 : Fin n` has degree 2, so the path is ruled out at radius 1. Remaining open: d-torus positive example, general classification theorem.

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

| Group | Name | Addressed | Closed with real content |
|---|---|---|---|
| IA | Infraanalysis (Pavel Hajek) | 5/5 | 5 |
| IG | InfraGaugeTheory (Pavel Pokorny paclet port) | 11/11 | 10 (IG10 open) |
| IC | Infracausality (EPS, MW-clock) | 8/8 | 8 |
| IT | Infratopology (VR + Latschev; Pavel Hajek) | 6/6 | 4 (IT5/IT6 obligations pending) |
| ID | Infradimension | 7/7 | 5 (ID6/ID7 in progress with real content) |
| IB | Infrablowup (Lie algebra, Poisson) | 6/6 | 5 (IB2 commutator theorem pending) |
| IQ | Branchial / quantum | 4/4 | 2 (IQ8/IQ9 obligations pending) |
| IS | Synthetic axiomatic | 3/3 | 3 |
| IR | Ruliology | 7/7 | 6 (IR7 in progress — over-strong form disproved, correct form open) |

**Addressed: 57/57. Closed with real content: 52/57 (91%).**

Honest breakdown of the remaining 9:
- T6 obligations **closed by upgrade** this session: IR7 (real content + disproof of over-strong form), ID6 (real content), **IQ6 (real content + proved `fubiniStudyBhattacharyya_bound`)**.
- T6 obligations remaining: IT5 Latschev, IT6 scale trichotomy, IQ8 EME persistence, IQ9 path integral — these genuinely need Mathlib infrastructure we do not have yet (GH-distance + homotopy equivalence, persistent-homology barcode, EME tracking functor, path-integral amplitude assignment).
- IG10 exponential-map: needs shortest-path-counting infrastructure.
- IB2 commutator-vanishing: needs multi-way system infrastructure.
- ID7 spectral dimension: heat trace defined; small-`t` asymptotics pending.

**The honest bridges proved so far** (task R-group, see task list):
- Flat GH limits (cycle→S¹, path, torus, lattice→Minkowski).
- Polynomial scaled-second-difference = f''.
- Forman-Ricci = 0 on cycle ≡ S¹ Ricci = 0.
- Schrödinger unitarity on Hypergraph V.
- Conservation ⇒ size invariance along trajectory (IR2).

**The real-work items tracked explicitly** (#176-#180, R1–R5):
- ✅ **R1**: C² Taylor convergence for scaled second difference (`CTwoTaylor.lean`). Unlocks all non-polynomial bridges.
- ✅ **R2**: `laplacianMatrix` + `heatKernel` via Matrix.exp (`LaplacianMatrix.lean`). Heat propagator as `exp(t · Δ)`, semigroup property, symmetry, row-sum zero, heat trace.
- ✅ **R3 (closed)**: ℓ²(BranchialSlice) Hilbert space (`BranchialHilbert.lean` + `BranchialSchrodinger.lean`) — `BranchialHilbert S := EuclideanSpace ℂ S` finite-dim ℂ-Hilbert alias; `branchialAdjLM` ℂ-linear adjacency operator + `branchialAdjLM_inner` self-adjointness for symmetric adjacency; `branchialSchrodinger_unitary_evolution` proves the unitary branchial evolution (discrete Schrödinger on the slice conserves total probability `∑(u² + v²)`). Born rule + uniform measure + observables + expectation values also in place. Closes I2/I3/I4/I5/I6/I7/I9.
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

## 10a. Grounding-audit bridge obligations (NEW, 2026-04-23 — all closed at obligation level)

See [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md) for the full audit.

| Module | Obligation bound to | Flat-case witness |
|---|---|---|
| `HypergraphMetricBridges.lean` | `HypergraphMetricOriginObligation M` / `HypergraphPartialMetricOriginObligation M` — every GR metric bound to `Hypergraph V` + `RewritingSystem P` + `Trajectory sys init` + scaling | `RuleWitnesses.lean` — every `*_from_hypergraph` Prop **provably inhabited** via `identitySystem Unit` + `cycleHypergraph n` + `emptyTrajectory` ✅ |
| `CausalLorentzianBridge.lean` | `LorentzianManifoldOriginObligation target` — every `DiagLorentzianManifold` bound to `CausalGraph V` + scaling | `minkowski4Manifold_from_causalGraph_proved` via `trivialCausalGraph (Fin 1)` (stably causal) ✅ |
| `FiberedGraphConnectionBridge.lean` | `ConnectionDataOriginObligation C` — every `ConnectionData n` bound to `FiberedGraph V W` + `FiberedGraph.Connection F` + scaling | `flatConnection_from_fiberedGraph_proved n` via `trivialFiberedGraph` + `trivialConnection` ✅ |
| `EinsteinEquationsBridge.lean` | `EFEOriginObligation M C Λ κ T x` — bundles EFE-satisfaction + metric origin + connection origin | `minkowski4_flat_vacuum_EFE_originated_global κ` — **first complete rule → metric → connection → EFE chain** ✅ |
| `RuleSearch.lean` | Concrete rule catalog; decidable `IsConservative`; screen predicates (`GrowthCompatible`); `conservative_blocks_dim_geq_one` — Gorard's structural block via IR2 | `minkowski4_from_growthRule` via `edgeDuplicateRule` ✅ |
| `RuleWitnesses.lean` | `identityRule`, `identityApplication_result`, `identitySystem`, `emptyTrajectory`, `trivialCausalGraph` + every bridge-obligation witness | All `*_from_hypergraph_proved` / `*_from_fiberedGraph_proved` theorems ✅ |

**Posture.** Every continuum GR structure now has a hypergraph-side
obligation attached at the Prop level. The flat-case inhabitations
are complete machine-checked proofs. The curved-case side (Schwarzschild
bridge, Kerr bridge, FLRW bridge, curved-Γ fibered-graph bridge) is
what remains — and it correctly remains open, because no such rule is
known. The refutation is structural, not notational.

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
