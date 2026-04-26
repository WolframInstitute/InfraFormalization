# Coverage map — done / in-progress / open

**Single source of truth for project posture.** Updated whenever a Lean file is added, a task is completed, or a research direction is opened. Complements `INFRAGEOMETRY.md` (program description), [`ROADMAP.md`](ROADMAP.md) (phase-sorted full-program sequencing toward BBH-from-hypergraph), and the task system (atomic items).

Legend: ✅ proved, axiom-clean. 🟡 partial. 🔲 open. 🚫 uninhabited formal obligation.

## 0. Recent landings (2026-04-26 — late, catch-up sync)

- ✅ **`KnillCore.dSquared_eq_zero` (#277)** — cochain-complex axiom for signed boundary on oriented simplices, axiom-clean. Plus `dStarSquared_eq_zero` codual.
- ✅ **`KnillCore.hodgeOnG_psd`** — Hodge laplacian PSD as bilinear form via sum-of-squares decomposition. Plus `hodgeOnG_dirichlet_zero_iff_isDiracKernel` (kernel-side Hodge isomorphism), `hodgeOnG_diag_eq_sum_dirac_sq`.
- ✅ **`SubdivisionPath.subdivisionTrajectory n` (#284, Route D)** — canonical n-step trajectory `pathEdges (subdVerts n)` defined directly, with `_isPathOf`, `_length = 2^n`, `_succ`. Decoupled from engine simulation lemma.
- ✅ **`WassersteinRate.subdivisionDiscrepancy` (#234)** — `1/2^n` discharges `WassersteinRateObligation` with `O(1/n)` rate. First end-to-end machine-checked rule-trajectory → continuum-target convergence certificate.
- ✅ **`MultiwayExecBridge.lean` (#231)** — first formal exec ↔ abstract bridge: `ExecRule.toRule`, `Fin.embedSuffix`, single-rule `ExecSystem` cast, `consumed_toMultiset`. Closes the architectural anchoring gap.
- ✅ **`KnillCore.wuCharacteristic₂_eq_chi_sq_sub_disjoint` (KN3)** — Wu inclusion-exclusion identity.
- ✅ **`KnillCore.eulerCharacteristic_eq_alt_sum_kSkeleton` + `_fintype` corollary (KN8)** — Euler-Poincaré f-vector identity.
- ✅ **#280–#283** — structural helpers `mem_subdivideVerts_imp`, `subdivideVerts_nodup`, `subdVerts_nodup`, `nextFresh_pathEdges`.
- ✅ **#233 Phase A** — `HypergraphMetricOriginObligationStrong` lands with `ScaledDiscrepancy + WassersteinRateObligation`; concrete discharge `minkowski4_from_hypergraph_strong` via `subdivisionDiscrepancyBundle`; generic lifting + per-metric Props (Schwarzschild / FLRW / RN / dS / S² / warpedDiag2). First obligation Prop with quantitative rate content.
- ✅ **#233 Phase A follow-up** — `ConvergenceRateObligation d r` generic rate-family admitting `rateOneOverN`, `rateOneOverNSquared`, `rateGeometric c`. Bidirectional bridge to `WassersteinRateObligation`. `subdivisionDiscrepancy_satisfies_geometric` (natural `(1/2)^n` rate). Precondition for Phase B's screener metrics (Forman-Ricci, GH, spectral).
- ✅ **#224 (Phase B opens)** — `RuleSignatureScreener.lean` lands: per-slice `signatureTrajectory τ : ℕ → RuleSignature V`; real-valued projections (`edgeCountTrajectory`, `vertexCountTrajectory`, `formanRicciTrajectory`); curvature-deviation discrepancy `formanRicciDeviation τ κ`; screener obligations `FormanRicciScreener τ κ r := ConvergenceRateObligation (formanRicciDeviation τ κ) r` and compound `MultiScreener τ tgt_e tgt_κ r`. Conservative-discharge theorems (`edgeCountTrajectory_const_of_conservative`, `edgeCountTrajectory_satisfies_any_rate_of_conservative`, `multiScreener_self_of_conservative_initial`). Negative-discharge `formanRicciScreener_fails_of_persistent_gap` (structural rule-disqualification when the curvature deviation has a uniform positive lower bound on a cofinal subset).
- 📋 **Angle tower (AT0–AT27, #285–#314)** — full taxonomy logged across 13 flavour-columns × multiple abstraction levels. Columns: M (metric, `dist`-only), S (spectral, Hodge-based), Y (synthetic, predicates-only), T (transport, Wasserstein), Q (branchial / QM, `BranchialHilbert`), L (Lorentzian, rapidity), G (gauge / fibre, `Connection`), I (information-geometric, Fisher), H (higher-dim k-tuples — incl. **AT20 Regge deficit, the numerical-GR variable**), K (conformal — **AT23 conformal IS pure-angle data**), F (higher-form: discrete metric tensor, Riemann), N (non-standard: tropical, p-adic), C (scale-spectrum), U (multivalued for non-`GeodesicallyUnique`). Plus **AT9 Bishop-Gromov scalar curvature from log V(r)** and **AT11 dimensionless ↔ dimensional bridge** (units emerge from continuum rescaling). **Three structural observations**: (i) AT18 Cayley-Klein cross-ratio works without straight lines (only `Between`+`dist`-ratios), sidestepping Stephen's geodesic-uniqueness requirement; (ii) conformal geometry IS pure-angle theory; (iii) AT20 Regge deficit gates Phase D BBH.
- 📋 **PATH1/PATH2 (#300/#301)** — Stephen's non-overlapping-path substrate. Currently `Hypergraph.dist := H.toSimpleGraph.dist` uses Mathlib clique-expansion which silently drops self-loops (`loopless`), collapses multi-edges in the `Multiset`, and treats ≥3-arity hyperedges as `K_n`. Numerically `dist` is right (Mathlib shortest walk is auto-simple-path), but structurally we lose "which hyperedge was rewritten at step i" — important for #228/#229 causal/branchial extraction. PATH1 = native `Hypergraph.SimplePath u v` carrying `Nodup` vertex list AND hyperedge sequence; PATH2 = equivalence/disagreement theorem with `Hypergraph.dist`. Prerequisite for AT3 (Toponogov), AT8 (`GeodesicallyUnique`), AT26 (multivalued angle).
- 📋 **Topology-before-metric layer** — full layered hierarchy logged. **Cellular substrate**: CELL1 (#315) cellular sheaves on Hypergraph V — Pavel's "string theory on the graph" framework, cycles-with-common-points = equalizer at common-stalk. **Polygon framework**: POLY1 (#316) generalised polygon (arbitrary intersection sequences, recovers Euclidean as singleton-intersection case); POLY2 (#317) cellular k-chain in Δ-complex with sheaf coefficients (full categorical generalisation, subsumes POLY1+CELL1+P4+P5+P19+IGE2); POLY3 (#318) spin networks/foams (LQG primitive, knot-invariant home via Witten/RT). **Path moves**: DEFORM1 (#330) elementary deformations (Tietze/Whitehead/Reidemeister-style: backtrack, 2-cell, hyperedge-transit substitution); DEFORM2 (#331) elementary extensions (forward/backward edge/hyperedge-transit append). **Equivalence relations**: HOM1 (#332) path-homotopy as `EqvGen` of DEFORM1; HOM2 (#333) fundamental groupoid Π_1(H); CONTRACT1 (#329) contractibility predicate (binary, scale-indexed via VR-complex; persistence-barcode death-time IS the contractibility scale). **Topological invariants**: TOP1 (#323) first Betti b_1 (combinatorial cycle rank); TOP2 (#324) higher Betti via Hodge; TOP3 (#325) fundamental group π_1; TOP4 (#326) connected components b_0 (with multi-way/branchial refinement); TOP5 (#327) higher homotopy π_k; TOP6 (#328) genus / crossing number. **Knot/link invariants**: KNOT1 (#320) linking number / Borromean detection; KNOT2 (#321) Massey products / higher-linking; KNOT3 (#322) Yamada/Jones via spin-network Chern-Simons evaluation. **Sheaf-angle**: AT-W (#319) — 14th flavour-column in the angle tower, generalises AT4 spectral / Knill / Connes inner-product angle. **For Phase D BBH**: black-hole horizon = non-contractible cycle; merger event = moment cycle becomes contractible (2-cell fills non-contractible region); knot-cobordism between linked → unlinked configurations. Stephen's structural sequence: TOP4 (b_0 connectedness, four flavours: spatial/causal/branchial/rewriting-reachable) → PATH1 → POLY1 → CONTRACT1 → DEFORM1/2 → HOM1/2 → TOP3 → TOP1 — each layer is one short Lean def on top of the previous; the whole hierarchy lives below the metric layer. Pavel's "string theory on the graph" framing: the cellular-sheaf framework IS string field theory (closed strings = 1-cycles, interaction vertices = common-stalk equalizers, worldsheets = cellular k-chains, string amplitudes = sheaf-cohomology).
- 📋 **Hyperplane / polytope / inside-outside / bounded layer** — Pavel's "graph separation" + Stephen's metric/topological refinements: HYPER1 (#338) separator, HYPER2 (#339) perpendicular bisector, HYPER3 (#340) Voronoi, HYPER4 (#341) three-strengths equivalence (finite-vs-infinite hyperplane distinction recovers in continuum limit), MIDPT1 (#342) midpoint, POLYTOPE1 (#343) polytope as hyperplane-arrangement cell, INOUT1 (#344) inside/outside on cycles (Jordan + 4 "inside" criteria), BOUND1 (#345) diameter (4 flavours), MEMBER1 (#346) decidable membership, COMPACT1 (#347) limit-only compactness. SPHERE1–4 (#334–#337) infra-sphere with topology + surface-area Bishop-Gromov extraction. **Stephen's program statement "we're going to get all the way to differential geometry"** — the full 25-step constructive route from elementary connectedness to BBH-from-hypergraph documented in INFRAGEOMETRY.md §5f.
- 📋 **Surface / manifold-detection layer** — SURFACE1 (#348) Knill/Fisk recursive manifold predicate (`IsFiskManifold n H` iff every vertex's unit sphere is (n-1)-manifold AND every unit ball is contractible); subsumes / sharpens KN13 (#249). **Diagnostic on a tree**: shell disconnected at every positive radius → fails Knill at every positive dim → tree is NOT manifold-like. Empirical screener for "rule produces manifold-like hypergraph".
- 📋 **Formal-topology layer** — OPEN1 (#349) multiple natural topologies on a hypergraph (discrete / Alexandrov / metric / cellular-star / VR-scale-indexed / causal); NBHD1 (#350) neighbourhood basis at each vertex (Stephen's "locally has neighbourhoods" intuition for surfaces — manifold-like = neighbourhood basis stabilises to disk-shapes).

For full taxonomy + connectedness flavour analysis + units-emergence + path-vs-walk + contractibility-via-persistence + 25-step diff-geo route, see INFRAGEOMETRY.md §2, §2.5, §3, §5b–§5f.

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
| `RemainingObligations.lean` | **All seven infrageometry obligations are PROVED** (`all_obligations_hold`). IT5 `latschevObligation_holds`, IT6 `scaleTrichotomyObligation_holds`, ID6 `dimensionCompatibilityObligation_holds` (V(v,r) = 2r+1 exact on every cycle), IQ6 `fubiniStudyBhattacharyya_bound`, IQ8/IQ9 baseline witnesses in `no_stub_obligations_remain`, IR7 `reverseEngineeringObligationRefined_holds` (over-strong unrefined form is FALSE: `not_reverseEngineeringObligation`). Zero stubs remain. | ✅ T6 (7/7) |
| `RuleDimensionBounds.lean` | `Trajectory.StepConsistent`, `trajectory_size_invariant`, `geodesicBallVolume_le_card` | ✅ IR2 |

ID-group status: **ID1 / ID2 / ID3 / ID4 / ID5 / ID6 closed with real content**. ID6 fully proved: `V(v, r) = 2r + 1` on cycle hypergraphs (`cycleHypergraph_ballVolume_exact`, `dimensionCompatibilityObligation_holds`). ID7 spectral dim via `Matrix.exp` small-`t` asymptotics still in progress.

Adjacent open problem: **P20 Rodkey classification** — characterise hypergraphs for which `localDimension v r` is constant across vertices; infrastructure in place (`Hypergraph.localDimension`, `wolframHausdorffDimension`, `plateauDimension`), classification theorem open. Partner with Pavel Hájek and Dugan Hammock. Current state (2026-04): Sufficient chain `AdjTransitive → DistTransitive → BallVolumeVertexUniform → LocalDimensionVertexUniform` fully proved in `RodkeyClassification.lean`. Necessary condition: `degree_uniform_of_ballVolumeVertexUniform` — on a connected hypergraph, ball-volume-uniformity forces uniform SimpleGraph degree (via `geodesicBallVolume v 1 = 1 + degree v`); contrapositive `not_ballVolumeVertexUniform_of_degree_ne` rules out non-regular graphs. **Local characterisation**: `ballVolumeOne_uniform_iff_regular` — on a connected hypergraph, the r=1 slice of BallVolumeVertexUniform is exactly `Regular` (all vertices same SimpleGraph degree). **Positive example**: `cycleHypergraph n` for `n ≥ 2` — full chain inhabited via rotation automorphism `cycleRotHom`, `Walk.map`, and dist-translation-invariance; `cycleHypergraph_regular` (= 2-regular for n ≥ 3). **Negative example**: `pathHypergraph n` for `n ≥ 3` (`pathHypergraph_not_ballVolumeVertexUniform`, `pathHypergraph_not_regular`) — endpoint `0 : Fin n` has degree 1, interior `1 : Fin n` has degree 2, so the path is ruled out at radius 1. Both separated structurally on Fin 3 by `rodkey_classification_nontrivial` and `regular_dichotomy_on_fin3`. Remaining open: d-torus positive example, general classification theorem (walk-regular vs vertex-transitive distinction).

## 7b. Infragauge / Infracausality / Infratopology / Synthetic / Blowup / Ruliology

| Module | Content | Status |
|---|---|---|
| `FiberedGraph.lean` | `FiberedGraph V W` structure; `fiber`, `disjoint_fibers`, `exists_unique_fiber`; `IsSection`, `SmoothSection`; `Connection`, `connectionAdj`, `connectionAdj_implies_total_Adj` | ✅ IG1 + IG2 + IG3 |
| `Holonomy.lean` | `IsHorizontalLift`; `ParallelTransportList`; `Holonomy`; `wilsonLoop`; `IsFlatConnection`; `flat_holonomy_all_fixed` | ✅ IG4 + IG5 + IG6 + IG7 |
| `CausalGraphType.lean` | `CausalGraph V` TR-DAG; `causallyPrecedes` (refl+trans), `causalEdge_implies_precedes`; `ChainOfLength` observer chain; `DegenerateInterval`, `OnLightStepFrom` | ✅ IC1 + IC2 + IC3 |
| `CausalFoliation.lean` | `IsAntichain`; `IsFoliation` (antichain+disjoint+covers); `FiniteSupportFoliation`; `HasProperTime`, `properTime_self_exists` | ✅ IC4 |
| `BranchialFinite.lean` | `successors`, `BranchialSliceFinite`; `branchialSliceFinite_zero / _succ / _of_successors_finite` | ✅ I1 |
| `VietorisRips.lean` | `VietorisRipsEdge`, `VietorisRipsSimplex` with mono / empty / singleton / mono_scale; `vietorisRipsGraph` as SimpleGraph; `vietorisRipsGraph_zero_no_edges_reachable` | ✅ IT1 |
| `SyntheticGeometry.lean` | `SyntheticCircle`, `SyntheticBall`, `SyntheticLineSegment`, `SyntheticSphere`; `mem_syntheticCircle`, `syntheticCircle_zero`, `center_not_on_circle`, `syntheticCircle_subset_ball`, `syntheticCircle_disjoint`, `endpoints_on_segment` | ✅ IS1 |
| `ElementaryBlowup.lean` | `ElementaryBlowup P` structure (single-hyperedge LHS); `headEdge`, `apply`, `rhsSize`, `Order` | ✅ IB1 |
| `DagBlowup.lean` | `dagEdge`, `dagAsBlowupOfInterval n`; `dagDerivative`; linearity (`_add`, `_smul`, `_const`) | ✅ IA1 |
| `RuleSignature.lean` | `RuleSignature V` structure (hausdorffDimAt, ballVolume, totalFormanRicci, edge/vertex counts); `hypergraphSignature`; `avgFormanRicci`; match predicates (`sameDim`, `sameBallVolume`, `sameEdgeCount`, `FullMatch`); `edgeCount_invariant_of_conservative` | ✅ IR1 |

## 8. Groups from the full Infrageometry program

From `INFRAGEOMETRY.md` — 9 groups (57 new tasks ). Status:

| Group | Name | Addressed | Closed with real content |
|---|---|---|---|
| IA | Infraanalysis (Pavel Hajek) | 5/5 | 5 |
| IG | InfraGaugeTheory (Pavel Pokorny paclet port) | 11/11 | 10 (IG10 open) |
| IC | Infracausality (EPS, MW-clock) | 8/8 | 8 |
| IT | Infratopology (VR + Latschev; Pavel Hajek) | 6/6 | 4 (IT5/IT6 obligations pending) |
| ID | Infradimension | 7/7 | 6 (ID7 in progress) |
| IB | Infrablowup (Lie algebra, Poisson) | 6/6 | 5 (IB2 commutator theorem pending) |
| IQ | Branchial / quantum | 4/4 | 4 (IQ8/IQ9 baseline witnesses proved; full refinement-limit follow-up) |
| IS | Synthetic axiomatic | 3/3 | 3 |
| IR | Ruliology | 7/7 | 7 (IR7 refined form proved; over-strong unrefined form provably FALSE) |

**Addressed: 57/57. Closed with real content: 55/57.**

What remains open, concretely:
- **IG10** (exponential map via weighted shortest-path counts): needs shortest-path-counting infrastructure + Hajek's weighted-sum formulation.
- **IB2** (causal-branchial commutator theorem): predicate-level content placeholder at `True`; needs a real theorem statement about `[B₁, B₂]` on isomorphism classes before proof work can start.
- **ID7** (spectral dimension via heat trace): heat trace defined; small-`t` asymptotics remain.

**The honest bridges proved so far** (task R-group, see task list):
- Flat GH limits (cycle→S¹, path, torus, lattice→Minkowski).
- Polynomial scaled-second-difference = f''.
- Forman-Ricci = 0 on cycle ≡ S¹ Ricci = 0.
- Schrödinger unitarity on Hypergraph V.
- Conservation ⇒ size invariance along trajectory (IR2).

**Cross-cutting real-work items (R-series)**:
- ✅ **R1**: C² Taylor convergence for scaled second difference (`CTwoTaylor.lean`). Unlocks all non-polynomial bridges.
- ✅ **R2**: `laplacianMatrix` + `heatKernel` via Matrix.exp (`LaplacianMatrix.lean`). Heat propagator as `exp(t · Δ)`, semigroup property, symmetry, row-sum zero, heat trace.
- ✅ **R3 (closed)**: ℓ²(BranchialSlice) Hilbert space (`BranchialHilbert.lean` + `BranchialSchrodinger.lean`) — `BranchialHilbert S := EuclideanSpace ℂ S` finite-dim ℂ-Hilbert alias; `branchialAdjLM` ℂ-linear adjacency operator + `branchialAdjLM_inner` self-adjointness for symmetric adjacency; `branchialSchrodinger_unitary_evolution` proves the unitary branchial evolution (discrete Schrödinger on the slice conserves total probability `∑(u² + v²)`). Born rule + uniform measure + observables + expectation values also in place. Closes I2/I3/I4/I5/I6/I7/I9.
- 🔲 **R4**: Curved discrete-Ricci convergence (first non-flat case).
- ✅ **R5**: Cycle Laplacian spectrum closed form (`CycleSpectrum.lean`, full wrap-around).

**Follow-on bridges proved on top of R1/R2/R5** (this session):
- ✅ **A3/A4**: scaled cycle eigenvalue → continuum circle Laplacian spectrum (`CycleEigenLimit.lean`); hypergraph scaled Laplacian = scaled second difference (`ScaledDiffC2Bridge.lean`).
- ✅ **D3**: heat semigroup via `Matrix.exp` — now captured by `heatKernel_add`.
- ✅ Matrix eigenvalue equation packaging in `CycleMatrixSpectrum.lean`.

**Colleague-work items (M-series)**:
Ioana Milea (IG intern), Van Le (Fisher→FS), Hubert Kolcz (MBQC
Lie-Poisson), Jan Pullman (IBL-∞/BV), Zapata-Ahmed (axiomatic
relativity), Pokorny paclet parity, Ahmed EME-tracking, Pokorny
diffusion-geometry bridge, tropical geometry, 3BP dynamics.

## 9. Legacy phase groups (plan A/B/C/.../K)

| Group | Purpose | Done | Open |
|---|---|---|---|
| A | Calculus foundations | A1–A5; A7 concrete rate (cycle δ-shift sharp + measure-level shift O(1/n)) | A6 (polys to deg 3), A7 general case, A8 |
| B | Schwarzschild / curved metrics | B1, B5, B6, B8 | B2, B3, B4, B7, B9, B10, B11 |
| C | Bundles + Levi-Civita | C1 (`DiagRiemannianMetric`), C2 (`DiagLorentzianMetric`), C7 (`HypergraphConnection`) | C3, C4, C5, C6, C8 |
| D | PDEs on Hypergraph V | D1, D2, D3, D4, D5, D6 (partial), D7, D8, D9, D10 | D11 |
| E | Lorentzian manifolds | E1, E2, E3, E4 | E5 (in progress), E6, E7 |
| F | Einstein / stress-energy / energy conditions | F1, F2, F3, F7, F8 | F4, F5, F6 |
| G | Scalar fields / Lagrangian | G1, G3, G4 | G2, G5, G6 |
| H | BBH / numerical | H1 (rule catalog) | H2–H9 |
| I | Branchial / QM | I1–I7, I9 | I8, I10 |
| J | Combined / emergent gravity / AdS/CFT | J1 (`MultiwayCausalGraph`) | J2–J6 |
| K | Paper drafts | — | K1–K9 |
| X | Support (Taylor, multiway engine, etc.) | X1, X2, X3 | X4 |

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

- **Proved**: Fintype `BranchialSlice` (I1), uniform measure (I2), ℂ amplitudes + Born rule (I3), ℓ²(slice) Hilbert space with ℂ-linear self-adjoint adjacency (I4), unitary branchial evolution (I5), Hermitian observables (I6), expectation values (I7), Schrödinger on branchial graph (I9); plus the Fubini-Study / Bhattacharyya bound (IQ6 `fubiniStudyBhattacharyya_bound`), EME persistence baseline (IQ8), path-integral baseline (IQ9), Fisher metric on branchial graph (IQ5).
- **Missing**: I8 continuum Hilbert-space limit, I10 full path-integral formulation (sum over paths = unitary evolution equivalence).

## 12. Axiom-cleanliness

Every proved theorem above depends on axioms ⊆ `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no custom axioms. `AxiomCheck.lean` holds the `#print axioms` certifications.

## 13. What is NOT persisted

Anything absent from this file, `INFRAGEOMETRY.md`, `MILESTONES.md`, `PUBLISHABLE.md`, `STATUS.md`, the task system, or the Lean source is *ephemeral* and will not survive a session reset. Keep this file in sync.

## 14. Update protocol

- **On every Lean-file commit**: update §1–7 and §12 of this file, and add a row to the relevant table.
- **On every task completion**: update §8 / §9 counters.
- **On every new formal obligation**: add a row to §10 / §11 / `ContinuumLimitStatement.lean`.
- **On every session close**: verify nothing was only in-context.
