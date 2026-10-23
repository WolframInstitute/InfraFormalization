# Bridge machinery: hypergraph rewriting and continuum mathematics

This document lists the Lean infrastructure that relates the Wolfram-model side (hypergraphs, rewriting trajectories, causal graphs, branchial slices) to continuum mathematics (manifolds, differential operators, PDEs, fields, Lorentzian geometry). It is organised as a ladder of rungs. Each entry carries one of the status labels below.

Status labels:

- PROVED: a Lean theorem, kernel-checked, sorry-free, with axioms at most `propext`, `Classical.choice`, `Quot.sound`.
- PROVED-WITH-NATIVE-DECIDE: kernel-checked, depends on `native_decide`.
- VACUOUS: a Lean theorem that holds, but its statement does not relate the continuum object to any hypergraph data.
- DEFINED: a Lean definition with no theorem attached in this entry.
- OPEN: not established. The statement needed is given.

Per-theorem axiom lists are in [`THEOREM_STATUS.md`](THEOREM_STATUS.md). See [`ROADMAP.md`](ROADMAP.md) for sequencing.

## How continuum objects are tied to hypergraph data

The library uses two kinds of tie. They differ in content.

### Origin obligations (VACUOUS)

The origin obligations do not depend on their target argument and hold for every target:

- `HypergraphMetricOriginObligation target` and `HypergraphPartialMetricOriginObligation target` (`HypergraphMetricBridges.lean`) state that some rewriting system has a trajectory and that a positive sequence exists. They hold for every metric (`Curvature.any_metric_has_obligation_witness`, `Curvature.any_partialMetric_has_obligation_witness`).
- `HypergraphMetricOriginObligationWithRate target d` adds `WassersteinRateObligation d` for a caller-supplied sequence `d` that is not linked to the trajectory. The zero sequence satisfies it. `HypergraphMetricOriginObligationStrong` and its partial-metric form hold for every target (`Curvature.any_metric_has_strong_obligation_witness`, `Curvature.any_partialMetric_has_strong_obligation_witness`).
- `subdivisionDiscrepancy n = 1/2^n` (`WassersteinRate.lean`) is defined directly and is not computed from any measure. `subdivisionDiscrepancyBundle` proves that this sequence satisfies `WassersteinRateObligation` and tends to 0.
- `ConnectionDataOriginObligation C` (`FiberedGraphConnectionBridge.lean`) holds for every connection (`Curvature.any_connection_has_obligation_witness`). `LorentzianManifoldOriginObligation M` (`CausalLorentzianBridge.lean`) holds for every `DiagLorentzianManifold` (`Curvature.any_lorentzianManifold_has_obligation_witness`).
- `EFEOriginObligation M C Λ κ T x` (`EinsteinEquationsBridge.lean`) is the conjunction of `EinsteinEqLambda M C Λ κ T x` with the two obligations above. `Curvature.EFEOriginObligation_iff_EinsteinEqLambda` proves that it is equivalent to `EinsteinEqLambda M C Λ κ T x`.
- `HypergraphQuantumOriginObligationStrong` and `HypergraphBBHOriginObligationStrong` have the same form and hold for every target.

All theorems that inhabit these obligations are VACUOUS: they do not state convergence of any hypergraph data to any metric, connection, quantum system or black hole. This includes `minkowski4_from_hypergraph_proved`, `schwarzschild_from_hypergraph_proved`, `flrw_from_hypergraph_proved`, `sphere_from_hypergraph_proved`, `warpedDiag2_from_hypergraph_proved` (`RuleWitnesses.lean`, witness: `identitySystem Unit`, `cycleHypergraph n`, the zero-step `emptyTrajectory`), `minkowski4Manifold_from_causalGraph_proved`, `flatConnection_from_fiberedGraph_proved`, `minkowski4_flat_vacuum_EFE_originated`, `minkowski4_flat_vacuum_EFE_originated_global`, `schwarzschild_vacuum_EFE_origin_bundle_witnessed`, `Curvature.minkowski4_from_hypergraph_strong`, the `*_strong_from_exec_witness_*` theorems, the `WitnessDiversity.lean` cells, `GREmergence.zoo_strong_origin_obligations`, `GREmergence.minkowski4_quadDischarge_components`, `QMEmergence.quantum_strong_origin_obligations`, `QMEmergence.zoo_and_quantum_strong_origin_obligations`, `BBHEmergence.bbh_strong_origin_obligations` and `BBHEmergence.zoo_quantum_bbh_strong_origin_obligations`.

The Milestone layer (`Milestone.lean`) defines `DistConvergesTo`, `ConnectionConvergesTo`, `RiemannTensorConvergesTo`, `EinsteinFieldEquationsHold`, `DiscreteStressEnergyEmerges`, `BranchialHilbertConvergesTo`, `BranchialEvolutionConvergesTo`, `BornRuleEmerges`, `InitialDataMatches` and `Psi4Matches`. Each is satisfied by the zero discrepancy (`*_zero` theorems). `Milestone.GR_emerges_from_hypergraph_holds` proves `GR_emerges_from_hypergraph target` for every target, and `Milestone.QM_emerges_from_hypergraph_holds` and `Milestone.BBH_emerges_from_hypergraph_holds` prove the QM and BBH forms. Status: VACUOUS.

The same applies to the rate obligations for a caller-supplied sequence in `LorentzianGH.lean` (`lorentzianGHObligation_zero`), `CurvedRicciExtensions.lean` (`curvedDiscreteRicciObligation_zero`), `MeasureTorusLift.lean` (`multiDimRateObligation_zero`) and `ScaledConnectionLimit.lean`, where `connectionSup` is identically 0 and `scaledConnectionToLeviCivita_trivial` holds for every family. Status: VACUOUS.

### Continuum limits of fixed graph families (PROVED)

These theorems state a limit or an approximation bound for an explicit family of graphs indexed by `n`. None of them concerns a rewriting evolution.

| Family | Theorem | File | Statement |
|---|---|---|---|
| n-cycle, circle | `Infra.cycle_circle_gh_bound` | `Infra/GHBound.lean` | An isometric embedding of the cycle metric scaled by 1/n into ℝ/ℤ with 1/(2n)-dense image |
| n-cycle, circle | `Infra.cycle_circle_eventual_epsilon_dense` | `Infra/GHBound.lean` | For every ε > 0 the lattice image is ε-dense for large n |
| path, [0, 1] | `Infra.path_interval_gh_bound` | `Infra/ScaledPath.lean` | Isometric embedding with 1/(2n)-dense image |
| n×n lattice, 2-torus | `Infra.torus_gh_bound` | `Infra/ScaledTorus.lean` | Isometric embedding with 1/(2n)-dense image |
| (Fin n)^(d+1) lattice, (d+1)-torus | `Infra.dTorus_gh_bound` | `Infra/ScaledTorusD.lean` | Isometric embedding with 1/(2n)-dense image |
| integer Lorentz lattice, Minkowski space | `Infra.lorentzIntEmbed_preserves_causal_iff`, `Infra.scaledLorentzEmbed_preserves_causal_iff`, `Infra.scaledLorentzEmbed_dense` | `Infra/ScaledLorentz.lean` | The embedding preserves and reflects causal order; the 1/n-scaled lattice is dense |
| second difference | `scaledSecondDiff_tendsto_iteratedDeriv`, `scaledSecondDiff_tendsto_iteratedDeriv_C2` | `CTwoTaylor.lean`, `ScaledDiffC2Bridge.lean` | (f(x+h) − 2f(x) + f(x−h))/h² → f''(x) for C² f |
| path hypergraph Laplacian | `hypergraph_scaled_laplacian_eq_scaledSecondDiff` | `ScaledDiffC2Bridge.lean` | The scaled hypergraph Laplacian equals the scaled second difference at interior indices |
| cycle spectrum | `cycleEigenvalue_scaled_tendsto` | `CycleEigenLimit.lean` | n²·(−4 sin²(πk/n)) → −(2πk)² |
| cycle heat kernel | `discreteHeatToContinuumHeat` | `ContinuumLimitStatement.lean` | exp(t·n²·λ_k(n)) → exp(−(2πk)²t) for each mode k |
| wave, Schrödinger, Klein-Gordon dispersion | `pde_spectrum_bridge_summary`, `pde_spectrum_bridge_summary_with_mass` | `ContinuumBridgeDemo.lean` | The scaled lattice dispersion relations converge to the continuum ones mode by mode |
| lattice Riemann sums | `A6Holds_poly_deg3` | `ContinuumLimitStatement.lean` | (1/n)·Σ f(k/n) → ∫₀¹ f for polynomials of degree at most 3 |
| cycle, Wasserstein | `wasserstein1_cycleDelta_succ`, `wasserstein1_shiftIter_le` | `CycleWasserstein.lean` | W₁ between point masses one step apart on the scaled cycle is 1/n; a k-step shift costs at most k/n |
| cycle ball volume | `dimensionCompatibilityObligation_holds` | `RemainingObligations.lean` | V(v, r) = 2r + 1 on `cycleHypergraph n` for 2r + 1 ≤ n |

`Infra.causallyPrecedes_gives_continuum` (`Infra/FullBridge.lean`, PROVED) maps a trajectory's `causallyPrecedes` relation into Minkowski causal order under the hypothesis `LightConeCompatible τ φ` on a caller-supplied spatial embedding. It is not a limit theorem, and no theorem in the library shows that a rule's trajectory satisfies the hypothesis. `causallyPrecedes` relates events through hyperedge values; `CausalHistory.lean` defines the causal graph on hyperedge identities.

## Rung 1. Discrete calculus on graphs and hypergraphs

- PROVED: self-adjointness of the graph Laplacian, the Dirichlet form identity, positive semidefiniteness of −Δ and Σ Δf = 0 (`laplacian_self_adjoint`, `dirichlet_form`, `laplacian_neg_psd`, `laplacian_sum_zero`, `DiscreteCalculusSymm.lean`).
- PROVED: linearity, self-adjointness and the Dirichlet inequality for the hypergraph Laplacian `laplacianHyper` (`HypergraphLaplacian.lean`).
- PROVED: the matrix form `laplacianMatrix H` reproduces `laplacianHyper`, is symmetric, has zero row sums and kills constants; `heatKernel H t := exp(t · laplacianMatrix H)` satisfies `heatKernel_zero`, `heatKernel_add` and `heatTrace_zero` (`LaplacianMatrix.lean`).
- PROVED: hyperedge gradient and divergence with summation by parts (`hyperedgeGradient`, `hypergraphDiv`, `summation_by_parts`, `HypergraphCalculus.lean`).
- PROVED: `KnillCore.dSquared_eq_zero` (d ∘ d = 0 for the signed boundary on oriented simplices), `hodgeOnG_psd`, `wuCharacteristic₂_eq_chi_sq_sub_disjoint`, `eulerCharacteristic_eq_alt_sum_kSkeleton` (`KnillCore.lean`).
- PROVED: `cycleLaplacian` equals the second difference (`CycleGraph.lean`, `SecondDifference.lean`).

## Rung 2. Convergence of discrete operators

- PROVED: the second-difference, path-Laplacian, cycle-spectrum and dispersion limits in the table above.
- PROVED: the cycle eigenvalue equation `cycleLaplacian_eigen` (`CycleSpectrum.lean`), its matrix form `laplacianMatrix_cycleHypergraph_eigen` and Mathlib form `laplacianMatrix_cycleHypergraph_hasEigenvalue`, and `exp_mulVec_of_eigenvector`, `heatKernel_mulVec_const` (`ExpEigenvector.lean`).
- OPEN: uniform convergence on C^k compacts; scaled torus and lattice Laplacians converging to the Laplace-Beltrami operator of the torus.

## Rung 3. Measure-theoretic limits

- DEFINED: `countingMeasure H`, `uniformProbability H`, `pushforwardCounting`, `pushforwardUniform` (`HypergraphMeasure.lean`), with `countingMeasure_univ` and `uniformProbability_univ` PROVED.
- PROVED: a finite W₁ framework in `WassersteinFinite.lean`: `wasserstein1_delta_eq_dist`, `wasserstein1_symm`, `wasserstein1_self_eq_zero`, `wasserstein1_triangle`, and `wasserstein1_lipschitz_bound` (|E_μ f − E_ν f| ≤ L·W₁(μ, ν) for L-Lipschitz f).
- PROVED: the cycle W₁ results and the polynomial Riemann-sum limits in the table above.
- OPEN: `A6LatticeRiemannObligation` for every continuous f; a W₁ rate ≤ C/n between the scaled counting measure and Lebesgue measure; the lift to the (d+1)-torus; Gromov-Hausdorff-Prokhorov distance.

## Rung 4. Connections and parallel transport

- DEFINED: `DiagRiemannianMetric` with Euclidean witness `euclidean_diagRiemannian` (PROVED), `DiagLorentzianMetric` with Minkowski witness `minkowski4_diagLorentzian` (PROVED) (`RiemannianManifold.lean`, `LorentzianManifold.lean`).
- DEFINED: Christoffel symbols on `MetricData n` (`CurvatureLocalCoord.lean`) and `leviCivitaConnection` (`CurvatureRiemann.lean`). PROVED: `christoffel_symm`, `CurvatureRiemann.bianchi_first`.
- DEFINED: `HypergraphConnection H G` with `transportWalk`, `holonomy` and `IsFlat`; PROVED: `transportWalk_append` (`HypergraphConnection.lean`).
- OPEN: a covariant derivative on smooth sections, torsion, existence and uniqueness of Levi-Civita (Koszul formula), the tensor transformation law, and convergence of scaled discrete connections on lattice graphs to the Levi-Civita connection of the limit manifold.

## Rung 5. Riemann, Ricci, scalar curvature, Einstein tensor

- DEFINED: `MetricData n`, `ConnectionData n`, Riemann tensor, Ricci tensor, scalar curvature, Einstein tensor. PROVED: `riemann_antisymm`, `CurvatureRiemann.bianchi_first`, `minkowski4_satisfies_vacuum_EFE` (`CurvatureRiemann.lean`).
- PROVED: Schwarzschild Christoffel symbols on the exterior (`Schwarzschild.lean`), FLRW Christoffel symbols (`FLRW.lean`) and the FLRW Riemann and Ricci components (`FLRWRicci.lean`), Reissner-Nordström lapse identities (`ReissnerNordstrom.lean`).
- PROVED: `warpedDiag2_einstein`: the 2D metric `warpedDiag2_C2` satisfies R_{μν} = (−1/(1+x₀²)²)·g_{μν} (`WarpedDiag2C2.lean`).
- PROVED: Ricci symmetry for the flat connection and for the Levi-Civita connection of `warpedDiag2` (`RicciSymmetry.lean`).
- PROVED: `forman_ricci_matches_continuum_on_cycle` (`RicciBridge.lean`): on a 2-regular graph the Forman-Ricci edge curvature is 0, and the Ricci tensor of the flat connection on ℝ¹ is 0. The theorem states that both quantities vanish.
- OPEN: Schwarzschild Ricci = 0 and the vacuum Einstein equations for Schwarzschild; FLRW Einstein equations with a perfect-fluid stress-energy tensor; the second Bianchi identity ∇_μ G^{μν} = 0; Ricci symmetry for a general Levi-Civita connection; convergence of a discrete Ricci curvature to a non-zero continuum Ricci curvature.

## Rung 6. ODEs and PDEs on hypergraphs

- PROVED: discrete heat equation u' = Δ_H u: existence and forward uniqueness (`heat_exists_unique_forward`), mass conservation (`heat_mass_conservation`), L² decay (`heat_L2_decay`), identification with the heat kernel (`heatKernel_isHeatSolution`).
- PROVED: on cycles, non-constant eigenmodes decay to 0 and finite eigen-combinations converge to their constant component (`heatKernel_cycleHypergraph_multi_mode_tendsto`, `HeatKernelDecay.lean`). OPEN: the same for arbitrary initial data.
- PROVED: wave energy conservation (`wave_energy_conservation`), Klein-Gordon energy conservation (`klein_gordon_energy_conservation`), Schrödinger probability conservation (`schrodinger_unitary_evolution`).
- PROVED: the mode-by-mode heat-kernel limit `discreteHeatToContinuumHeat` on cycles.
- OPEN: the Cauchy problem for the Einstein equations.

## Rung 7. Fields and Lagrangians

- DEFINED: discrete scalar field, Lagrangian density and Hamiltonian (`ScalarField.lean`). PROVED: `discreteHamiltonian_eq_legendre`, `KG_EulerLagrange_iff_KleinGordonSolution`.
- PROVED: Klein-Gordon dispersion limit (`discreteKleinGordonSpectrum_holds`).
- OPEN: a discrete gauge field as a connection on a fibred graph, Yang-Mills continuum limits, integration with HepLean.

## Rung 8. Lorentzian geometry and causal structure

- PROVED: causal precedence on the cubic lattice with the timelike, null, spacelike trichotomy (`Infra/LorentzLattice.lean`), the same trichotomy in continuum Minkowski space (`Infra/Minkowski.lean`), and the lattice-to-continuum results in the table above.
- PROVED: `stablyCausal_hasFoliation` (`CausalFoliation.lean`).
- PROVED, under the hypothesis `LightConeCompatible`: `Infra.causallyPrecedes_gives_continuum`.
- OPEN: a general Lorentzian `MetricData`; strong causality and global hyperbolicity for continuum targets; Cauchy surfaces and the ADM decomposition; Lorentzian Gromov-Hausdorff distance; a convergence theorem from scaled causal graphs of rewriting evolutions to a Lorentzian manifold.

## Rung 9. Einstein's equations

- DEFINED: `EinsteinEqLambda` (`EinsteinEquations.lean`), `StressEnergyTensor` (`StressEnergyTensor.lean`).
- PROVED: `minkowski4_satisfies_EFE_zero_lambda`, `minkowski4_flat_vacuum_forces_lambda_zero`, `flatConnection_einstein_divergence_zero` (flat case).
- OPEN: energy conditions; Schwarzschild as a vacuum solution; FLRW with perfect-fluid stress-energy; a rule together with a convergence notion under which the rule's causal graph converges to a Lorentzian manifold satisfying the Einstein equations.

## Rung 10. Hypergraph to geometry bridges

- PROVED: the flat-target limits of fixed graph families in the table above (cycle, path, 2-torus, (d+1)-torus, Lorentz lattice).
- OPEN: a curved-target limit for any graph family; any continuum limit of a rewriting evolution; binary black hole evolution from a hypergraph.

## Branchial and quantum track

- DEFINED: `BranchialRelated`, `NStep`, `BranchialSlice` on the abstract `Step` relation (`Branchial.lean`); `BranchialHilbert S := EuclideanSpace ℂ S`, `bornProbability`, `BranchialObservable`, `expectationValue` (`BranchialHilbert.lean`).
- PROVED: finiteness lemmas for slices (`BranchialFinite.lean`); self-adjointness of the adjacency operator (`branchialAdjLM_inner`); probability conservation (`branchialSchrodinger_unitary_evolution`, `BranchialSchrodinger.lean`); `expectationValue_re_of_symm`, `expectationValue_eigenvector`.
- PROVED: `branchial_qm_is_rewriting_grounded` (`BranchialCanonical.lean`): the ℓ² space of a finite branchial slice of `(sys, s₀, n)` carries a self-adjoint observable built from the slice adjacency.
- PROVED: `fubiniStudyBhattacharyya_bound` (`RemainingObligations.lean`): |⟨ψ, φ⟩| ≤ Σ_s |ψ_s|·|φ_s| on `BranchialHilbert S`. The statement is the triangle inequality and contains no limit.
- OPEN: a continuum limit from branchial slices to a quantum-mechanical Hilbert space; a path-integral formulation.

The modules `BranchialEventTrace`, `BranchialDepthTrajectory`, `BranchialFromInteraction`, `BranchialRSpectrum` and `BranchialUniversalAdditivity` state their results with `MultiwayExec.fireAllStep`, which applies every match including matches that share edges. Their results do not describe Wolfram model evolutions. The "branchial" relation of `BranchialEventTrace` is same-step consumed-edge contention and differs from the Wolfram-model branchial graph.

## Lean files on G1-G4

`lean/InfraFormalization/Refutations/` accompanies the findings in [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md). F3 and F4 are PROVED by `Iff.rfl` about the project's encodings. F1, F2, F5 and F6 are VACUOUS with respect to the papers: they state facts about function types, `Bool`, the sequence 1/(n+1) and a restated hypothesis. F7 PROVES edge-count conservation for the rule of G3 line 6202. The findings about the papers are READ findings with line numbers.

## Summary

| Rung | PROVED | Tie to hypergraph data | OPEN |
|---|---|---|---|
| 1 | Laplacian identities, matrix form, heat kernel, hyperedge gradient and divergence, d² = 0 | Defined on `Hypergraph V` | none listed |
| 2 | Second difference, cycle spectrum and dispersion limits | Fixed families (cycle, path) | Torus Laplace-Beltrami, uniform convergence |
| 3 | Finite W₁ framework, cycle W₁ bounds, polynomial Riemann sums | Fixed families (cycle, lattice) | General weak convergence, W₁ rate, torus lift |
| 4 | Christoffel symmetry, Bianchi I, `transportWalk_append` | Origin obligation only (VACUOUS) | Levi-Civita existence, discrete connection limit |
| 5 | Flat EFE, Schwarzschild and FLRW Christoffels, FLRW Ricci, warpedDiag2 Einstein identity | Origin obligation only (VACUOUS) | Schwarzschild vacuum, discrete Ricci limit |
| 6 | Heat, wave, Klein-Gordon, Schrödinger on `Hypergraph V`; cycle heat-kernel limit | Defined on `Hypergraph V` | Einstein Cauchy problem |
| 7 | Discrete Euler-Lagrange, Klein-Gordon dispersion limit | Defined on `Hypergraph V` | Gauge fields |
| 8 | Lattice and Minkowski causal structure, lattice embedding | Fixed lattice family; trajectories under `LightConeCompatible` | Lorentzian GH, limit of rewriting causal graphs |
| 9 | Flat vacuum EFE | Origin obligation only (VACUOUS) | Curved solutions, rule producing EFE in a limit |
| 10 | Flat-target limits of fixed families | Fixed families | Curved targets, limits of rewriting evolutions |
| QM | Self-adjointness, probability conservation on finite slices | Defined on branchial slices | Continuum limit |

## Discrete d'Alembertian

`DiscreteDAlembertian.lean` formalises the Benincasa-Dowker-type operator on a trajectory causal DAG used in the §6 chain of G3: the causal interval size, the layers L_k, and `discreteDAlembertian4 τ φ i := −φ i + Σ L_0 φ − 9·Σ L_1 φ + 16·Σ L_2 φ − 8·Σ L_3 φ`. OPEN: the Benincasa-Dowker convergence statement.
