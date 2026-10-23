# Coverage map

This file lists the Lean modules of `InfraFormalization` by topic, with the status of what each module proves. [`INDEX.md`](INDEX.md) gives a longer entry per module, [`THEOREM_STATUS.md`](THEOREM_STATUS.md) gives the status of each cited theorem, and [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) and [`ROADMAP.md`](ROADMAP.md) describe the planned work.

Status labels:

- PROVED: kernel-checked, sorry-free, axioms at most `propext`, `Classical.choice`, `Quot.sound`.
- PROVED-WITH-NATIVE-DECIDE: the proof uses `native_decide`. These results are values computed for specific rules, seeds and depths.
- VACUOUS: the statement holds for every target, because a definition in it does not depend on the target.
- DEFINITIONS: the module defines objects and proves no theorem about them beyond basic lemmas.
- OPEN: stated, not proved. The statement is given.

## 1. Rewriting substrate

| Module | Content | Status |
|---|---|---|
| `Hypergraph.lean` | `Hypergraph V`, `Hyperedge`, `size`, size lemmas | PROVED |
| `Rule.lean` | `Rule P`, `IsConservative` | DEFINITIONS |
| `Application.lean` | `Application r H`, `result` | DEFINITIONS |
| `Conservation.lean` | A conservative rule application preserves size (`Application.size_result_of_conservative`) | PROVED |
| `Multiway.lean` | `RewritingSystem`, `Step`, `MultiStep`, confluence | DEFINITIONS |
| `Causal.lean` | `Trajectory`, causal precedence between applications | DEFINITIONS |
| `CausalLevel.lean` | Level function, `no_causal_edge_within_level`, `same_level_ordered_antichain` | PROVED |
| `Branchial.lean` | `BranchialRelated` on states of a multiway system, `NStep`, `BranchialSlice` | PROVED |
| `ParallelSchedule.lean` | In-degree and out-degree of applications of conservative rules | PROVED |
| `Demo.lean` | `edge_conservation`, a restatement of conservation | PROVED |
| `CausalHistory.lean` | Evolutions with hyperedge identities and their causal graph, for every update order. `consumer_unique`, `succ_card_le`, antichain bound `k·\|A\| ≤ N` for `\|LHS\| = \|RHS\| = k`, cone bound `(\|RHS\| + 1)^t`. For the G3 rule: `gorardNamedRule_antichain_card_le` (`4·\|A\| ≤ N`) and `gorardNamedRule_ball_card_le` (`5^t`). | PROVED. OPEN: linear cone growth, `GorardNamedRuleConeGrowthLinear` |
| `Growth.lean` | Ball and cone counts, `growthExponentAtMost_of_linear`. No cone bound for any rule. | PROVED |
| `RuleDimensionBounds.lean` | `trajectory_size_invariant`, `geodesicBallVolume_le_card`. No dimension bound. | PROVED |

## 2. Executable rewriting

| Module | Content | Status |
|---|---|---|
| `MultiwayExec.lean` | `ExecHG ℕ`, `ExecRule`, `allMatches`, `multiwayStep`. `singleWayStep` applies a maximal set of edge-disjoint matches, chosen greedily in enumeration order. `fireAllStep` applies every match, including matches that share edges, and is not a Wolfram model update when matches overlap. | DEFINITIONS, PROVED (`fireIfFree` lemmas) |
| `MultiwayExecBridge.lean` | Casts from executable to abstract rules and systems, `consumed_toMultiset`. No simulation of `singleWayStep` by `MultiStep`. | PROVED |
| `MultiwayExecTests.lean` | Multiway state and event counts for TC1, TC2, TC3, TC6; subdivision counts `2^n`, `2^n + 1` for `n ≤ 4` | PROVED (`decide`) |
| `SubdivisionPath.lean` | `subdivisionTrajectory n := pathEdges (subdVerts n)` and its path properties | PROVED. Agreement with `singleWayEvolve` for `n ≤ 5` and base step on `Fin 8`, `Fin 12`: PROVED-WITH-NATIVE-DECIDE |
| `SubdivisionAbstract.lean` | `singleWayStep_subdivisionSys_consEdge_of_ne`: one step of the subdivision rule on `{a, b}` for every `a ≠ b : ℕ` | PROVED |
| `RuleSignatureSchema.lean` | `Dossier`, `isConsistent`, `canonicalDossier`, `consistent_dossier_eq_canonical` | PROVED |
| `RuleSignatureExecCorpus.lean` | `ExecRule` versions of the catalogue rules. `h1_corpus_edgeCount_screener_verdict`: constant edge count for the trivial rule and for the G3 rule on the path and 4-cycle seeds, non-constant for the doubling, append and triple rules. On the 4-cycle seed the four matches pairwise share an edge, `singleWayStep` fires one, and the edge count stays 4. | PROVED-WITH-NATIVE-DECIDE |
| `CausalEventTrace.lean` | `tracedSingleWayStep`, `tracedFireAllStep`, `deriveCausalEdges` (by edge values, so equal hyperedges from different events give extra pairs), `causalDAGOfEvolution`, `causalDAGOfFireAll`. Knill value 6 for the subdivision event graph at depth 2. | PROVED-WITH-NATIVE-DECIDE |
| `BranchialEventTrace.lean` | `eventsAreBranchial`: same-step consumed-edge contention between events. This is not the Wolfram-model branchial graph, which relates states. | PROVED-WITH-NATIVE-DECIDE |

The modules MultiRuleDiscovered, StepZeroAncestor, H9Bridge, H9BridgeStepProof, H9Closure, H9StructuralProgress, DistinctEdgeAPI, DistinctEdgeIdentity, PartitionClosure, the multi-rule part of UniversalAdditivity, the BBH*, Branchial* and Discrete* modules that use `tracedFireAllEvolve`, EnhancedPsi4, CurvatureDensityLimit, MultiRuleDepthTrajectory, Phase_D_FrameworkOverview and VacuumLikeUniversal state their results with `fireAllStep`. Their results do not describe Wolfram model evolutions.

## 3. Hypergraph calculus

| Module | Content | Status |
|---|---|---|
| `DiscreteCalculus.lean` | Graph Laplacian, inner product, linearity | PROVED |
| `DiscreteCalculusSymm.lean` | Self-adjointness, Dirichlet form, `laplacian_sum_zero` | PROVED |
| `HypergraphLaplacian.lean` | `laplacianHyper`, linearity, Dirichlet non-positivity, self-adjointness | PROVED |
| `HypergraphCalculus.lean` | Gradient, divergence, `summation_by_parts` | PROVED |
| `SecondDifference.lean` | Central second difference, exact on quadratics | PROVED |
| `CycleGraph.lean` | `cycleLaplacian`, cycle Dirichlet form | PROVED |
| `CTwoTaylor.lean` | `scaledSecondDiff_tendsto_iteratedDeriv` for `ContDiff ℝ 2 f` | PROVED |
| `CycleSpectrum.lean` | Cycle eigenvectors and eigenvalues, `cycleLaplacian_eigen` | PROVED |
| `CycleEigenLimit.lean` | `cycleEigenvalue_scaled_tendsto`: `n² · cycleEigenvalue n k → −(2πk)²` | PROVED |
| `ScaledDiffC2Bridge.lean` | Scaled hypergraph Laplacian on `cycleHypergraph n` equals the scaled second difference at interior indices | PROVED |
| `LaplacianMatrix.lean` | `laplacianMatrix`, `heatKernel = exp(t · Δ)`, semigroup law, symmetry, `heatTrace` | PROVED |
| `CycleMatrixSpectrum.lean` | Cycle eigenvectors are matrix eigenvectors | PROVED |
| `HeatKernelODE.lean` | `heatKernel_isHeatSolution` | PROVED |
| `ExpEigenvector.lean` | `exp_mulVec_of_eigenvector` | PROVED |
| `CycleHasEigenvalue.lean` | `laplacianMatrix_cycleHypergraph_hasEigenvalue` | PROVED |
| `SymmEigenOrthogonal.lean` | Orthogonality of eigenvectors for distinct eigenvalues | PROVED |
| `PathHypergraph.lean` | `pathHypergraph n`, path eigenvalue formulas and sign lemmas | PROVED. OPEN: the eigenvalue equation for the path |
| `PathHypergraphDistance.lean` | Path adjacency, connectivity, degrees | PROVED |
| `HypergraphCycleBridge.lean` | `laplacianHyper_cycleHypergraph`, `hypergraph_scaled_laplacian_eq_second_deriv` for quadratics | PROVED |
| `LaplacianBridge.lean` | `n² · Δ²_{1/n} f = f''` for quadratics | PROVED |

## 4. Equations on `Hypergraph V`

| Module | Equation | Result | Status |
|---|---|---|---|
| `HeatEquation.lean` | `u' = Δ_H u` | Mass conservation, L² decay | PROVED |
| `HeatEquationUniqueness.lean` | Heat equation | Existence, forward uniqueness, matrix-level conservation | PROVED |
| `HeatKernelDecay.lean` | Heat flow on the cycle | Non-constant modes and finite combinations decay to the constant part | PROVED |
| `CycleHeatDecayBounds.lean` | Heat flow on the cycle | Spectral gap is negative, explicit first-mode decay | PROVED |
| `WaveEquation.lean` | `u'' = Δ_H u` | Energy conservation | PROVED |
| `KleinGordon.lean` | `u'' = Δ_H u − m²u` | Energy conservation | PROVED |
| `SchrodingerEquation.lean` | Real and imaginary parts of `iψ' = −Δ_H ψ` | Total probability is constant | PROVED |
| `ScalarField.lean` | Lagrangian, Hamiltonian | `KG_EulerLagrange_iff_KleinGordonSolution` | PROVED |
| `DiscreteDAlembertian.lean` | Benincasa-Dowker operator, `discreteAction`, `discreteEL` | Linearity | PROVED. OPEN: `BenincasaDowkerConjecture` (a structure with no instance) |

## 5. Continuum limits

| Module | Content | Status |
|---|---|---|
| `Infra/ScaledCycle.lean` | `cycleDist` | PROVED |
| `Infra/LatticeDensity.lean` | `1/n`-density of the lattice | PROVED |
| `Infra/Circle.lean` | Circle metric, `latticeEmbed_isometry` | PROVED |
| `Infra/GHBound.lean` | `cycle_circle_gh_bound` (`1/(2n)`) | PROVED |
| `Infra/ScaledPath.lean` | `path_interval_gh_bound` | PROVED |
| `Infra/ScaledTorus.lean`, `Infra/ScaledTorusD.lean` | `torus_gh_bound`, `dTorus_gh_bound` | PROVED |
| `Infra/GHApprox.lean` | `GHApproximation` | PROVED |
| `Infra/LorentzLattice.lean` | Discrete Lorentzian lattice, causal relations, interval | PROVED |
| `Infra/Minkowski.lean` | Continuum Minkowski space with the L∞ spatial metric | PROVED |
| `Infra/TrajectoryLorentz.lean`, `Infra/TrajectoryLorentzD.lean` | Trajectory to lattice by causal level; with a spatial embedding under `LightConeCompatible` | PROVED |
| `Infra/ScaledLorentz.lean` | `lorentzIntEmbed_preserves_causal_iff`, `scaledLorentzEmbed_dense` | PROVED |
| `Infra/FullBridge.lean` | `causallyPrecedes_gives_continuum` under `LightConeCompatible` | PROVED |
| `ContinuumBridgeDemo.lean` | Scaled cycle spectra of four operators tend to the circle spectra | PROVED |
| `ContinuumLimitStatement.lean` | Spectral limits of the heat, wave, Schrödinger and Klein-Gordon operators on the cycle; Riemann sums of polynomials of degree ≤ 3 (`A6Holds_poly_deg3`) | PROVED. `CycleLaplacianConvergenceC2` is stated and not proved in this module. `TorusLaplacianConvergenceC2` is the constant `True`. `SchwarzschildObligationMet`, `KerrObligationMet`, `FLRWObligationMet` contain `False` |
| `Limit.lean` | `HypergraphSequence`, `MetricMeasureTarget`. No convergence statement. | DEFINITIONS |
| `GraphMetric.lean` | Graph distance, `ScaledHypergraph` | DEFINITIONS |

## 6. Curvature and metrics in coordinates

| Module | Content | Status |
|---|---|---|
| `CurvatureLocalCoord.lean` | `MetricData n`, Christoffel symbols | PROVED |
| `CurvatureRiemann.lean` | Riemann, Ricci, scalar and Einstein tensors, `bianchi_first`, `minkowski4_satisfies_vacuum_EFE`, `leviCivitaConnection` | PROVED |
| `PartialMetricData.lean` | Metrics with a domain predicate | PROVED |
| `Schwarzschild.lean` | Components, exterior region, `sginv_mul_sgg`, Christoffel symbols | PROVED |
| `FLRW.lean`, `FLRWRicci.lean` | FLRW metric and connection, Ricci and Einstein components, `flrwEFE_diag_iff_friedmann` | PROVED |
| `ReissnerNordstrom.lean` | Metric, `rnLapse_schwarzschild` | PROVED |
| `DeSitter.lean` | Metric, `dsLapse_pos_iff` | PROVED |
| `Kerr.lean` | Metric in Boyer-Lindquist coordinates, zero-spin reductions | PROVED |
| `TwoSphere.lean` | Round 2-sphere, `sphereChristoffel_0_1_1` | PROVED |
| `CurvedRicciBridge.lean`, `WarpedDiag2C2.lean` | `warpedDiag2`, its Christoffel, Riemann and Ricci components, `warpedDiag2_einstein` | PROVED |
| `EinsteinEquations.lean` | `EinsteinEqLambda`, `minkowski4_flat_vacuum_forces_lambda_zero` | PROVED |
| `CovariantDerivative.lean` | Covariant derivatives for `ConnectionData` | PROVED |
| `LorentzianManifold.lean` | `DiagLorentzianMetric`, Minkowski instance | PROVED |
| `RiemannianManifold.lean` | `DiagRiemannianMetric`, Euclidean instance | PROVED |
| `StressEnergyTensor.lean` | Stress-energy tensor, energy conditions, `wec_implies_nec` | PROVED |
| `GRMetricsDemo.lean` | `gr_metric_zoo` lists the formalised metrics | PROVED |
| `DiscreteRicci.lean` | Forman-Ricci curvature, ball-volume scalar curvature | PROVED |
| `RicciBridge.lean` | Circle Ricci curvature and cycle Forman-Ricci curvature are both 0 | PROVED |

## 7. Origin obligations and emergence statements

Every origin obligation in this section is a statement in which the target does not occur, so it holds for every target (`Curvature.any_metric_has_strong_obligation_witness`). `WassersteinRateObligation d` concerns a caller-supplied sequence `d` and is satisfied by the zero function. The theorems below do not state convergence to any metric, quantum system or black hole.

| Module | Content | Status |
|---|---|---|
| `WassersteinRate.lean` | `WassersteinRateObligation`, `ConvergenceRateObligation`, `subdivisionDiscrepancy n := 1/2^n` (defined directly, not computed from a measure) | PROVED |
| `HypergraphMetricBridges.lean` | `HypergraphMetricOriginObligation` and its `WithRate`, `Strong` and partial forms; `minkowski4_from_hypergraph_strong`, `all_gr_targets_have_strong_obligations_proven` | VACUOUS |
| `Milestone.lean` | `GR_emerges_from_hypergraph target`, `QM_emerges_from_hypergraph`, `BBH_emerges_from_hypergraph`. The layer Props are satisfied by the zero discrepancy. `GR_emerges_from_hypergraph_holds` proves the GR statement for every target. | VACUOUS |
| `GREmergence.lean` | `zoo_strong_origin_obligations`, `minkowski4_quadDischarge_components` | VACUOUS |
| `QMEmergence.lean` | `quantum_strong_origin_obligations`, `zoo_and_quantum_strong_origin_obligations` | VACUOUS |
| `BBHEmergence.lean` | `bbh_strong_origin_obligations`, `zoo_quantum_bbh_strong_origin_obligations` | VACUOUS |
| `ExecRateBridge.lean` | `strong_obligation_from_exec_rate`, `*_strong_from_exec_witness_*` | VACUOUS. `witnessRule0_passes`: PROVED-WITH-NATIVE-DECIDE |
| `TransportRateBridge.lean`, `HiguchiRateBridge.lean`, `DegVarianceRateBridge.lean`, `SquareCountRateBridge.lean` | Rate bridges for four further scalars and their metric discharges | VACUOUS. Trace values of `witnessRule0`: PROVED-WITH-NATIVE-DECIDE |
| `WitnessDiversity.lean` | Discharges on the seeds `path123` and `cycle4` | VACUOUS. Trace values: PROVED-WITH-NATIVE-DECIDE |
| `ExecTrajectoryLift.lean` | `liftExecRunInitial`, `strong_obligation_from_exec_rate_with_lifted_trajectory` | VACUOUS |
| `MetricTargetScalars.lean` | `formanTarget` and four other targets, all the constant 0 for every metric; `minkowski4_strong_coupled` and the other coupled discharges | VACUOUS |
| `RuleExtraction.lean` | Five named rules from `quintStableSelect` and their metric discharges | Selection and traces: PROVED-WITH-NATIVE-DECIDE. Discharges: VACUOUS |
| `LiteratureRules.lean` | Six literature rules and their traces at depth 2 | Traces: PROVED-WITH-NATIVE-DECIDE. Discharges: VACUOUS |
| `CycleContinuumLimit.lean` | Forman total 0 on nine cycles; constant-zero sequence tends to `formanTarget M = 0` | PROVED-WITH-NATIVE-DECIDE, PROVED. VACUOUS with respect to the metrics |
| `DiscreteRicciConvergence.lean` | `FiniteFitEnvelope`, `TrueLimitConverges`; a trace constant at 4 does not tend to 0 | PROVED |
| `FiberedGraphConnectionBridge.lean` | `ConnectionDataOriginObligation`, `any_connection_has_obligation_witness` | VACUOUS |
| `CausalLorentzianBridge.lean` | `LorentzianManifoldOriginObligation`, `any_lorentzianManifold_has_obligation_witness` | VACUOUS |
| `EinsteinEquationsBridge.lean` | `EFEOriginObligation_iff_EinsteinEqLambda`: the obligation is equivalent to the Einstein equation alone | PROVED |
| `RuleWitnesses.lean` | `*_from_hypergraph_proved` | VACUOUS |
| `RuleSearch.lean` | Conservation screen and catalogue | PROVED. `minkowski4_from_growthRule`: VACUOUS |
| `RemainingObligations.lean` | `all_obligations_hold`: cycle ball volume `2r + 1`, cycle distances below `n + 1`, Vietoris-Rips scale trichotomy, `‖⟨ψ, φ⟩‖ ≤ Σ ‖ψ s‖‖φ s‖`, `reverseEngineeringObligationRefined_holds`, `not_reverseEngineeringObligation`. `EMEPersistenceObligation` and `PathIntegralObligation` are satisfied by the zero vector. | PROVED |

## 8. Distance, dimension and topology

| Module | Content | Status |
|---|---|---|
| `HypergraphDistance.lean` | `dist`, balls, local and Wolfram-Hausdorff dimension, angles, spheres, bisectors, midpoints, Voronoi cells, `GeodesicallyUnique`, cut vertices; `dist_triangle`, `cycleHypergraph_connected` | PROVED |
| `HypergraphTopology.lean` | `spatialB0`, `firstBettiZ`, `spatialDiameter`, open-set predicates (`IsDiscreteOpen` is `True`), `nbhdBasis` | PROVED |
| `HypergraphMeasure.lean` | Counting and uniform measures, pushforwards | PROVED |
| `RodkeyClassification.lean` | Adjacency-transitive implies uniform ball volume; uniform ball volume implies regular; cycle satisfies, path fails | PROVED. OPEN: general classification |
| `PlateauDimension.lean` | `plateau_range_nonempty` | PROVED |
| `HomologyDimension.lean` | `HasNontrivialHomology_requires_simplex` | PROVED |
| `CoordinatizationDimension.lean` | Axes, `AreOrthogonalAxes` by `IsOrthoApprox` | DEFINITIONS |
| `CausalDimension.lean` | `HasChainToDepth` | DEFINITIONS |
| `VietorisRips.lean` | Vietoris-Rips edges, simplices, graph | PROVED |
| `HodgeVR.lean`, `HodgeLaplacianSpectrum.lean`, `HodgeLaplacianBounds.lean` | Hodge 0-Laplacian on the Vietoris-Rips complex: linearity, symmetry, constants in the kernel, `vrHodge0_quadratic_nonpos` | PROVED |

## 9. Gauge, causal, synthetic and blowup structures

| Module | Content | Status |
|---|---|---|
| `FiberedGraph.lean` | Fibred graphs, sections, connections | PROVED |
| `Holonomy.lean` | Parallel transport, holonomy, Wilson loops, `flat_holonomy_all_fixed` | PROVED |
| `FiberBundle.lean`, `MultiFibrationProjection.lean` | Fibre-bundle predicate, multi-fibred graph | DEFINITIONS |
| `HypergraphConnection.lean` | Group-valued connection on a hypergraph, `transportWalk_append` | PROVED |
| `CausalGraphType.lean` | `CausalGraph V`, `causallyPrecedes`, chains, light steps | PROVED |
| `CausalFoliation.lean` | Antichains, foliations, proper time | PROVED |
| `ProperTimeBounds.lean` | Chain-length lemmas | PROVED |
| `SpatialReconstruction.lean` | Adjacency by shared immediate ancestors | PROVED |
| `EPSAxioms.lean` | Ehlers-Pirani-Schild axioms as Props, `eps_worldline_not_light` | PROVED |
| `MarzkeWheeler.lean` | `mwClock_implies_causallyPrecedes` | PROVED |
| `MultiwayCausalGraph.lean` | Rewriting system with a causal graph on events | DEFINITIONS |
| `SyntheticGeometry.lean`, `SyntheticAxiomatic.lean`, `InfrageometricScene.lean` | Synthetic circles, balls, segments, spheres, betweenness, scenes | PROVED |
| `ElementaryBlowup.lean`, `BlowupLieAlgebra.lean`, `BlowupOperations.lean`, `RadialLaminarBlowup.lean`, `BlowupPoissonConcrete.lean` | Blowups, `elementaryBlowup_commutator_vanishes`, cycle doubling, brackets | PROVED |
| `DagBlowup.lean`, `DagCalculus.lean`, `DeRham.lean`, `FormCochainIntegration.lean` | DAG derivative and prefix sums, `d0`, `stokes_zero_to_one`, integration | PROVED |

## 10. Branchial and quantum structures

`Branchial.lean` relates states of a multiway system. The modules below use that relation, or a symmetric adjacency matrix supplied as a parameter.

| Module | Content | Status |
|---|---|---|
| `BranchialFinite.lean` | Finiteness of branchial slices | PROVED |
| `BranchialHilbert.lean` | `EuclideanSpace ℂ S`, adjacency operator, Born probabilities, uniform weight | PROVED |
| `BranchialSchrodinger.lean` | Schrödinger evolution for a symmetric adjacency matrix conserves total probability | PROVED |
| `BranchialCanonical.lean` | Hamiltonian of a finite slice is symmetric | PROVED |
| `WolframPhysicsBridgeDemo.lean` | Hermitian operator, real expectation values and Born probabilities on a finite slice | PROVED |
| `BranchialCommutator.lean` | Multi-step branchial relation is reflexive, symmetric and transitive. No commutator theorem is stated. | PROVED |
| `FisherMetric.lean`, `FisherMetricExtended.lean` | Fisher inner product, linearity, non-negativity | PROVED |
| `EMETracker.lean` | Persistence of a predicate along a trajectory | PROVED |

## 11. Rule screening

These modules compute values for specific rules, seeds and depths of `singleWayStep`.

| Module | Content | Status |
|---|---|---|
| `CandidateRuleCatalog.lean` | G3 rule and four other rules, conservation status | PROVED |
| `CandidateRuleDatabase.lean`, `RuleSignature.lean`, `RuleSignatureEquiv.lean`, `StructuralRuleBounds.lean` | Rule signatures, conservation screens, signature equivalence | PROVED |
| `RuleSignatureScreener.lean` | Screeners as `ConvergenceRateObligation`s, conservative and persistent-gap results | PROVED |
| `RuleSignatureExecMetrics.lean` | Forman scalar on `ExecHG ℕ`, `SignatureVerdict` | PROVED-WITH-NATIVE-DECIDE |
| `RuleSignatureExecSearch.lean` | One-edge rule generator, trend classifier, stability filter (21 candidates, 11 stably classifiable), rate screener | PROVED-WITH-NATIVE-DECIDE |
| `DualCurvatureScreener.lean` | Combined screeners (Forman 11, transport 17, both 11) | PROVED-WITH-NATIVE-DECIDE |
| `OllivierRicciScreener.lean`, `OllivierRicciExec.lean` | Product-coupling upper bound on W₁ (not the optimal-transport curvature) | PROVED, PROVED-WITH-NATIVE-DECIDE |
| `HiguchiScreener.lean`, `DegreeVarianceScreener.lean`, `SquareCountScreener.lean` | Higuchi, degree-variance and square-count scalars on small graphs | PROVED-WITH-NATIVE-DECIDE |
| `InfraMeasure.lean` | Non-negative weights, couplings, transport cost | PROVED |
| `PerpendicularModuli.lean` | Three perpendicularity predicates disagree pairwise on small graphs | PROVED-WITH-NATIVE-DECIDE |
| `DiscoveredRules.lean`, `RuleReportComparison.lean`, `RulePhysicsReport.lean`, `RulePreservationClassification.lean` | Knill values and edge trajectories of named rules on `edge12` | PROVED-WITH-NATIVE-DECIDE |

## 12. Knill curvature and lattice samples

| Module | Content | Status |
|---|---|---|
| `KnillCore.lean` | Simplicial complexes, Euler and Wu characteristics, Dirac and Hodge operators, `dSquared_eq_zero`, `hodgeOnG_psd` | PROVED |
| `KnillExamples.lean` | Values on small complexes | PROVED-WITH-NATIVE-DECIDE |
| `KnillDiscreteGaussBonnet.lean`, `KnillHigherGenus.lean`, `KnillThreeManifold.lean`, `KnillTopologyBenchmark.lean`, `KnillRuleBridge.lean`, `CausalDAGKnill.lean` | Scaled Knill values of polyhedra, tori, K₅, complete graphs, the Petersen graph, Q₃, paths, small directed graphs | PROVED-WITH-NATIVE-DECIDE |
| `SphereTriangulationAudit.lean` | Unweighted Forman and Higuchi totals differ across three triangulations of S² | PROVED-WITH-NATIVE-DECIDE |
| `PathContinuumLimit.lean`, `GridContinuumLimit.lean`, `AdvancedContinuumLimits.lean`, `NormalizedDensityLimits.lean` | Scalar totals on sampled paths, cycles, tori and grids | PROVED-WITH-NATIVE-DECIDE |
| `PolynomialDensityLimits.lean` | `polynomialPerArea_tendsto` and its grid instances | PROVED. 3-torus samples: PROVED-WITH-NATIVE-DECIDE |

## 13. Lean files attached to findings F1-F7

The findings about the papers are READ findings with line numbers, recorded in [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) and [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md).

| Module | Content | Status |
|---|---|---|
| `Refutations/F1NoMetric.lean` | The function type `DHyp V → V → V → ℝ` has more than one element | VACUOUS with respect to the papers |
| `Refutations/F2Orthonormality.lean` | Two functions on `Bool × Bool` make the same pair orthonormal | VACUOUS with respect to the papers |
| `Refutations/F3Tautology.lean` | The project's encodings of dimension preservation and the Euler-Lagrange equation are equal | PROVED (`Iff.rfl`) |
| `Refutations/F4Tautology.lean` | The project's encodings of causal invariance and discrete general covariance are equal | PROVED (`Iff.rfl`) |
| `Refutations/F5Illdefined.lean` | Facts about 1/(n+1) and the constant-`True` predicate | VACUOUS with respect to the papers |
| `Refutations/F6Circularity.lean` | `CircularReconstruction.comp_eq_id` restates its hypothesis | VACUOUS with respect to the papers |
| `Refutations/F7NamedRuleStructure.lean` | The G3 rule conserves edge count | PROVED |

## 14. Open statements

- `CausalHistory.GorardNamedRuleConeGrowthLinear`: for every `N` there is `c` such that, in every valid `RuleHistory` of the G3 rule with `N` initial hyperedges, every event `i` and every `t` satisfy `|ball i t| ≤ c·(t+1)`.
- `BenincasaDowkerConjecture` (`DiscreteDAlembertian.lean`): no instance is constructed.
- `CycleLaplacianConvergenceC2` (`ContinuumLimitStatement.lean`): the scaled second difference tends to `f''(x)` whenever `deriv f` has derivative `f''(x)` at `x`.
- `SchwarzschildObligationMet`, `KerrObligationMet`, `FLRWObligationMet`: defined with `False`, so they have no proof as stated. A rule whose evolution converges to a curved spacetime is not known to the project.
- The eigenvalue equation for `pathHypergraph n`.
- The general classification of hypergraphs with vertex-uniform local dimension (`RodkeyClassification.lean`).
- Small-`t` asymptotics of `heatTrace` (spectral dimension).
- Convergence of a discrete curvature to a non-zero continuum Ricci curvature.

## 15. `native_decide`

About 100 modules use `native_decide`. Results proved with it depend on an axiom generated by `native_decide` and are labelled PROVED-WITH-NATIVE-DECIDE above and in [`THEOREM_STATUS.md`](THEOREM_STATUS.md). `AxiomCheck.lean` holds `#print axioms` commands for selected theorems.
