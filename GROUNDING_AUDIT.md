# Grounding audit: which objects are defined from hypergraph data

The project's grounding principle requires every continuum structure in the library to be tied to hypergraph rewriting data. This file records, for each major object, which tie it has. Theorem statuses follow [`THEOREM_STATUS.md`](THEOREM_STATUS.md); the per-rung detail is in [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md).

## Tie categories

- HYPERGRAPH: defined directly on `Hypergraph V`, `RewritingSystem`, `Trajectory`, a causal graph or a branchial slice; or a discrete construct parametric over any finite carrier and instantiated on such data at a named consumer site.
- LIMIT: a PROVED continuum limit or approximation bound for a fixed graph family (cycles, paths, tori, lattices), with the theorem named. No LIMIT result concerns a rewriting evolution.
- TARGET-ONLY: a continuum object with no PROVED relation to hypergraph data. Some of these carry an origin obligation. The origin obligations do not depend on their target and hold for every target, so they relate the object to no hypergraph data.

### Origin obligations

`HypergraphMetricOriginObligation`, `HypergraphPartialMetricOriginObligation`, `HypergraphMetricOriginObligationStrong`, `HypergraphMetricOriginObligationWithRate`, their partial-metric forms, `ConnectionDataOriginObligation`, `LorentzianManifoldOriginObligation`, `HypergraphQuantumOriginObligationStrong` and `HypergraphBBHOriginObligationStrong` take the target as an unused argument. Each states that some rewriting system, trajectory, fibred graph or causal graph exists together with a positive sequence, and the strong forms add `WassersteinRateObligation d` for a caller-supplied `d` that the zero function satisfies. They hold for every target: `Curvature.any_metric_has_obligation_witness`, `Curvature.any_partialMetric_has_obligation_witness`, `Curvature.any_metric_has_strong_obligation_witness`, `Curvature.any_partialMetric_has_strong_obligation_witness`, `Curvature.any_connection_has_obligation_witness`, `Curvature.any_lorentzianManifold_has_obligation_witness`. `EFEOriginObligation M C Λ κ T x` is equivalent to `EinsteinEqLambda M C Λ κ T x` (`Curvature.EFEOriginObligation_iff_EinsteinEqLambda`). Every theorem that inhabits one of these Props for a specific target is VACUOUS.

## When a type needs a tie

A type needs a tie to hypergraph data when its definition contains continuum content: a coordinate chart `Fin n → ℝ`, a smooth manifold, `MetricData`, `ConnectionData`, a Riemannian or Lorentzian structure, PDE state on a continuum, or a tensor field on a manifold. Examples: `MetricData`, `ConnectionData`, `DiagLorentzianMetric`, `DiagRiemannianMetric`, `VectorBundleConnection`, `EinsteinEqLambda`.

A discrete construct that is parametric over any `[Fintype X] [DecidableEq X]` carrier and has no continuum content does not need its own tie. Examples: `TransportPlan μ ν`, `wasserstein1 d μ ν`, `PathIntegralAmplitude V`, `BranchialSlice sys s₀ n`, `CausalGraph V`, `Hypergraph V`. Such a construct is instantiated on hypergraph data at a consumer site with a named theorem. Example: `wasserstein1_delta_eq_dist` (`WassersteinFinite.lean`) is specialised to the cycle as `wasserstein1_cycleDelta_eq_hypergraphDist` (`CycleWasserstein.lean`), which gives W₁(δ_i, δ_j) = `(cycleHypergraph n).dist i j`.

## Rung 1. Discrete calculus: HYPERGRAPH

- `Hypergraph V`, `Hyperedge V`.
- `Hypergraph.laplacianHyper`, `Hypergraph.laplacianMatrix`, `Hypergraph.heatKernel`, `heatTrace`.
- `cycleHypergraph n`, `pathHypergraph n`.
- `Hypergraph.dist`, geodesic balls and ball volumes.

## Rung 2. Operator convergence

- `cycleEigenvalue n k`, `cycleEigenvector n k j` on `cycleHypergraph n`: HYPERGRAPH. `cycleLaplacian_eigen`: PROVED.
- `cycleEigenvalue_scaled_tendsto`: LIMIT (n²·λ_k(n) → −(2πk)²).
- `discreteWaveToContinuumWave_holds`, `discreteSchrodingerToContinuumSchrodinger_holds`, `discreteKleinGordonSpectrum_holds`, bundled in `pde_spectrum_bridge_summary` and `pde_spectrum_bridge_summary_with_mass`: LIMIT, mode by mode on cycles.
- `pathEigenvalue`, `pathEigenvector` on `pathHypergraph n`: HYPERGRAPH. The eigenvalue equation is PROVED only at k = 0.

## Rung 3. Measure and Gromov-Hausdorff approximation

- `countingMeasure`, `uniformProbability`, `pushforwardCounting` on `Hypergraph V`: HYPERGRAPH.
- `A6LatticeRiemannObligation` (lattice Riemann sums converge to the integral for every continuous f): OPEN. PROVED for polynomials of degree at most 3 (`A6_for_constants`, `A6_for_identity`, `A6_for_sq`, `A6_for_cube`, closed under `A6Holds.const_mul`, `A6Holds.add`, `A6Holds.sub`; combined in `A6Holds_poly_deg3`). LIMIT for these test functions.
- W₁ framework (`WassersteinFinite.lean`): `TransportPlan μ ν`, `wasserstein1`, with `wasserstein1_delta_eq_dist`, `wasserstein1_symm`, `wasserstein1_self_eq_zero`, `wasserstein1_triangle` and `wasserstein1_lipschitz_bound` PROVED. Cycle instance (`CycleWasserstein.lean`): `wasserstein1_cycleDelta_eq_hypergraphDist`, `wasserstein1_cycleDelta_succ` (= 1/n), `wasserstein1_shiftMeasure_le` (≤ 1/n), `wasserstein1_shiftIter_le` (≤ k/n). LIMIT on the cycle family.
- OPEN: a W₁ rate ≤ C/n from the scaled counting measure to Lebesgue measure. `WassersteinRateObligation d` concerns a caller-supplied sequence `d` and is satisfied by the zero function. `subdivisionDiscrepancy n = 1/2^n` is defined directly and is not computed from any measure.
- d-torus measure lift: OPEN. `MeasureTorusLift.lean` states rate obligations for a caller-supplied discrepancy, satisfied by the zero discrepancy (`multiDimRateObligation_zero`).
- Gromov-Hausdorff approximation of fixed families: LIMIT. `Infra.cycle_circle_gh_bound` (cycle, circle), `Infra.path_interval_gh_bound` (path, [0, 1]), `Infra.torus_gh_bound` (n×n lattice, 2-torus), `Infra.dTorus_gh_bound` ((Fin n)^(d+1) lattice, (d+1)-torus). Each gives an isometric embedding of the 1/n-scaled graph metric whose image is 1/(2n)-dense.
- `discreteHeatToContinuumHeat`: LIMIT, exp(t·n²·λ_k(n)) → exp(−(2πk)²t) for each mode k on cycles.

## Rung 4. Connections

- `Curvature.MetricData n`, `Curvature.ConnectionData n`, `Curvature.flatConnection n`, `Curvature.ConnectionData.nabla_scalar`, `nabla_vector` and `nabla_covector` (`CovariantDerivative.lean`): TARGET-ONLY.
- `ConnectionDataOriginObligation` holds for every connection (`Curvature.any_connection_has_obligation_witness`). `flatConnection_from_fiberedGraph_proved` and `flatConnection_minkowski4_from_fiberedGraph` inhabit it with an edge-free fibred graph: VACUOUS.
- `FiberedGraph`, `FiberedGraph.Connection`, `IsSection`, `ParallelTransportList`, `Holonomy`, `wilsonLoop`, `IsFlatConnection`, `IsFiberBundle`: HYPERGRAPH.
- `ScaledConnectionToLeviCivitaObligation` (`ScaledConnectionLimit.lean`): VACUOUS. `connectionSup` is identically 0, and `scaledConnectionToLeviCivita_trivial` holds for every family.
- OPEN: a theorem that a sequence of discrete connections on scaled graphs converges to a `ConnectionData` on a limit manifold.

## Rung 5. Riemann, Ricci, scalar curvature: TARGET-ONLY

- `Curvature.ricci`, `scalarCurvature`, `einsteinTensor`, `minkowski4`, `circleMetric`, Schwarzschild, FLRW, Reissner-Nordström, de Sitter, Kerr, S², `warpedDiag2`, `schwarzschildPartial`, `flrwPartial`: TARGET-ONLY.
- `gr_metric_zoo` (`GRMetricsDemo.lean`) states that these targets exist. It does not relate them to hypergraph data.
- The metric origin obligations attached to these targets (`HypergraphMetricBridges.lean`) hold for every target. `minkowski4_from_hypergraph_proved`, `warpedDiag2_from_hypergraph_proved`, `sphere_from_hypergraph_proved`, `schwarzschild_from_hypergraph_proved` and `flrw_from_hypergraph_proved` (`RuleWitnesses.lean`) inhabit them with `identitySystem Unit`, `cycleHypergraph n`, the zero-step `emptyTrajectory` and the sequence 1/(k+1): VACUOUS. All per-metric target scalars in `MetricTargetScalars.lean` are 0.
- `SchwarzschildObligationMet`, `KerrObligationMet`, `FLRWObligationMet` (`ContinuumLimitStatement.lean`) and `SchwarzschildVacuumObligation M` (`Schwarzschild.lean`): OPEN.
- `RicciBridge.forman_ricci_matches_continuum_on_cycle`: PROVED. On a 2-regular graph the Forman-Ricci edge curvature is 0, and the Ricci tensor of the flat connection on ℝ¹ is 0. The statement is that both vanish.
- `CurvedRicciBridge.warpedDiag2_christoffel_nonzero`, `curvedRicciBridgeObligation`, `threeRegular_formanRicci_nonzero`: PROVED. They state that `warpedDiag2` has a non-zero Christoffel symbol and that 3-regular graphs have non-zero Forman-Ricci curvature. No curved-target limit is proved. `CurvedDiscreteRicciObligation d` is satisfied by the zero sequence (`curvedDiscreteRicciObligation_zero`): VACUOUS.

## Rung 6. ODE and PDE: HYPERGRAPH

- Heat, wave, Schrödinger and Klein-Gordon equations on `Hypergraph V` and `cycleHypergraph n`: existence and forward uniqueness, mass conservation, L² decay, energy and probability conservation are PROVED (see `BRIDGE_MACHINERY.md` Rung 6).
- `discreteHeatToContinuumHeat`: LIMIT on cycles.
- `BranchialSchrodinger`: probability conservation on a finite branchial slice, PROVED.

## Rung 7. Fields

- `ScalarField.lean`: discrete scalar field, Lagrangian and Euler-Lagrange equation on `Hypergraph V`: HYPERGRAPH.
- Discrete gauge field: OPEN.

## Rung 8. Lorentzian geometry

- `Infra/LorentzLattice.lean` (discrete Lorentz lattice), `CausalGraph V`, `causalEdge`, `causallyPrecedes`, `causalFuture`, `causalPast`, `lightCone`, `ChainOfLength`, `StronglyCausal`: HYPERGRAPH.
- `TimeFunction` and `stablyCausal_hasFoliation` (PROVED): HYPERGRAPH.
- `Infra.lorentzIntEmbed_preserves_causal_iff`, `Infra.scaledLorentzEmbed_preserves_causal_iff`, `Infra.scaledLorentzEmbed_dense`: LIMIT on the Lorentz lattice family.
- `Infra.causallyPrecedes_gives_continuum`: PROVED under the hypothesis `LightConeCompatible τ φ` on a caller-supplied embedding. No theorem shows that a rule's trajectory satisfies the hypothesis.
- `DiagLorentzianMetric`, `DiagLorentzianManifold`: TARGET-ONLY. `LorentzianManifoldOriginObligation` holds for every target (`Curvature.any_lorentzianManifold_has_obligation_witness`); `minkowski4Manifold_from_causalGraph_proved` inhabits it with an edge-free `CausalGraph (Fin 1)`: VACUOUS.
- `LorentzianGHObligation d` is satisfied by the zero sequence (`lorentzianGHObligation_zero`): VACUOUS.
- OPEN: a convergence theorem from scaled causal graphs to a `DiagLorentzianManifold`, and Lorentzian Gromov-Hausdorff distance.

## Rung 9. Einstein equations: TARGET-ONLY

- `EinsteinEqLambda`: TARGET-ONLY.
- `minkowski4_satisfies_EFE_zero_lambda`, `minkowski4_flat_vacuum_forces_lambda_zero`, `flatConnection_einstein_divergence_zero`: PROVED continuum facts about the flat connection.
- `EFEOriginObligation M C Λ κ T x` is equivalent to `EinsteinEqLambda M C Λ κ T x` (`Curvature.EFEOriginObligation_iff_EinsteinEqLambda`). `minkowski4_flat_vacuum_EFE_originated`, `minkowski4_flat_vacuum_EFE_originated_global` and `schwarzschild_vacuum_EFE_origin_bundle_witnessed` add VACUOUS origin clauses to continuum facts.
- No rewriting rule is shown to produce a continuum limit that satisfies the Einstein equations. The Milestone Props (`Milestone.lean`) are satisfied by the zero discrepancy, and `Milestone.GR_emerges_from_hypergraph_holds` proves `GR_emerges_from_hypergraph target` for every target: VACUOUS.

## Rung 10. Hypergraph to geometry

- Flat targets: LIMIT for cycle, path, 2-torus, (d+1)-torus and Lorentz lattice families.
- Curved targets: TARGET-ONLY.
- `StressEnergyTensor`: TARGET-ONLY, with only the zero tensor used.

## Infrageometry groups

### IS. Synthetic (`SyntheticInfrageometry` paclet, PHAJEK): HYPERGRAPH

`SyntheticCircle`, `SyntheticLineSegment`, `SyntheticSphere`, `InfrageometricScene`, and the axioms of `SyntheticAxiomatic.lean`, all on `Hypergraph V`.

### IR. Ruliology and rule signatures: HYPERGRAPH

`RuleSignature V`, `hypergraphSignature` and the predicates `RewritingSystem.ProducesTrees`, `RewritingSystem.ProducesPlanar`, `IsDirectConcatSystem`, all on trajectories. PROVED: `RuleSignature.edgeCount_invariant_of_conservative` and `trajectory_size_invariant` (edge count of a conservative rule is constant). No dimension bound for planar, tree-producing or product rules is proved. `reverseEngineeringObligationRefined_holds` is PROVED with the zero-step trajectory of the empty rule list starting at the target hypergraph.

### IT. Topology and Vietoris-Rips: HYPERGRAPH

`VietorisRipsEdge`, `VietorisRipsSimplex`, `vietorisRipsGraph`, `PersistenceBarcode` on `Hypergraph V`. `latschevObligation_holds` (PROVED) states that distances on `cycleHypergraph n` are less than n + 1. It does not state Latschev's theorem. `scaleTrichotomyObligation_holds` (PROVED) covers the endpoints ε = 0 and ε = n on cycles.

### IQ. Quantum: HYPERGRAPH

- Fisher metric on branchial slices (HVLE direction): defined on `BranchialSlice`.
- `fubiniStudyBhattacharyya_bound`: PROVED, |⟨ψ, φ⟩| ≤ Σ_s |ψ_s|·|φ_s| on `BranchialHilbert S`.
- `EMEPersistenceObligation` and `PathIntegralObligation` are PROVED with the zero vector and the zero amplitude.

### IC. Causal (axiomatic relativity, CZAPATA and SAHMED): HYPERGRAPH

`CausalGraph`, `ChainOfLength`, `DegenerateInterval`, `spatialReconstructionAdj`, `IsFoliation`, `HasProperTime`, `EPSAxioms`, `MWClock` with `mwClock_implies_causallyPrecedes` (PROVED).

### IG. Fibred graphs, holonomy: HYPERGRAPH

`FiberedGraph`, `IsSection`, `FiberedGraph.Connection`, `ParallelTransportList`, `Holonomy`, `wilsonLoop`, `IsFlatConnection`, `IsFiberBundle`, `MultiFiberedGraph`, `GraphTangentBundle`. No convergence from an IG connection to a `ConnectionData n` is proved.

### IB. Blowups and Poisson brackets (HKOLCZ, Lie-Poisson): HYPERGRAPH

`ElementaryBlowup`, `BlowupLieAlgebraStructure`, `PoissonBracket`, radial and laminar blowups, on `Hypergraph V`. `ElementaryBlowup.CommutatorVanishesCausalBranchial` is a predicate; the commutator theorem is OPEN.

### IA. DAG calculus: HYPERGRAPH

`dagAsBlowupOfInterval`, `dagDerivative`, `dagPrefixSum`, de Rham complex on `Hypergraph V`, forms-to-cochains integration.

### ID. Dimension: HYPERGRAPH

Wolfram-Hausdorff dimension, plateau detection, homology, coordinatization and causal dimension are defined on hypergraph data. `dimensionCompatibilityObligation_holds` (PROVED): V(v, r) = 2r + 1 on `cycleHypergraph n` for 2r + 1 ≤ n. Heat-trace spectral dimension: OPEN.

## Open ties

1. A convergence theorem from scaled discrete connections on fibred graphs to a curved `ConnectionData n`.
2. A convergence theorem from a rewriting evolution to any metric in the GR zoo.
3. A convergence theorem from scaled causal graphs to a `DiagLorentzianManifold`.
4. A rule whose continuum limit satisfies the Einstein equations.
5. Weak convergence of lattice measures for every continuous test function, a W₁ rate, and the d-torus lift.
6. A discrete gauge field.
7. Lorentzian Gromov-Hausdorff distance.
8. A discrete stress-energy tensor.

The origin obligations attached to these objects hold for every target and do not close any of these items.
