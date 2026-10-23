# InfraFormalization

A Lean 4 / Mathlib library on hypergraph rewriting (the Wolfram model) and its relation to general relativity and quantum mechanics, with an audit of four papers by Jonathan Gorard on the derivation of general relativity from hypergraph rewriting.

The repository has three parts:

1. A Lean library of discrete structures (hypergraphs, rewriting rules, trajectories, causal graphs, discrete calculus, metric and curvature data, branchial Hilbert spaces) and of statements that relate them to continuum targets.
2. An audit of G1-G4 (arXiv:2004.14810, 2011.12174, 2102.09363, 2303.07282): close readings with line numbers, Lean statements about the project's encodings, and measurements of the rule of G3. The status of each conclusion is in [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md).
3. The infrageometry task list of the Wolfram Institute ([`INFRAGEOMETRY.md`](INFRAGEOMETRY.md)), with contributors indexed in [`CONTRIBUTORS.md`](CONTRIBUTORS.md).

## Status of the Lean library

`lake build` completes without errors and without `sorry`. [`THEOREM_STATUS.md`](THEOREM_STATUS.md) lists every theorem cited in the documentation with its status from `#print axioms`: PROVED (axioms at most `propext`, `Classical.choice`, `Quot.sound`), PROVED-WITH-NATIVE-DECIDE (depends on `Lean.ofReduceBool`; about 100 files use `native_decide`), or VACUOUS (proved, but the statement does not concern the object its name refers to). `scripts/theorem_status.sh` regenerates the table.

Two classes of statements are VACUOUS:

- The origin obligations (`HypergraphMetricOriginObligationStrong` and its quantum, BBH and connection forms) do not depend on their target and hold for every target (`Curvature.any_metric_has_strong_obligation_witness`). The theorems in `GREmergence.lean`, `QMEmergence.lean`, `BBHEmergence.lean` and `HypergraphMetricBridges.lean` that discharge them do not state convergence to any metric, quantum system or black hole.
- The milestone statements of `Milestone.lean` hold for every target: `Milestone.GR_emerges_from_hypergraph_holds`, `Milestone.QM_emerges_from_hypergraph_holds`, `Milestone.BBH_emerges_from_hypergraph_holds`.

`MultiwayExec.singleWayStep` applies a maximal set of edge-disjoint matches per step. `MultiwayExec.fireAllStep` applies every match, including overlapping ones, and is not a Wolfram model update when matches overlap; the modules that use it are listed in [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md), section "Execution engine".

## Audit of G1-G4

Paper files: G1 = `papers/gorard_2004.14810.txt`, G2 = `papers/gorard_2011.12174.txt`, G3 = `papers/gorard_2102.09363.txt`, G4 = `papers/gorard_2303.07282.txt`.

- G1 §3.3 (lines 2168-2240) uses a discrete metric, a volume measure and orthonormal hyperedges that are not constructed from the hypergraph (READ, G1 line 786 and lines 2061-2063), and states asymptotic dimension preservation as the Euler-Lagrange equation of the action (READ, lines 2203-2211). The passage from sum to integral (line 2214) states no notion of convergence.
- G1 identifies causal invariance with discrete general covariance (READ, lines 1066-1075). The project's encodings of this equivalence and of the one above hold by `Iff.rfl` (PROVED).
- G3 eq. 342 and eq. 344 differ from Gray (1973) and Ollivier (2009) by factors of 2 and 6 on S² and S³ (PROVED as arithmetic comparisons; [`results/phase2_continuum/`](results/phase2_continuum/)).
- G3 states that the rule {{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}} "provably satisfies the Einstein field equations in the continuum limit" (lines 50-52) and gives no proof for this rule. Its comparison with numerical relativity assumes Poisson-distributed rewrite events (line 6080) and starts from a hypergraph sampled from the Brill-Lindquist initial data (lines 6148-6152, 6179).
- The rule conserves edge count, and in every evolution from N hyperedges, with any update order, every antichain of its causal graph has at most N/4 events and at most 5^t events lie within directed distance t of an event (PROVED, `CausalHistory.lean`). Linear cone growth is OPEN (`CausalHistory.GorardNamedRuleConeGrowthLinear`). Measured cone-growth exponents on cycles, paths and 3D grids up to 2000 events lie between 0.77 and 1.26 and depend on the update order (MEASURED, [`notes/empirical_refutation.md`](notes/empirical_refutation.md)).
- G4's title names discrete singularity theorems, and its abstract states such a theorem as a hope (READ, lines 1-3, 76-78).

Details: [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) (findings F1-F8), [`FINDINGS.md`](FINDINGS.md) (one line per claim), [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md) (status per claim, and the section on reproducing the binary black hole experiment of G3).

## How it is structured

### Lean source (`lean/InfraFormalization/`)

```
lean/
  InfraFormalization.lean            — top-level module; imports everything
  InfraFormalization/
    # Core substrate
    Hypergraph.lean                  — Hypergraph V; Adj, degree, geodesicBall
    Rule.lean                        — Rule P; IsConservative
    Application.lean                 — Application r; size preservation
    Conservation.lean                — |LHS|=|RHS| ⇒ size preserved on trajectories
    Multiway.lean                    — RewritingSystem, Step, MultiStep
    Causal.lean                      — Trajectory sys init, causallyPrecedes (on hyperedge values)
    CausalHistory.lean               — evolutions with hyperedge identities; causal graph; antichain and cone bounds
    CausalLevel.lean                 — level function, antichain at each level
    Branchial.lean, BranchialCanonical.lean
    ParallelSchedule.lean, Demo.lean
    RuleSearch.lean, RuleWitnesses.lean
    CandidateRuleCatalog.lean        — H1: literature rules as Rule P (gorardNamedRule, etc.)
    CandidateRuleDatabase.lean       — IR6: CandidateRule + decidable screens
    MultiwayCausalGraph.lean         — J1: combined causal + branchial structure

    # Discrete calculus & spectral theory (Rungs 1–2)
    DiscreteCalculus.lean, DiscreteCalculusSymm.lean  — graph Laplacian, self-adjoint, Dirichlet, PSD
    HypergraphLaplacian.lean         — Δ_H on directed hyperedges
    HypergraphCalculus.lean          — gradient, divergence, Stokes
    HypergraphDistance.lean          — dist, geodesic balls, triangle ineq; cycle-hypergraph walk infrastructure (ID6 machinery)
    HypergraphConnection.lean        — C7: discrete connection, transport along walks, holonomy, IsFlat
    PathHypergraph.lean, PathHypergraphDistance.lean
    RodkeyClassification.lean        — P20 (partial): BallVolumeVertexUniform, DistTransitive, Regular
    LaplacianMatrix.lean             — Mathlib matrix form + heat kernel via Matrix.exp (R2)
    LaplacianBridge.lean, HypergraphCycleBridge.lean
    CycleGraph.lean, CycleSpectrum.lean, CycleMatrixSpectrum.lean
    CycleHeatDecayBounds.lean
    HeatKernelODE.lean               — ODE ↔ matrix heat kernel (T1)
    ExpEigenvector.lean              — exp fixes eigenvectors (T2)
    CycleHasEigenvalue.lean          — Mathlib HasEigenvalue form (T4)
    CycleEigenLimit.lean             — scaled eigenvalue → continuum (A4)
    SecondDifference.lean, CTwoTaylor.lean, ScaledDiffC2Bridge.lean  — C² Taylor bridges (R1/A3)
    SymmEigenOrthogonal.lean

    # PDE ladder (Rung 6)
    HeatEquation.lean, HeatEquationUniqueness.lean
    HeatKernelDecay.lean             — long-time convergence to uniform (D6 partial)
    WaveEquation.lean, KleinGordon.lean, SchrodingerEquation.lean
    ScalarField.lean                 — Lagrangian + Euler-Lagrange (G1/G3/G4)
    DiscreteDAlembertian.lean

    # Continuum limits (Rungs 1–6)
    Infra/ScaledCycle, ScaledPath, ScaledTorus, ScaledTorusD
    Infra/LatticeDensity, Circle, GHBound, GHApprox
    Infra/OllivierStatement, GrayTubeStatement
    Infra/LorentzLattice, Minkowski, ScaledLorentz
    Infra/TrajectoryLorentz{,D}, FullBridge

    # Metrics, connections, curvature (Rung 5)
    CurvatureLocalCoord.lean         — MetricData n, Christoffel, symmetries
    CurvatureRiemann.lean            — Riemann, Ricci, Einstein; flat case vanishes
    DiscreteRicci.lean               — Forman-Ricci
    RicciBridge.lean, CurvedRicciBridge.lean
    CovariantDerivative.lean         — ∇ on ConnectionData (X2)
    PartialMetricData.lean           — X1: metrics with validity domains
    RiemannianManifold.lean          — C1: DiagRiemannianMetric + Euclidean witness
    LorentzianManifold.lean          — C2/E1: DiagLorentzianMetric + Minkowski witness
    Schwarzschild.lean, FLRW.lean, ReissnerNordstrom.lean, Kerr.lean
    DeSitter.lean, TwoSphere.lean
    GRMetricsDemo.lean               — single-theorem bundle over the GR zoo

    # Lorentzian structure & causal foliation (Rung 8)
    CausalGraphType.lean             — TR-DAG CausalGraph (IC1)
    CausalFoliation.lean             — stably causal → foliation (E5 in progress)
    SpatialReconstruction.lean, EPSAxioms.lean, MarzkeWheeler.lean
    ProperTimeBounds.lean

    # Einstein equations (Rung 9)
    EinsteinEquations.lean           — F3 EinsteinEqLambda; Minkowski vacuum
    StressEnergyTensor.lean
    # F2 energy conditions, F7 Penrose statement, F8 Raychaudhuri
    # all live under CurvatureRiemann + StressEnergyTensor + EinsteinEquations

    # Hypergraph-origin obligations (grounding-audit bridges)
    HypergraphMetricBridges.lean     — G2: every GR metric ↔ hypergraph origin obligation
    CausalLorentzianBridge.lean      — G3: manifold-from-causal-graph obligation
    FiberedGraphConnectionBridge.lean— G1: connection-from-fibered-graph obligation
    EinsteinEquationsBridge.lean     — G4: EFE origin obligation bundling the above

    # Fibered-graph machinery (IG)
    FiberedGraph.lean, Holonomy.lean, FiberBundle.lean
    MultiFibrationProjection.lean, CoordinatizationDimension.lean

    # Infradimension (ID)
    HomologyDimension.lean, PlateauDimension.lean, CausalDimension.lean

    # Infratopology + VR (IT)
    VietorisRips.lean, HodgeVR.lean
    HodgeLaplacianSpectrum.lean, HodgeLaplacianBounds.lean

    # Branchial / quantum (IQ) + measure (A5)
    BranchialHilbert.lean, BranchialSchrodinger.lean, BranchialFinite.lean
    BranchialCommutator.lean
    FisherMetric.lean, FisherMetricExtended.lean
    EMETracker.lean
    HypergraphMeasure.lean

    # Blowup / Lie / Poisson (IB)
    ElementaryBlowup.lean, BlowupOperations.lean, BlowupLieAlgebra.lean
    RadialLaminarBlowup.lean, BlowupPoissonConcrete.lean

    # Analysis on DAGs / forms (IA)
    DagBlowup.lean, DagCalculus.lean, DeRham.lean, FormCochainIntegration.lean

    # Synthetic axiomatic infrageometry (IS)
    SyntheticGeometry.lean, SyntheticAxiomatic.lean, InfrageometricScene.lean

    # Rule signatures and dimension bounds (IR)
    RuleSignature.lean, RuleSignatureEquiv.lean
    RuleDimensionBounds.lean, StructuralRuleBounds.lean

    # Final-obligation Props + master closure
    RemainingObligations.lean        — all seven infrageometry obligations; all_obligations_hold

    # Continuum-limit Props for targets currently open
    ContinuumLimitStatement.lean     — Schwarzschild/Kerr/FLRW continuum-limit statements
    ContinuumBridgeDemo.lean, WolframPhysicsBridgeDemo.lean, GrandTour.lean

    # Refutations
    Refutations/F1NoMetric.lean, F2Orthonormality.lean, F3Tautology.lean
    Refutations/F4Tautology.lean, F5Illdefined.lean, F6Circularity.lean
    Refutations/F7NamedRuleStructure.lean

    # Axiom-cleanliness certification
    AxiomCheck.lean                  — #print axioms for a hand-picked list of theorems
```

### Documentation

| File | Content |
|---|---|
| [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md) | Status of each conclusion about G1-G4 |
| [`THEOREM_STATUS.md`](THEOREM_STATUS.md) | Status of every theorem cited in the documentation |
| [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) | Findings F1-F8 with paper lines and Lean files |
| [`FINDINGS.md`](FINDINGS.md) | One line per audited claim |
| [`STATUS.md`](STATUS.md) | State of the library by area |
| [`COVERAGE_MAP.md`](COVERAGE_MAP.md) | Content of each module |
| [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md) | Which objects are defined from hypergraph data |
| [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) | The ten areas from discrete calculus to the Einstein equations |
| [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) | Infrageometry task list (groups IA-IR) |
| [`MILESTONES.md`](MILESTONES.md) | Phase tracker |
| [`NEXT_STEPS.md`](NEXT_STEPS.md) | Open work |
| [`RULE_SEARCH.md`](RULE_SEARCH.md) | Rule-search pipeline |
| [`PUBLISHABLE.md`](PUBLISHABLE.md) | Paper targets |
| [`GLOSSARY.md`](GLOSSARY.md) | Terms |
| [`INDEX.md`](INDEX.md) | Document tree |
| [`LEAN_PHYSICS.md`](LEAN_PHYSICS.md) | Conventions shared with Mathlib physics and HepLean |

Dated weekly reports (`INFRAFORMALIZATION_WEEKLY_REPORT_*.md`, `POST_WEEKLY_UPDATES_*.md`, `weekly_email_*.txt`) record the state on their dates.

### Audit notes (`notes/`)

- `plan.md`: verification plan
- `severity_taxonomy.md`: groups S1-S6 of the findings
- `corpus_audit.md`: errors repeated across G1-G4
- `claims_catalog.md`: G1 equation by equation
- `singleway_vs_multiway.md`: single-way and multiway evolution
- `corpus_assessment.md`: per-claim assessment
- `2004.14810_close_reading.md`, `2102.09363_close_reading.md`, `2303.07282_close_reading.md`: close readings
- `null_tetrad_resolution.md`, `limit_toolkit.md`, `empirical_refutation.md`, `continuum_limit_claims.md`

### Results (`results/`)

- `phase1_selfaudit/`: Python rewriter and SetReplace runs of the G3 rule; cone-growth measurements on 9 seeds.
- `phase2_continuum/`: G3 eq. 342 (Gray tube) and eq. 344 (Ollivier) with symbolic and numeric computation.

## Building

Prerequisites: Lean 4 via `elan`, `lake`, and a Mathlib build.

```bash
cd lean
lake update            # first-time Mathlib setup
lake build
```

## Reproducing the measurements

Prerequisites: `wolframscript` with SetReplace 0.3 or later, Python 3.10 or later.

```bash
# SetReplace runs of the G3 rule
wolframscript -file scripts/run_seeds_v3.wl
wolframscript -file scripts/causal_dimension.wl
wolframscript -file scripts/grid3d_test.wl

# Python runs in two update orders
cd scripts/python && python3 run_all_seeds.py
python3 setreplace_order.py --tie pos

# G3 eq. 342 on S² and S³
wolframscript -file scripts/test_eq342.wl
```

## License

MIT, see [`LICENSE.md`](LICENSE.md). The papers in `papers/` belong to their authors and are included for reference.
