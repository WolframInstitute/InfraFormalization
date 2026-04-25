/-
Top-level module of the `InfraFormalization` Lean library.

**Purpose.** Formalize the mechanics of directed hypergraph rewriting
in a way that supports proving continuum-limit theorems — and use that
machinery to formally state, where possible, refutations of Gorard's
2004.14810 / 2102.09363 / 2303.07282 claims that survive the
project's multi-rail verification (see ../README.md).

Layout grouped by phase:

  * **Core hypergraph rewriting:**
    `Hypergraph`, `Rule`, `Application`, `Conservation`, `Multiway`,
    `Causal`, `CausalLevel`, `Branchial`, `ParallelSchedule`, `Demo`.

  * **Continuum-limit infrastructure:**
    `GraphMetric`, `Growth`, `Limit`, and the `Infra/*` submodules
    (cycle / path / torus GH bounds, Lorentz lattice, Minkowski,
    bridging theorems).

  * **Refutations of Gorard's structural flaws:**
    `Refutations/F1NoMetric`, `F2Orthonormality`, `F3Tautology`,
    `F4Tautology`, `F5Illdefined`.

  * **Discrete calculus (Rung 1 of the bridge ladder):**
    `DiscreteCalculus`, `DiscreteCalculusSymm`, `CycleGraph`.

The `AxiomCheck` module imports everything and certifies the
axiom-cleanliness of every proved theorem.
-/

-- Core hypergraph rewriting
import InfraFormalization.Hypergraph
import InfraFormalization.Rule
import InfraFormalization.Application
import InfraFormalization.Conservation
import InfraFormalization.Multiway
import InfraFormalization.MultiwayExec
import InfraFormalization.MultiwayExecTests
import InfraFormalization.Causal
import InfraFormalization.CausalLevel
import InfraFormalization.Branchial
import InfraFormalization.ParallelSchedule
import InfraFormalization.Demo

-- Continuum-limit infrastructure
import InfraFormalization.GraphMetric
import InfraFormalization.Growth
import InfraFormalization.Limit
import InfraFormalization.Infra.ScaledCycle
import InfraFormalization.Infra.LatticeDensity
import InfraFormalization.Infra.Circle
import InfraFormalization.Infra.GHBound
import InfraFormalization.Infra.GHApprox
import InfraFormalization.Infra.ScaledPath
import InfraFormalization.Infra.ScaledTorus
import InfraFormalization.Infra.ScaledTorusD
import InfraFormalization.Infra.OllivierStatement
import InfraFormalization.Infra.GrayTubeStatement
import InfraFormalization.Infra.LorentzLattice
import InfraFormalization.Infra.TrajectoryLorentz
import InfraFormalization.Infra.TrajectoryLorentzD
import InfraFormalization.Infra.Minkowski
import InfraFormalization.Infra.ScaledLorentz
import InfraFormalization.Infra.FullBridge

-- Refutations of Gorard structural flaws F1-F5
import InfraFormalization.Refutations.F1NoMetric
import InfraFormalization.Refutations.F2Orthonormality
import InfraFormalization.Refutations.F3Tautology
import InfraFormalization.Refutations.F4Tautology
import InfraFormalization.Refutations.F5Illdefined
import InfraFormalization.Refutations.F6Circularity
import InfraFormalization.Refutations.F7NamedRuleStructure
import InfraFormalization.StressEnergyTensor
import InfraFormalization.WolframPhysicsBridgeDemo

-- Discrete calculus (Rung 1 of the bridge ladder)
import InfraFormalization.DiscreteCalculus
import InfraFormalization.DiscreteCalculusSymm
import InfraFormalization.CycleGraph
import InfraFormalization.SecondDifference
import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann
import InfraFormalization.VectorBundleConnection
import InfraFormalization.Schwarzschild
import InfraFormalization.DiscreteRicci
import InfraFormalization.RicciBridge
import InfraFormalization.LaplacianBridge
import InfraFormalization.HypergraphLaplacian
import InfraFormalization.HypergraphCalculus
import InfraFormalization.HeatEquation
import InfraFormalization.WaveEquation
import InfraFormalization.SchrodingerEquation
import InfraFormalization.KleinGordon
import InfraFormalization.ScalarField
import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.HypergraphDistance
import InfraFormalization.HypergraphMeasure
import InfraFormalization.RuleDimensionBounds
import InfraFormalization.FiberedGraph
import InfraFormalization.HypergraphConnection
import InfraFormalization.MultiwayCausalGraph
import InfraFormalization.PathIntegralCausalGraph
import InfraFormalization.ScaledConnectionLimit
import InfraFormalization.RicciSymmetry
import InfraFormalization.DiscreteGaugeField
import InfraFormalization.CausalSetComparison
import InfraFormalization.RuleSignatureScreens
import InfraFormalization.WassersteinRate
import InfraFormalization.MeasureTorusLift
import InfraFormalization.LQGComparison
import InfraFormalization.ContinuumFieldLimits
import InfraFormalization.EmergentGravity
import InfraFormalization.AdSCFTAnalog
import InfraFormalization.LorentzianGH
import InfraFormalization.CausalDAGContinuumLimit
import InfraFormalization.ScaledTrajectoryLimit
import InfraFormalization.CurvedRicciExtensions
import InfraFormalization.WarpedDiag2C2
import InfraFormalization.WassersteinFinite
import InfraFormalization.CycleWasserstein
import InfraFormalization.PathWasserstein
import InfraFormalization.CandidateRuleCatalog
import InfraFormalization.RiemannianManifold
import InfraFormalization.CausalGraphType
import InfraFormalization.CausalFoliation
import InfraFormalization.BranchialFinite
import InfraFormalization.VietorisRips
import InfraFormalization.SyntheticGeometry
import InfraFormalization.ElementaryBlowup
import InfraFormalization.DagBlowup
import InfraFormalization.Holonomy
import InfraFormalization.RuleSignature
import InfraFormalization.SpatialReconstruction
import InfraFormalization.PlateauDimension
import InfraFormalization.FiberBundle
import InfraFormalization.InfrageometricScene
import InfraFormalization.StructuralRuleBounds
import InfraFormalization.SyntheticAxiomatic
import InfraFormalization.HomologyDimension
import InfraFormalization.CausalDimension
import InfraFormalization.EPSAxioms
import InfraFormalization.DeRham
import InfraFormalization.MultiFibrationProjection
import InfraFormalization.FormCochainIntegration
import InfraFormalization.BlowupOperations
import InfraFormalization.CoordinatizationDimension
import InfraFormalization.CandidateRuleDatabase
import InfraFormalization.MarzkeWheeler
import InfraFormalization.BlowupLieAlgebra
import InfraFormalization.DagCalculus
import InfraFormalization.RadialLaminarBlowup
import InfraFormalization.HodgeVR
import InfraFormalization.FisherMetric
import InfraFormalization.RemainingObligations
import InfraFormalization.CycleSpectrum
import InfraFormalization.CTwoTaylor
import InfraFormalization.CycleEigenLimit
import InfraFormalization.ScaledDiffC2Bridge
import InfraFormalization.LaplacianMatrix
import InfraFormalization.HeatKernelODE
import InfraFormalization.HeatEquationUniqueness
import InfraFormalization.ExpEigenvector
import InfraFormalization.CycleMatrixSpectrum
import InfraFormalization.CycleHasEigenvalue
import InfraFormalization.ContinuumLimitStatement
import InfraFormalization.DiscreteDAlembertian
import InfraFormalization.BranchialHilbert
import InfraFormalization.HeatKernelDecay
import InfraFormalization.SymmEigenOrthogonal
import InfraFormalization.BranchialSchrodinger
import InfraFormalization.HodgeLaplacianSpectrum
import InfraFormalization.BranchialCanonical
import InfraFormalization.PathHypergraph
import InfraFormalization.PathHypergraphDistance
import InfraFormalization.CycleHeatDecayBounds
import InfraFormalization.FisherMetricExtended
import InfraFormalization.HodgeLaplacianBounds
import InfraFormalization.BlowupPoissonConcrete
import InfraFormalization.EMETracker
import InfraFormalization.BranchialCommutator
import InfraFormalization.ProperTimeBounds
import InfraFormalization.RuleSignatureEquiv
import InfraFormalization.HypergraphMetricBridges
import InfraFormalization.CausalLorentzianBridge
import InfraFormalization.RuleWitnesses
import InfraFormalization.RuleSearch
import InfraFormalization.FiberedGraphConnectionBridge
import InfraFormalization.EinsteinEquationsBridge
import InfraFormalization.RodkeyClassification
import InfraFormalization.CurvedRicciBridge
import InfraFormalization.ContinuumBridgeDemo
import InfraFormalization.EinsteinEquations
import InfraFormalization.CovariantDerivative
import InfraFormalization.LorentzianManifold
import InfraFormalization.PartialMetricData
import InfraFormalization.FLRW
import InfraFormalization.FLRWRicci
import InfraFormalization.ReissnerNordstrom
import InfraFormalization.TwoSphere
import InfraFormalization.DeSitter
import InfraFormalization.GRMetricsDemo
import InfraFormalization.Kerr
import InfraFormalization.GrandTour
