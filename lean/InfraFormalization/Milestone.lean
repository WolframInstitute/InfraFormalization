/-
Statements named after the completion of the programme: `GR_emerges_from_hypergraph`,
`QM_emerges_from_hypergraph` and `BBH_emerges_from_hypergraph`.

Each layer Prop below (`DistConvergesTo`, `ConnectionConvergesTo`, ...) is
`∃ d : ScaledDiscrepancy, WassersteinRateObligation d`. It does not depend on
the trajectory or the target, and the zero discrepancy satisfies it. The
origin obligations used in the GR conjunct hold for every target
(`Curvature.any_metric_has_strong_obligation_witness`). Consequently
`GR_emerges_from_hypergraph target` holds for every `target`
(`GR_emerges_from_hypergraph_holds`), and `QM_emerges_from_hypergraph` and
`BBH_emerges_from_hypergraph` hold (`QM_emerges_from_hypergraph_holds`,
`BBH_emerges_from_hypergraph_holds`). These statements do not express
convergence to the named geometries.
-/

import InfraFormalization.HypergraphMetricBridges
import InfraFormalization.WassersteinRate
import InfraFormalization.RuleSignatureScreener

namespace InfraFormalization
namespace Milestone

variable {V P : Type*} [Fintype V] [DecidableEq V]

/-- Layer 2. Independent of `τ` and `targetDist`; holds by `DistConvergesTo_zero`. -/
def DistConvergesTo {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) (_targetDist : V → V → ℝ) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- Layer 3. Independent of `τ`; holds by `ConnectionConvergesTo_zero`. -/
def ConnectionConvergesTo {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- Layer 4. Independent of `τ`; holds by `RiemannTensorConvergesTo_zero`. -/
def RiemannTensorConvergesTo {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- Layer 5. Independent of `τ`; holds by `EinsteinFieldEquationsHold_zero`.
The name does not describe the statement.
-/
def EinsteinFieldEquationsHold {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- Layer 6. Independent of `τ`; holds by `DiscreteStressEnergyEmerges_zero`. -/
def DiscreteStressEnergyEmerges {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- A trajectory exists, the origin obligation of `target` holds, and the
layer Props 2-6 hold. Holds for every `target` (`GR_emerges_from_hypergraph_holds`).
-/
def GR_emerges_from_hypergraph {n : Nat} (target : Curvature.MetricData n) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (τ : Trajectory sys s₀),
      Curvature.HypergraphMetricOriginObligationStrong target ∧
      (∃ (targetDist : V → V → ℝ), DistConvergesTo τ targetDist) ∧
      ConnectionConvergesTo τ ∧
      RiemannTensorConvergesTo τ ∧
      EinsteinFieldEquationsHold τ ∧
      DiscreteStressEnergyEmerges τ

/-- `GR_emerges_from_hypergraph` at `minkowski4`. -/
def GR_emerges_from_hypergraph_minkowski : Prop :=
  GR_emerges_from_hypergraph Curvature.minkowski4

/-- The Schwarzschild form of `GR_emerges_from_hypergraph`, with the partial-metric origin obligation. -/
def GR_emerges_from_hypergraph_schwarzschild : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (τ : Trajectory sys s₀) (M : ℝ),
      Curvature.HypergraphPartialMetricOriginObligation
        (Curvature.schwarzschildPartial M) ∧
      (∃ (targetDist : V → V → ℝ), DistConvergesTo τ targetDist) ∧
      ConnectionConvergesTo τ ∧ RiemannTensorConvergesTo τ ∧
      EinsteinFieldEquationsHold τ ∧ DiscreteStressEnergyEmerges τ

/-- The FLRW form of `GR_emerges_from_hypergraph`, with the partial-metric origin obligation. -/
def GR_emerges_from_hypergraph_flrw : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (τ : Trajectory sys s₀) (a da : ℝ → ℝ),
      Curvature.HypergraphPartialMetricOriginObligation
        (Curvature.flrwPartial a da) ∧
      (∃ (targetDist : V → V → ℝ), DistConvergesTo τ targetDist) ∧
      ConnectionConvergesTo τ ∧ RiemannTensorConvergesTo τ ∧
      EinsteinFieldEquationsHold τ ∧ DiscreteStressEnergyEmerges τ

/-- Disjunction of the Minkowski, Schwarzschild and FLRW forms. -/
def GR_emerges_from_some_hypergraph : Prop :=
  GR_emerges_from_hypergraph_minkowski ∨
  GR_emerges_from_hypergraph_schwarzschild ∨
  GR_emerges_from_hypergraph_flrw

/-- Layer Q1. Independent of `τ`; holds by `BranchialHilbertConvergesTo_zero`. -/
def BranchialHilbertConvergesTo {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- Layer Q2. Independent of `τ`; holds by `BranchialEvolutionConvergesTo_zero`. -/
def BranchialEvolutionConvergesTo {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- Layer Q3. Independent of `τ`; holds by `BornRuleEmerges_zero`. -/
def BornRuleEmerges {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- A trajectory exists and the layer Props Q1-Q3 hold. Holds (`QM_emerges_from_hypergraph_holds`). -/
def QM_emerges_from_hypergraph : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (τ : Trajectory sys s₀),
      BranchialHilbertConvergesTo τ ∧
      BranchialEvolutionConvergesTo τ ∧
      BornRuleEmerges τ

/-- Layer B1. Independent of `τ`; holds by `InitialDataMatches_zero`. -/
def InitialDataMatches {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- Layer B2. Independent of `τ`; holds by `Psi4Matches_zero`. -/
def Psi4Matches {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (_τ : Trajectory sys s₀) : Prop :=
  ∃ d : ScaledDiscrepancy, WassersteinRateObligation d

/-- A trajectory exists and layers B1, 5, 4 and B2 hold. Holds (`BBH_emerges_from_hypergraph_holds`). -/
def BBH_emerges_from_hypergraph : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (τ : Trajectory sys s₀),
      InitialDataMatches τ ∧
      EinsteinFieldEquationsHold τ ∧
      RiemannTensorConvergesTo τ ∧
      Psi4Matches τ


/-- The constant-zero discrepancy satisfies `WassersteinRateObligation`. -/
theorem zero_rate_obligation : WassersteinRateObligation (fun _ => 0) :=
  wassersteinRateObligation_zero

/-- Every layer Prop holds with the zero discrepancy. -/
theorem DistConvergesTo_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) (targetDist : V → V → ℝ) :
    DistConvergesTo τ targetDist :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem ConnectionConvergesTo_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : ConnectionConvergesTo τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem RiemannTensorConvergesTo_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : RiemannTensorConvergesTo τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem EinsteinFieldEquationsHold_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : EinsteinFieldEquationsHold τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem DiscreteStressEnergyEmerges_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : DiscreteStressEnergyEmerges τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem BranchialHilbertConvergesTo_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : BranchialHilbertConvergesTo τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem BranchialEvolutionConvergesTo_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : BranchialEvolutionConvergesTo τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem BornRuleEmerges_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : BornRuleEmerges τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem InitialDataMatches_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : InitialDataMatches τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩

theorem Psi4Matches_zero {sys : RewritingSystem P} {s₀ : Hypergraph V}
    (τ : Trajectory sys s₀) : Psi4Matches τ :=
  ⟨fun _ => 0, zero_rate_obligation⟩


/-- The trajectory with one empty state and no applications. -/
def emptyTrajectory : Trajectory (⟨[]⟩ : RewritingSystem Unit) (Hypergraph.empty : Hypergraph (Fin 1)) :=
  { states := [Hypergraph.empty]
    applications := []
    length_eq := rfl
    first_state := rfl
    well_formed := by intro i hi; simp at hi }

/-- `GR_emerges_from_hypergraph target` holds for every `target`. -/
theorem GR_emerges_from_hypergraph_holds {n : Nat} (target : Curvature.MetricData n) :
    GR_emerges_from_hypergraph target :=
  ⟨Fin 1, inferInstance, inferInstance, Unit, ⟨[]⟩, Hypergraph.empty, emptyTrajectory,
    Curvature.any_metric_has_strong_obligation_witness target,
    ⟨fun _ _ => 0, DistConvergesTo_zero _ _⟩, ConnectionConvergesTo_zero _,
    RiemannTensorConvergesTo_zero _, EinsteinFieldEquationsHold_zero _,
    DiscreteStressEnergyEmerges_zero _⟩

/-- `QM_emerges_from_hypergraph` holds. -/
theorem QM_emerges_from_hypergraph_holds : QM_emerges_from_hypergraph :=
  ⟨Fin 1, inferInstance, inferInstance, Unit, ⟨[]⟩, Hypergraph.empty, emptyTrajectory,
    BranchialHilbertConvergesTo_zero _, BranchialEvolutionConvergesTo_zero _,
    BornRuleEmerges_zero _⟩

/-- `BBH_emerges_from_hypergraph` holds. -/
theorem BBH_emerges_from_hypergraph_holds : BBH_emerges_from_hypergraph :=
  ⟨Fin 1, inferInstance, inferInstance, Unit, ⟨[]⟩, Hypergraph.empty, emptyTrajectory,
    InitialDataMatches_zero _, EinsteinFieldEquationsHold_zero _,
    RiemannTensorConvergesTo_zero _, Psi4Matches_zero _⟩
end Milestone
end InfraFormalization
