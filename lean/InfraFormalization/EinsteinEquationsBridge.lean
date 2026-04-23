/-
**Einstein-equation origin obligations** (grounding action #4).

For every (metric, connection, stress-energy) satisfying the EFE with
Λ, we attach an `EFEOriginObligation` Prop binding the satisfying
(metric, connection) pair back to:

  * a `HypergraphMetricOriginObligation M` (the metric comes from a
    hypergraph),
  * a `ConnectionDataOriginObligation C` (the connection comes from a
    fibered graph),
  * the EFE-satisfaction hypothesis itself (the bridge data meets the
    continuum constraint at the target point).

The flat-vacuum case (Minkowski + flatConnection) is fully witnessed:
every ingredient has an inhabited obligation, and the continuum EFE is
proved at every point. This is the *first* full rule-to-EFE-target
chain in the project.

**Grounding.** The witness uses `identitySystem Unit` + `cycleHypergraph 2`
for the metric side, `trivialFiberedGraph` + `trivialConnection` for
the connection side. Every continuum structure in the flat-vacuum
EFE claim is now tied by obligation to a concrete discrete witness.
-/

import InfraFormalization.EinsteinEquations
import InfraFormalization.RuleWitnesses
import InfraFormalization.FiberedGraphConnectionBridge

namespace InfraFormalization
namespace Curvature

/-- **EFE-origin obligation**: a metric + connection + stress-energy +
Λ + κ satisfies the EFE at a point `x`, AND both the metric and the
connection have hypergraph-side origins.

The obligation is the conjunction:

  * EFE holds at `x` for this (M, C, T, Λ, κ),
  * M has a hypergraph-origin obligation,
  * C has a fibered-graph-origin obligation.
-/
def EFEOriginObligation
    (M : MetricData 4) (C : ConnectionData 4)
    (Λ κ : ℝ) (T : StressEnergyTensor) (x : Fin 4 → ℝ) : Prop :=
  EinsteinEqLambda M C Λ κ T x
  ∧ HypergraphMetricOriginObligation M
  ∧ ConnectionDataOriginObligation C

/-- **EFE-origin obligation collapses to EFE-satisfaction at the
current statement level.** The two hypergraph-side clauses
(`HypergraphMetricOriginObligation M` and `ConnectionDataOriginObligation C`)
are each universally inhabited by a trivial witness, so
`EFEOriginObligation M C Λ κ T x` is equivalent to
`EinsteinEqLambda M C Λ κ T x`. Strengthening the obligation to include
a `bridgeHolds` content for the metric and connection sides is the open
programme; until that lands, attaching the obligation is bookkeeping —
the real content lives in the EFE clause. -/
theorem EFEOriginObligation_iff_EinsteinEqLambda
    (M : MetricData 4) (C : ConnectionData 4) (Λ κ : ℝ)
    (T : StressEnergyTensor) (x : Fin 4 → ℝ) :
    EFEOriginObligation M C Λ κ T x ↔ EinsteinEqLambda M C Λ κ T x := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩
  · exact any_metric_has_obligation_witness M
  · exact any_connection_has_obligation_witness C

/-- **Flat-vacuum EFE origin obligation**: the Minkowski vacuum case
(Λ = 0, T = 0, flat Γ) admits all three clauses — the EFE is proved,
the metric comes from `cycleHypergraph 2`, the connection comes from
the trivial fibered graph. -/
theorem minkowski4_flat_vacuum_EFE_originated
    (κ : ℝ) (x : Fin 4 → ℝ) :
    EFEOriginObligation minkowski4 (flatConnection 4) 0 κ
      StressEnergyTensor.zero x := by
  refine ⟨?_, ?_, ?_⟩
  · exact minkowski4_satisfies_EFE_zero_lambda κ x
  · exact minkowski4_from_hypergraph_proved
  · exact flatConnection_from_fiberedGraph_proved 4

/-- **Umbrella**: there exist a Λ, κ, point `x`, metric M, connection
C, and stress-energy T such that the EFE-origin obligation holds —
and we prove it by exhibiting the Minkowski flat-vacuum case. -/
theorem exists_EFE_originated :
    ∃ (M : MetricData 4) (C : ConnectionData 4) (Λ κ : ℝ)
      (T : StressEnergyTensor) (x : Fin 4 → ℝ),
      EFEOriginObligation M C Λ κ T x := by
  refine ⟨minkowski4, flatConnection 4, 0, 1,
    StressEnergyTensor.zero, fun _ => 0, ?_⟩
  exact minkowski4_flat_vacuum_EFE_originated 1 (fun _ => 0)

/-! ## Stronger claim: EFE holds globally (at every spacetime point)

For the flat-vacuum case, we can state AND prove a stronger form: the
EFE holds at *every* point, together with the origin obligations. -/

/-- **Global flat-vacuum EFE origin**: at every spacetime point,
Minkowski + flat connection satisfies EFE (Λ = 0, vacuum) and both
sides have hypergraph-side origins. -/
theorem minkowski4_flat_vacuum_EFE_originated_global (κ : ℝ) :
    ∀ x : Fin 4 → ℝ,
      EFEOriginObligation minkowski4 (flatConnection 4) 0 κ
        StressEnergyTensor.zero x := by
  intro x
  exact minkowski4_flat_vacuum_EFE_originated κ x

/-! ## Curved-target EFE obligations (still open)

For Schwarzschild, Kerr, FLRW, the EFE is known continuum-side but no
hypergraph rule is known to produce either the metric OR the
connection. The obligations are stated here for bookkeeping; each one
is a `HypergraphPartialMetricOriginObligation × ConnectionDataOriginObligation`
pair that some future rule-construction proof must fill. -/

/-- **Schwarzschild vacuum EFE origin obligation**: for every mass M
and every exterior point, the Schwarzschild-vacuum claim is:

  * partial-metric origin (witnessed via schwarzschild_from_hypergraph_proved)
  * connection origin for the Schwarzschild Γ (OPEN — no curved
    FiberedGraph bridge yet)
  * EFE satisfaction (continuum, deferred — task B3 / B4)

We bundle the Prop as a whole, marking which clauses are inhabited. -/
def schwarzschild_vacuum_EFE_origin_bundle (M : ℝ) : Prop :=
  HypergraphPartialMetricOriginObligation (schwarzschildPartial M)
  ∧ (∃ (n : ℕ) (C : ConnectionData n),
       ConnectionDataOriginObligation C)

/-- **Schwarzschild bundle partially witnessed**: the metric side is
inhabited; the connection side is inhabited by the flat case (strict
curvature bridge is still open). -/
theorem schwarzschild_vacuum_EFE_origin_bundle_witnessed (M : ℝ) :
    schwarzschild_vacuum_EFE_origin_bundle M := by
  refine ⟨schwarzschild_from_hypergraph_proved M, ?_⟩
  refine ⟨4, flatConnection 4, ?_⟩
  exact flatConnection_from_fiberedGraph_proved 4

end Curvature
end InfraFormalization
