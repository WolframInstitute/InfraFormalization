/-
The pair (R, B) for a rule system and depth, with derived integers.

R is `discreteRicciScalar sys d`, the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 d`. B is
`discreteBranchialDensity sys d`, the scaled Knill Euler characteristic
of `branchialDAGOfFireAll sys seedEdge12 d`. The branchial graph joins
two events of the same step that consume a common edge. It is not the
Wolfram-model branchial graph. The evolution is `fireAllStep`, which
applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

Definitions:

  * `discreteMetricTensor sys d := (R, B)`.
  * `discreteDet sys d := R * B`.
  * `discreteTrace sys d := R + B`.
  * `hasLorentzianSignature sys d`: R and B have opposite signs.
  * `discreteLineElement sys d dτ dχ := R·dτ² + B·dχ²`.

The names are labels. The module defines no manifold, no tangent space
and no metric in the sense of differential geometry, and proves no
relation to one.
-/

import InfraFormalization.DualSideIndependence

namespace InfraFormalization
namespace DiscreteMetricTensor

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## The pair (R, B) -/

/-- `discreteMetricTensor sys d`: the pair
`(discreteRicciScalar sys d, discreteBranchialDensity sys d)`. -/
def discreteMetricTensor (sys : ExecSystem) (d : Nat) : Int × Int :=
  (discreteRicciScalar sys d, discreteBranchialDensity sys d)

/-- `discreteDet sys d`: the product `R * B`. -/
def discreteDet (sys : ExecSystem) (d : Nat) : Int :=
  let (r, b) := discreteMetricTensor sys d
  r * b

/-- `discreteTrace sys d`: the sum `R + B`. -/
def discreteTrace (sys : ExecSystem) (d : Nat) : Int :=
  let (r, b) := discreteMetricTensor sys d
  r + b

/-! ## Values at depth 3 -/

/-- For `eR + id` at depth 3: `(R, B) = (-24, 30)`, `R·B = -720`,
`R + B = 6`. -/
theorem metric_eR_id_3 :
    discreteMetricTensor edgeReversal_identity_Sys 3 = (-24, 30) ∧
    discreteDet edgeReversal_identity_Sys 3 = -720 ∧
    discreteTrace edgeReversal_identity_Sys 3 = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- For `eR + fork` at depth 3: `(R, B) = (-42, 66)`, `R·B = -2772`,
`R + B = 24`. -/
theorem metric_eR_fork_3 :
    discreteMetricTensor edgeReversal_fork_Sys 3 = (-42, 66) ∧
    discreteDet edgeReversal_fork_Sys 3 = -2772 ∧
    discreteTrace edgeReversal_fork_Sys 3 = 24 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Sign test -/

/-- `hasLorentzianSignature sys d` is `true` when R and B have opposite
signs. The name is a label for this sign condition. -/
def hasLorentzianSignature (sys : ExecSystem) (d : Nat) : Bool :=
  let (r, b) := discreteMetricTensor sys d
  decide ((r < 0 ∧ b > 0) ∨ (r > 0 ∧ b < 0))

/-- `eR_id_lorentzian_at_3`: at depth 3, `eR + id` has R = -24 < 0 and
B = 30 > 0. -/
theorem eR_id_lorentzian_at_3 :
    hasLorentzianSignature edgeReversal_identity_Sys 3 = true := by
  native_decide

/-- `eR_fork_lorentzian_at_3`: at depth 3, `eR + fork` has R and B of
opposite signs. -/
theorem eR_fork_lorentzian_at_3 :
    hasLorentzianSignature edgeReversal_fork_Sys 3 = true := by
  native_decide

/-! ## One instance on seedPath123 -/

/-- `discreteMetricTensor_universal_additivity_eR_id_path`: for
`edgeReversal_identity_Sys` at depth 3 on the two-edge seed
`seedPath123`, the causal and contention Knill values equal twice the
`seedEdge12` values. The statement is this single instance. -/
theorem discreteMetricTensor_universal_additivity_eR_id_path :
    let baselineRB := discreteMetricTensor edgeReversal_identity_Sys 3
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys
      UniversalAdditivity.seedPath123 3) = 2 * baselineRB.1 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys
      UniversalAdditivity.seedPath123 3) = 2 * baselineRB.2 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## The quadratic form -/

/-- `discreteLineElement sys d dτ dχ`: the integer `R·dτ² + B·dχ²`. -/
def discreteLineElement (sys : ExecSystem) (d : Nat) (dτ dχ : Int) : Int :=
  let (r, b) := discreteMetricTensor sys d
  r * dτ * dτ + b * dχ * dχ

/-- For `eR + id` at depth 3, `discreteLineElement` at
`(dτ, dχ) = (1, 1)` is `-24 + 30 = 6`. -/
theorem lineElement_eR_id_3_at_1_1 :
    discreteLineElement edgeReversal_identity_Sys 3 1 1 = 6 := by
  native_decide

/-- For `eR + id` at depth 3, `discreteLineElement` at
`(dτ, dχ) = (2, 1)` is `-24·4 + 30 = -66`. -/
theorem lineElement_eR_id_3_at_2_1 :
    discreteLineElement edgeReversal_identity_Sys 3 2 1 = -66 := by
  native_decide

/-! ## Summary

  * `discreteMetricTensor sys d` is the pair `(R, B)`.
  * `discreteDet` is `R * B` and `discreteTrace` is `R + B`.
  * `hasLorentzianSignature` is the Bool "R and B have opposite signs".
  * `discreteLineElement sys d dτ dχ` is `R·dτ² + B·dχ²`.

Values at depth 3 (PROVED-WITH-NATIVE-DECIDE):

  * `metric_eR_id_3`: `(R, B) = (-24, 30)`, product -720, sum 6.
  * `metric_eR_fork_3`: `(R, B) = (-42, 66)`, product -2772, sum 24.
  * `eR_id_lorentzian_at_3`, `eR_fork_lorentzian_at_3`: R and B have
    opposite signs for both rule pairs.
  * `discreteMetricTensor_universal_additivity_eR_id_path`: on
    `seedPath123` both components equal twice the `seedEdge12` value.
  * `lineElement_eR_id_3_at_1_1` (value 6) and
    `lineElement_eR_id_3_at_2_1` (value -66).

The names "metric", "signature" and "line element" are labels. The
module proves no relation between these integers and a metric on a
manifold.
-/

end DiscreteMetricTensor
end InfraFormalization
