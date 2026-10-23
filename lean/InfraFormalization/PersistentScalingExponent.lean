/-
The values `B(d) + 3 = 3^(d+1)` at d = 2 to 5 for one rule pair, and
the open all-depth statement.

B is `discreteBranchialDensity edgeReversal_tripleMerger_Sys d`, the
scaled Knill Euler characteristic of `branchialDAGOfFireAll` on
`seedEdge12`. That graph joins two events of the same step that
consume a common edge. It is not the Wolfram-model branchial graph.
The evolution is `fireAllStep`, which applies every match of every
rule found in the state, including matches that share edges. It is
not a Wolfram model update when matches overlap.

PROVED-WITH-NATIVE-DECIDE: `B(d) + 3 = 3^(d+1)` at d = 2, 3, 4, 5.

OPEN: `PersistentScalingExponentConjecture`, the same identity for
every `d ≥ 2`.

If the identity held for every d, then `B(d)` would grow as `3^(d+1)`.
The exponent `log₂ 3` arises only under an identification of depth d
with `-log₂ h` for a spacing h. The library defines no spacing h and no
continuum limit, so no exponent in h is stated or proved.
-/

import InfraFormalization.BClosedForm

namespace InfraFormalization
namespace PersistentScalingExponent

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity
open BClosedForm

/-! ## B(d) + 3 = 3^(d+1) at d = 2, 3, 4, 5 -/

/-- `scaling_exponent_3_d2`: at d=2, `B(d) + 3 = 3^(d+1) = 27`. -/
theorem scaling_exponent_3_d2 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 + 3 = 3^3 := by
  native_decide

/-- `scaling_exponent_3_d3`: at d=3, `B(d) + 3 = 3^(d+1) = 81`. -/
theorem scaling_exponent_3_d3 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 + 3 = 3^4 := by
  native_decide

/-- `scaling_exponent_3_d4`: at d=4, `B(d) + 3 = 3^(d+1) = 243`. -/
theorem scaling_exponent_3_d4 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 + 3 = 3^5 := by
  native_decide

/-- `scaling_exponent_3_d5`: at d=5, `B(d) + 3 = 3^(d+1) = 729`. -/
theorem scaling_exponent_3_d5 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 + 3 = 3^6 := by
  native_decide

/-! ## Four values and three products -/

/-- `persistent_class_scaling_form`: for `edgeReversal_tripleMerger_Sys`,
`B(d) + 3` equals 27, 81, 243, 729 at d = 2, 3, 4, 5, together with the
integer identities `81 = 3 * 27`, `243 = 3 * 81`, `729 = 3 * 243`. -/
theorem persistent_class_scaling_form :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 + 3 = 27 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 + 3 = 81 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 + 3 = 243 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 + 3 = 729 ∧
    -- 3^3 * 3 = 81, 3^4 * 3 = 243, 3^5 * 3 = 729:
    81 = 3 * 27 ∧
    243 = 3 * 81 ∧
    729 = 3 * 243 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## The all-depth statement -/

/-- `PersistentScalingExponentConjecture` (OPEN): for every `d ≥ 2`,
`discreteBranchialDensity edgeReversal_tripleMerger_Sys d + 3 = 3^(d+1)`.
No theorem in the library proves it. -/
def PersistentScalingExponentConjecture : Prop :=
  ∀ d ≥ 2, discreteBranchialDensity edgeReversal_tripleMerger_Sys d + 3 = 3^(d+1)

/-- `PersistentScalingExponentConjecture_verified_through_5`: the
instances d = 2, 3, 4, 5 of `PersistentScalingExponentConjecture`. -/
theorem PersistentScalingExponentConjecture_verified_through_5 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 + 3 = 3^3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 + 3 = 3^4 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 + 3 = 3^5 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 + 3 = 3^6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

  * `persistent_class_scaling_form`: `B(d) + 3` is 27, 81, 243, 729 at
    d = 2, 3, 4, 5, with the three arithmetic identities
    `81 = 3·27`, `243 = 3·81`, `729 = 3·243`.
  * `PersistentScalingExponentConjecture`: the Prop
    `∀ d ≥ 2, B(d) + 3 = 3^(d+1)` for `edgeReversal_tripleMerger_Sys`.
    It is OPEN.
  * `PersistentScalingExponentConjecture_verified_through_5`: its
    instances d = 2, 3, 4, 5.
-/

end PersistentScalingExponent
end InfraFormalization
