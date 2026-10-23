/-
Causal and contention Knill values of `fork_doubleCycle_Sys` on
`bbhInitial` at depths 3 and 4.

R denotes the scaled Knill Euler characteristic of
`causalDAGOfFireAll sys bbhInitial d`. B denotes the scaled Knill
Euler characteristic of `branchialDAGOfFireAll sys bbhInitial d`.
`branchialDAGOfFireAll` joins two events of the same step that
consume a common edge. It is not the Wolfram-model branchial graph.

The evolution is `fireAllStep`, which applies every match of every
rule found in the state, including matches that share edges. It is
not a Wolfram model update when matches overlap. The name "vacuum" in
this module is a label for R = 0. The module defines no metric, field
equation or quantum state.

Values (PROVED-WITH-NATIVE-DECIDE):

  | d | R on bbhInitial | B on bbhInitial | 7 · B on seedEdge12 |
  |---|-----------------|-----------------|---------------------|
  | 3 |        0        |       546       |      7·78 = 546     |
  | 4 |        0        |      1680       |     7·240 = 1680    |
-/

import InfraFormalization.VacuumLikeUniversal
import InfraFormalization.BBHInitialData

namespace InfraFormalization
namespace BBHVacuumRegime

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open BBHInitialData
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## Values on bbhInitial -/

theorem bbh_vacuum_R_3 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) = 0 := by
  native_decide

theorem bbh_vacuum_R_4 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) = 0 := by
  native_decide

theorem bbh_vacuum_B_3 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) = 546 := by
  native_decide

theorem bbh_vacuum_B_4 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) = 1680 := by
  native_decide

/-! ## Four-part conjunction -/

/-- `bbh_vacuum_regime_certified`: for `fork_doubleCycle_Sys` on
`bbhInitial`, R = 0 at depths 3 and 4, and B equals 7 times
`discreteBranchialDensity` (the B value on `seedEdge12`) at depths 3
and 4. -/
theorem bbh_vacuum_regime_certified :
    -- R = 0 on bbhInitial:
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) = 0 ∧
    -- B on bbhInitial = 7 × B on seedEdge12:
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) =
      7 * discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) =
      7 * discreteBranchialDensity fork_doubleCycle_Sys 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- `bbh_vacuum_B_growth`: for `fork_doubleCycle_Sys` on
`bbhInitial`, B at depth 4 (1680) exceeds B at depth 3 (546), and R
at depth 3 equals R at depth 4 (both 0). -/
theorem bbh_vacuum_B_growth :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) >
      knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) =
      knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) := by
  refine ⟨?_, ?_⟩
  · rw [bbh_vacuum_B_4, bbh_vacuum_B_3]; decide
  · rw [bbh_vacuum_R_3, bbh_vacuum_R_4]

/-! ## Summary

  * `bbh_vacuum_regime_certified`: R = 0 and B = 7 · B(seedEdge12)
    on `bbhInitial` at depths 3 and 4.
  * `bbh_vacuum_B_growth`: B at depth 4 exceeds B at depth 3, and R
    is equal at both depths.

All statements concern one rule pair, one seed and depths 3 and 4.
-/

end BBHVacuumRegime
end InfraFormalization
