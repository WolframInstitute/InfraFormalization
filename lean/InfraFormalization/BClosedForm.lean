/-
Values of `discreteBranchialDensity` for two two-rule systems at depths
2 to 5, compared with `3^(d+1) - 3`.

`discreteBranchialDensity sys d` is the scaled Knill value of
`branchialDAGOfFireAll sys seedEdge12 d`. The trace comes from
`tracedFireAllEvolve`, which applies every match of every rule found in
the state, including matches that share edges. It is not a Wolfram model
update when matches overlap. The contention relation links two events of
the same step that consume a common edge value. It is not the branchial
graph of the Wolfram model.

The module proves by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | d | `3^(d+1) - 3` | `edgeReversal + tripleMerger` | `forkRule_2 + doubleCycle_5` |
  |---|---------------|-------------------------------|------------------------------|
  | 2 |  24           |  24                           |  24                          |
  | 3 |  78           |  78                           |  not computed in this module |
  | 4 | 240           | 240                           |  not computed in this module |
  | 5 | 726           | 726                           | 726                          |

The equality for all d is OPEN. It is the statement
`∀ d, discreteBranchialDensity edgeReversal_tripleMerger_Sys d = 3^(d+1) - 3`,
which this module does not prove.
-/

import InfraFormalization.PersistentBEquivalence

namespace InfraFormalization
namespace BClosedForm

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

/-! ## Values compared with `3^(d+1) - 3` -/

/-- `discreteBranchialDensity edgeReversal_tripleMerger_Sys 2` equals 3^3 - 3 = 24. -/
theorem B_closed_form_d2 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 = 3^3 - 3 := by
  native_decide

/-- `discreteBranchialDensity edgeReversal_tripleMerger_Sys 3` equals 3^4 - 3 = 78. -/
theorem B_closed_form_d3 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 3^4 - 3 := by
  native_decide

/-- `discreteBranchialDensity edgeReversal_tripleMerger_Sys 4` equals 3^5 - 3 = 240. -/
theorem B_closed_form_d4 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 = 3^5 - 3 := by
  native_decide

/-- `discreteBranchialDensity edgeReversal_tripleMerger_Sys 5` equals 3^6 - 3 = 726. -/
theorem B_closed_form_d5 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 = 3^6 - 3 := by
  native_decide

/-! ## Six finite equalities -/

/-- The four values for `edgeReversal + tripleMerger` at depths 2, 3, 4
and 5 equal `3^(d+1) - 3`, and the values for `forkRule_2 + doubleCycle_5`
at depths 2 and 5 equal `3^3 - 3` and `3^6 - 3`. -/
theorem B_closed_form_persistent_class :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 = 3^3 - 3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 3^4 - 3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 = 3^5 - 3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 = 3^6 - 3 ∧
    -- fork + dCyc at depths 2 and 5:
    discreteBranchialDensity fork_doubleCycle_Sys 2 = 3^3 - 3 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 5 = 3^6 - 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `B_closed_form_d2` to `B_closed_form_d5`: the four values for
    `edgeReversal + tripleMerger` at depths 2 to 5.
  * `B_closed_form_persistent_class`: those four values together with
    the values for `forkRule_2 + doubleCycle_5` at depths 2 and 5.

The module proves six finite equalities. It states nothing about other
depths, about a limit as d grows, or about any seed other than
`seedEdge12`.
-/

end BClosedForm
end InfraFormalization
