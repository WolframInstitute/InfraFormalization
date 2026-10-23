/-
Branchial-contention Knill values at depth 6 for two rule pairs.

`discreteBranchialDensity sys d` is the scaled Knill Euler
characteristic of `branchialDAGOfFireAll sys seedEdge12 d`. That graph
joins two events of the same step that consume a common edge. It is
not the Wolfram-model branchial graph. The evolution is `fireAllStep`,
which applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

Values for `edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`
(PROVED-WITH-NATIVE-DECIDE; depth 6 here, depths 2 to 5 in
`PersistentScalingExponent` and `PersistentBEquivalence`):

  | d | 3^(d+1) - 3 | B (both pairs) |
  |---|-------------|----------------|
  | 2 |      24     |       24       |
  | 3 |      78     |       78       |
  | 4 |     240     |      240       |
  | 5 |     726     |      726       |
  | 6 |    2184     |     2184       |

The equality `B(d) = 3^(d+1) - 3` for all `d ≥ 2` is OPEN. No theorem
in the library states it for unbounded `d`. The module states no
continuum limit and no relation to `bbhInitial` at depth 6.
-/

import InfraFormalization.PersistentScalingExponent

namespace InfraFormalization
namespace BClosedFormExtended

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open BranchialUniversalAdditivity

/-! ## B(d=6) = 2184 = 3^7 - 3 -/

theorem B_d6_eR_tripleMerger :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 6 = 2184 := by
  native_decide

theorem B_d6_fork_dCyc :
    discreteBranchialDensity fork_doubleCycle_Sys 6 = 2184 := by
  native_decide

/-! ## The form 3^(d+1) - 3 at depth 6 -/

/-- `B_closed_form_d6`: `discreteBranchialDensity` at depth 6 equals
`3^7 - 3` for `edgeReversal_tripleMerger_Sys` and for
`fork_doubleCycle_Sys`. -/
theorem B_closed_form_d6 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 6 = 3^7 - 3 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 6 = 3^7 - 3 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Equal B at depths 2 to 6 -/

/-- `persistent_B_equivalence_5_depths`: `edgeReversal_tripleMerger_Sys`
and `fork_doubleCycle_Sys` have equal `discreteBranchialDensity` at
each of the depths 2, 3, 4, 5, 6. -/
theorem persistent_B_equivalence_5_depths :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 =
      discreteBranchialDensity fork_doubleCycle_Sys 2 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 =
      discreteBranchialDensity fork_doubleCycle_Sys 4 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 =
      discreteBranchialDensity fork_doubleCycle_Sys 5 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 6 =
      discreteBranchialDensity fork_doubleCycle_Sys 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

  * `B_closed_form_d6`: both pairs give `B = 3^7 - 3 = 2184` at depth 6.
  * `persistent_B_equivalence_5_depths`: the two pairs give equal B at
    each of the depths 2, 3, 4, 5, 6.
-/

end BClosedFormExtended
end InfraFormalization
