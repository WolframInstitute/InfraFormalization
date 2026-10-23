/-
Branchial-contention Knill values of five rule pairs at depth 2.

`discreteBranchialDensity sys d` (B) is the scaled Knill Euler
characteristic of `branchialDAGOfFireAll sys seedEdge12 d`. That graph
joins two events of the same step that consume a common edge. It is
not the Wolfram-model branchial graph. The evolution is `fireAllStep`,
which applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

At depth 2 the five pairs take two values (PROVED-WITH-NATIVE-DECIDE):

  | B(d=2) | Rule pairs                                      |
  |--------|--------------------------------------------------|
  |  18    | eR + identityKeep, eR + doubleCycle_5            |
  |  24    | eR + forkRule_2, eR + tripleMerger, fork + dCyc  |

The statements concern depth 2 only.
-/

import InfraFormalization.BCoincidenceFinding

namespace InfraFormalization
namespace BEquivalenceClasses

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

/-! ## Depth-2 B values for the five rule pairs -/

theorem B_d2_eR_id : discreteBranchialDensity edgeReversal_identity_Sys 2 = 18 := by
  native_decide

theorem B_d2_eR_dCyc : discreteBranchialDensity edgeReversal_doubleCycle_Sys 2 = 18 := by
  native_decide

theorem B_d2_eR_fork : discreteBranchialDensity edgeReversal_fork_Sys 2 = 24 := by
  native_decide

theorem B_d2_eR_tripleMerger : discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 = 24 := by
  native_decide

theorem B_d2_fork_dCyc : discreteBranchialDensity fork_doubleCycle_Sys 2 = 24 := by
  native_decide

/-! ## Class A: B = 18 -/

/-- `B_equivalence_class_18`: at depth 2, `edgeReversal_identity_Sys`
and `edgeReversal_doubleCycle_Sys` have equal B, and the value is 18. -/
theorem B_equivalence_class_18 :
    discreteBranchialDensity edgeReversal_identity_Sys 2 =
      discreteBranchialDensity edgeReversal_doubleCycle_Sys 2 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 2 = 18 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Class B: B = 24 -/

/-- `B_equivalence_class_24`: at depth 2, `edgeReversal_fork_Sys`,
`edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys` have equal
B, and the value is 24. -/
theorem B_equivalence_class_24 :
    discreteBranchialDensity edgeReversal_fork_Sys 2 =
      discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 ∧
    discreteBranchialDensity edgeReversal_fork_Sys 2 =
      discreteBranchialDensity fork_doubleCycle_Sys 2 ∧
    discreteBranchialDensity edgeReversal_fork_Sys 2 = 24 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## The two-class partition -/

/-- `B_partition_at_d2`: at depth 2, `edgeReversal_identity_Sys` and
`edgeReversal_doubleCycle_Sys` give B = 18; `edgeReversal_fork_Sys`,
`edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys` give
B = 24; and the value for `edgeReversal_identity_Sys` differs from the
value for `edgeReversal_fork_Sys`. -/
theorem B_partition_at_d2 :
    -- Class 18:
    discreteBranchialDensity edgeReversal_identity_Sys 2 = 18 ∧
    discreteBranchialDensity edgeReversal_doubleCycle_Sys 2 = 18 ∧
    -- Class 24:
    discreteBranchialDensity edgeReversal_fork_Sys 2 = 24 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 = 24 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 2 = 24 ∧
    -- Classes are disjoint:
    discreteBranchialDensity edgeReversal_identity_Sys 2 ≠
      discreteBranchialDensity edgeReversal_fork_Sys 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

  * `B_equivalence_class_18`: two pairs give B = 18 at depth 2.
  * `B_equivalence_class_24`: three pairs give B = 24 at depth 2.
  * `B_partition_at_d2`: the five values at depth 2, and 18 ≠ 24.

Whether the same grouping holds at other depths is OPEN in this module.
-/

end BEquivalenceClasses
end InfraFormalization
