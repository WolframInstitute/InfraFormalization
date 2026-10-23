/-
Values of `discreteBranchialDensity` for five two-rule systems at depths
3 and 4, grouped by the depth-2 values of `BEquivalenceClasses`.

`discreteBranchialDensity sys d` is the scaled Knill value of
`branchialDAGOfFireAll sys seedEdge12 d`. The trace comes from
`tracedFireAllEvolve`, which applies every match of every rule found in
the state, including matches that share edges. It is not a Wolfram model
update when matches overlap. The contention relation links two events of
the same step that consume a common edge value. It is not the branchial
graph of the Wolfram model.

At depth 2 (`BEquivalenceClasses`), `edgeReversal + identityKeep` and
`edgeReversal + doubleCycle_5` have value 18, and
`edgeReversal + forkRule_2`, `edgeReversal + tripleMerger` and
`forkRule_2 + doubleCycle_5` have value 24.

This module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | System                      | d=3 | d=4                         |
  |-----------------------------|-----|-----------------------------|
  | edgeReversal + identityKeep |  30 | not computed here           |
  | edgeReversal + doubleCycle_5|  42 | not computed here           |
  | edgeReversal + forkRule_2   |  66 | not computed here           |
  | edgeReversal + tripleMerger |  78 | 240                         |
  | forkRule_2 + doubleCycle_5  |  78 | 240                         |

`DualSideIndependence` proves the depth-4 values 42 for
`edgeReversal + identityKeep` and 168 for `edgeReversal + forkRule_2`.

At depth 3 the five systems take four distinct values.
`edgeReversal + tripleMerger` and `forkRule_2 + doubleCycle_5` have equal
values at depths 2, 3 and 4.
-/

import InfraFormalization.BEquivalenceClasses

namespace InfraFormalization
namespace BEquivalenceRefinement

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

/-! ## Depth-3 B values -/

theorem B_d3_eR_id : discreteBranchialDensity edgeReversal_identity_Sys 3 = 30 := by
  native_decide

theorem B_d3_eR_dCyc : discreteBranchialDensity edgeReversal_doubleCycle_Sys 3 = 42 := by
  native_decide

theorem B_d3_eR_fork : discreteBranchialDensity edgeReversal_fork_Sys 3 = 66 := by
  native_decide

/-! ## Depth-3 values of the two systems with depth-2 value 18 -/

/-- At depth 3, `edgeReversal + identityKeep` has value 30 and
`edgeReversal + doubleCycle_5` has value 42. Both have value 18 at
depth 2. -/
theorem B_18_class_refines_at_d3 :
    discreteBranchialDensity edgeReversal_identity_Sys 3 = 30 ∧
    discreteBranchialDensity edgeReversal_doubleCycle_Sys 3 = 42 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 3 ≠
      discreteBranchialDensity edgeReversal_doubleCycle_Sys 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Depth-3 values of the three systems with depth-2 value 24 -/

/-- At depth 3, `edgeReversal + forkRule_2` has value 66, and
`edgeReversal + tripleMerger` and `forkRule_2 + doubleCycle_5` both have
value 78. These three systems all have value 24 at depth 2. -/
theorem B_24_class_refines_at_d3 :
    discreteBranchialDensity edgeReversal_fork_Sys 3 = 66 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 78 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 3 = 78 ∧
    -- Equal values for eR+tripleMerger and fork+dCyc:
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Depth-4 values -/

/-- At depth 4, `edgeReversal + tripleMerger` and
`forkRule_2 + doubleCycle_5` both have value 240. -/
theorem persistent_equivalence_at_d4 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 = 240 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 4 = 240 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 =
      discreteBranchialDensity fork_doubleCycle_Sys 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Values at depths 2 and 3 -/

/-- Seven values of `discreteBranchialDensity`: 18 and 24 at depth 2,
30, 42, 66 and 78 at depth 3, and the depth-3 equality of
`edgeReversal + tripleMerger` and `forkRule_2 + doubleCycle_5`. Proved
by `native_decide`. -/
theorem B_class_refinement_pattern :
    -- d=2 values 18 and 24:
    discreteBranchialDensity edgeReversal_identity_Sys 2 = 18 ∧
    discreteBranchialDensity edgeReversal_fork_Sys 2 = 24 ∧
    -- d=3 values 30, 42, 66, 78:
    discreteBranchialDensity edgeReversal_identity_Sys 3 = 30 ∧
    discreteBranchialDensity edgeReversal_doubleCycle_Sys 3 = 42 ∧
    discreteBranchialDensity edgeReversal_fork_Sys 3 = 66 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 78 ∧
    -- d=3: eR+tripleMerger and fork+dCyc have equal values:
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `B_18_class_refines_at_d3`: values 30 and 42 at depth 3, and their
    inequality.
  * `B_24_class_refines_at_d3`: values 66, 78 and 78 at depth 3, and the
    equality of the last two.
  * `persistent_equivalence_at_d4`: values 240 and 240 at depth 4, and
    their equality.
  * `B_class_refinement_pattern`: seven of the values above.

The module proves these finite statements for five systems at depths 2,
3 and 4. Whether `edgeReversal + tripleMerger` and
`forkRule_2 + doubleCycle_5` have equal values at every depth is OPEN.
-/

end BEquivalenceRefinement
end InfraFormalization
