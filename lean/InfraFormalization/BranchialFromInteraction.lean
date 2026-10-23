/-
Scaled Knill values of the same-step contention graph for five
single-rule systems at depth 3 on the single edge `seedEdge12`.

The trace comes from `tracedFireAllEvolve`, which applies every match of
every rule found in the state, including matches that share edges. It is
not a Wolfram model update when matches overlap. `branchialDAGOfFireAll`
links two events of the same step that consume a common edge value. This
relation is not the branchial graph of the Wolfram model.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | Single-rule system | value at depth 3 |
  |--------------------|------------------|
  | edgeReversal       |       0          |
  | identityKeep       |       0          |
  | forkRule_2         |       0          |
  | doubleCycle_5      |       0          |
  | tripleMerger       |       0          |

Other modules compute nonzero depth-3 values for two-rule systems on the
same seed: 30 for `edgeReversal + identityKeep`, 66 for
`edgeReversal + forkRule_2`, and 78 for `edgeReversal + tripleMerger`
(`BranchialUniversalAdditivity`, `BEquivalenceRefinement`).
-/

import InfraFormalization.BranchialUniversalAdditivity

namespace InfraFormalization
namespace BranchialFromInteraction

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded

/-! ## Three single-rule values -/

theorem fork_branchial_0 :
    knillEulerScaled (branchialDAGOfFireAll forkSys_2 seedEdge12 3) = 0 := by
  native_decide

theorem doubleCycle_5_branchial_0 :
    knillEulerScaled (branchialDAGOfFireAll doubleCycleSys_5 seedEdge12 3) = 0 := by
  native_decide

theorem tripleMerger_branchial_0 :
    knillEulerScaled (branchialDAGOfFireAll tripleMergerSys seedEdge12 3) = 0 := by
  native_decide

/-! ## Five single-rule values -/

/-- For the five single-rule systems `edgeReversalSys`,
`identityKeepSys`, `forkSys_2`, `doubleCycleSys_5` and `tripleMergerSys`,
the scaled Knill value of the fire-all same-step contention graph on
`seedEdge12` at depth 3 is 0. The statement is a conjunction of these
five equalities. Proved by `native_decide`. -/
theorem all_single_rules_branchial_zero :
    knillEulerScaled (branchialDAGOfFireAll edgeReversalSys seedEdge12 3) = 0 ∧
    knillEulerScaled (branchialDAGOfFireAll identityKeepSys seedEdge12 3) = 0 ∧
    knillEulerScaled (branchialDAGOfFireAll forkSys_2 seedEdge12 3) = 0 ∧
    knillEulerScaled (branchialDAGOfFireAll doubleCycleSys_5 seedEdge12 3) = 0 ∧
    knillEulerScaled (branchialDAGOfFireAll tripleMergerSys seedEdge12 3) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `fork_branchial_0`, `doubleCycle_5_branchial_0`,
    `tripleMerger_branchial_0`: three values computed by `native_decide`.
  * `all_single_rules_branchial_zero`: the five depth-3 values for the
    single-rule systems listed above.

The module proves five finite equalities at depth 3 on `seedEdge12`. It
states nothing about other single-rule systems, other depths or other
seeds. A scaled Knill value of 0 does not by itself imply that the
contention graph has no edges.
-/

end BranchialFromInteraction
end InfraFormalization
