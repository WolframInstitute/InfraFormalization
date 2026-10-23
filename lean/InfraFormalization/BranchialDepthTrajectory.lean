/-
Contention Knill values of two rule pairs at depths 2, 3 and 4.

The quantity is the scaled Knill Euler characteristic of
`branchialDAGOfFireAll sys seedEdge12 d`. That graph joins two events
of the same step that consume a common edge. It is not the
Wolfram-model branchial graph. The evolution is `fireAllStep`, which
applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE):

  | Rule pair                   | d=2 | d=3 | d=4 |
  |-----------------------------|-----|-----|-----|
  | edgeReversal + identityKeep |  18 |  30 |  42 |
  | edgeReversal + forkRule_2   |  24 |  66 | 168 |

For `edgeReversal + identityKeep` the two differences are 12 and 12.
For `edgeReversal + forkRule_2` the two differences are 42 and 102.
The module defines no Hilbert space or quantum state.
-/

import InfraFormalization.BranchialRSpectrum

namespace InfraFormalization
namespace BranchialDepthTrajectory

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open BranchialRSpectrum

/-! ## edgeReversal + identityKeep -/

theorem eR_id_branchial_d2 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 2) = 18 := by
  native_decide

theorem eR_id_branchial_d4 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 4) = 42 := by
  native_decide

/-! ## edgeReversal + forkRule_2 -/

theorem eR_fork_branchial_d2 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 2) = 24 := by
  native_decide

theorem eR_fork_branchial_d4 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 4) = 168 := by
  native_decide

/-! ## Six values -/

/-- `branchial_depth_trajectory`: the scaled Knill value of
`branchialDAGOfFireAll sys seedEdge12 d` at depths 2, 3, 4 is 18, 30,
42 for `edgeReversal_identity_Sys` and 24, 66, 168 for
`edgeReversal_fork_Sys`. -/
theorem branchial_depth_trajectory :
    -- eR + identityKeep:
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 2) = 18 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = 30 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 4) = 42 ∧
    -- eR + forkRule_2:
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 2) = 24 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = 66 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 4) = 168 :=
  ⟨eR_id_branchial_d2, eR_id_branchial_30, eR_id_branchial_d4,
   eR_fork_branchial_d2, eR_fork_branchial_66, eR_fork_branchial_d4⟩

/-- `arithmetic_branchial_regime`: for `eR + identityKeep`, the
contention Knill value increases by 12 from depth 2 to depth 3 and by
12 from depth 3 to depth 4. -/
theorem arithmetic_branchial_regime :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) -
      knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 2) = 12 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 4) -
      knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = 12 := by
  refine ⟨?_, ?_⟩
  · rw [eR_id_branchial_30, eR_id_branchial_d2]; rfl
  · rw [eR_id_branchial_d4, eR_id_branchial_30]; rfl

/-- `geometric_branchial_regime`: for `eR + forkRule_2`, the difference
of the contention Knill values from depth 3 to depth 4 (102) exceeds
the difference from depth 2 to depth 3 (42). -/
theorem geometric_branchial_regime :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 4) -
      knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) >
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) -
      knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 2) := by
  rw [eR_fork_branchial_d4, eR_fork_branchial_66, eR_fork_branchial_d2]
  decide

/-! ## Summary

  * `branchial_depth_trajectory`: six values (two pairs, depths 2, 3, 4).
  * `arithmetic_branchial_regime`: for `eR + identityKeep` the
    differences d=2→3 and d=3→4 are both 12.
  * `geometric_branchial_regime`: for `eR + forkRule_2` the difference
    d=3→4 (102) exceeds the difference d=2→3 (42).

No theorem here states the growth law beyond depth 4.
-/

end BranchialDepthTrajectory
end InfraFormalization
