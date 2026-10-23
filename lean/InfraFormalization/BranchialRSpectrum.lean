/-
Contention Knill values at depth 3 for two one-rule systems and three
rule pairs.

The quantity is the scaled Knill Euler characteristic of
`branchialDAGOfFireAll sys seedEdge12 3`. That graph joins two events
of the same step that consume a common edge. It is not the
Wolfram-model branchial graph. The evolution is `fireAllStep`, which
applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE):

  | System                        | value at d=3 |
  |-------------------------------|--------------|
  | edgeReversalSys               |       0      |
  | identityKeepSys               |       0      |
  | edgeReversal + identityKeep   |      30      |
  | edgeReversal + forkRule_2     |      66      |
  | edgeReversal + tripleMerger   |      78      |

The module proves no statement about one-rule systems in general. It
defines no quantum state or superposition.
-/

import InfraFormalization.BranchialEventTrace
import InfraFormalization.MultiRuleDiscovered

namespace InfraFormalization
namespace BranchialRSpectrum

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered

/-! ## One-rule systems -/

/-- `edgeReversalSys` gives contention Knill value 0 at depth 3 on
`seedEdge12`. -/
theorem edgeReversal_branchial_0 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversalSys seedEdge12 3) = 0 := by
  native_decide

/-- `identityKeepSys` gives contention Knill value 0 at depth 3 on
`seedEdge12`. -/
theorem identityKeep_branchial_0 :
    knillEulerScaled (branchialDAGOfFireAll identityKeepSys seedEdge12 3) = 0 := by
  native_decide

/-! ## Two-rule systems -/

theorem eR_id_branchial_30 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = 30 := by
  native_decide

theorem eR_fork_branchial_66 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = 66 := by
  native_decide

theorem eR_tripleMerger_branchial_78 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 3) = 78 := by
  native_decide

/-! ## One-rule and two-rule systems -/

/-- `branchial_single_rule_zero`: `edgeReversalSys` and
`identityKeepSys` give 0 at depth 3 on `seedEdge12`. The statement is
a conjunction over these two systems. -/
theorem branchial_single_rule_zero :
    knillEulerScaled (branchialDAGOfFireAll edgeReversalSys seedEdge12 3) = 0 ∧
    knillEulerScaled (branchialDAGOfFireAll identityKeepSys seedEdge12 3) = 0 :=
  ⟨edgeReversal_branchial_0, identityKeep_branchial_0⟩

/-- `branchial_multi_rule_nonzero`: `edgeReversal_identity_Sys`,
`edgeReversal_fork_Sys` and `edgeReversal_tripleMerger_Sys` give 30, 66
and 78 at depth 3 on `seedEdge12`. The statement is a conjunction over
these three systems. -/
theorem branchial_multi_rule_nonzero :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = 30 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = 66 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 3) = 78 :=
  ⟨eR_id_branchial_30, eR_fork_branchial_66, eR_tripleMerger_branchial_78⟩

/-! ## Five values at depth 3 -/

/-- `branchial_R_spectrum`: the conjunction of the five contention
Knill values at depth 3 on `seedEdge12`. -/
theorem branchial_R_spectrum :
    -- One-rule systems:
    knillEulerScaled (branchialDAGOfFireAll edgeReversalSys seedEdge12 3) = 0 ∧
    knillEulerScaled (branchialDAGOfFireAll identityKeepSys seedEdge12 3) = 0 ∧
    -- Rule pairs:
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = 30 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = 66 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 3) = 78 :=
  ⟨edgeReversal_branchial_0, identityKeep_branchial_0,
   eR_id_branchial_30, eR_fork_branchial_66, eR_tripleMerger_branchial_78⟩

/-! ## Summary

  * Five contention Knill values at depth 3 on `seedEdge12`.
  * `branchial_single_rule_zero`: the two one-rule systems give 0.
  * `branchial_multi_rule_nonzero`: the three rule pairs give 30, 66, 78.
  * `branchial_R_spectrum`: the conjunction of the five values.

Every statement is about named systems at depth 3. No theorem states
that every one-rule system gives 0 or that every rule pair gives a
nonzero value.
-/

end BranchialRSpectrum
end InfraFormalization
