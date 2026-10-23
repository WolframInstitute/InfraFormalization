/-
Causal-graph Knill values of three rule pairs at depths 2 to 5.

K denotes `knillEulerScaled (causalDAGOfFireAll sys seedEdge12 d)`.
The evolution is `fireAllStep`, which applies every match of every
rule found in the state, including matches that share edges. It is not
a Wolfram model update when matches overlap. Some docstrings in the
library call the integer `1 - K/6` the number of holes.

Values (PROVED-WITH-NATIVE-DECIDE; depth-3 values from
`MultiRuleDiscovered`):

  | Rule pair                   | d=2 | d=3 | d=4  | d=5 |
  |-----------------------------|-----|-----|------|-----|
  | edgeReversal + tripleMerger |   0 |     | -192 |     |
  | edgeReversal + identityKeep |  -6 | -24 |    6 |     |
  | edgeReversal + forkRule_2   |  -6 |     |  -72 | -36 |

The theorem names `new_high_merger_champion`, `transient_causal_bubble`
and `bbh_phase_structure_signature` are labels. The module defines no
waveform, merger or binary system.
-/

import InfraFormalization.MultiRuleDiscovered

namespace InfraFormalization
namespace MultiRuleDepthTrajectory

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered

/-! ## edgeReversal + tripleMerger -/

/-- `edgeReversal + tripleMerger` at depth 2: K = 0. -/
theorem edgeReversal_tripleMerger_depth2 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 2) = 0 := by
  native_decide

/-- `edgeReversal + tripleMerger` at depth 4: K = -192. -/
theorem edgeReversal_tripleMerger_depth4 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 4) = -192 := by
  native_decide

/-! ## edgeReversal + identityKeep -/

/-- `edgeReversal + identityKeep` at depth 2: K = -6. -/
theorem edgeReversal_identity_depth2 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys seedEdge12 2) = -6 := by
  native_decide

/-- `edgeReversal + identityKeep` at depth 4: K = 6. -/
theorem edgeReversal_identity_depth4_closes :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys seedEdge12 4) = 6 := by
  native_decide

/-! ## edgeReversal + forkRule_2 -/

/-- `edgeReversal + forkRule_2` at depth 2: K = -6. -/
theorem edgeReversal_fork_depth2 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 2) = -6 := by
  native_decide

/-- `edgeReversal + forkRule_2` at depth 4: K = -72. -/
theorem edgeReversal_fork_depth4 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 4) = -72 := by
  native_decide

/-- `edgeReversal + forkRule_2` at depth 5: K = -36. -/
theorem edgeReversal_fork_depth5_regresses :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 5) = -36 := by
  native_decide

/-! ## Three conjunctions -/

/-- `new_high_merger_champion`: for `edgeReversal + tripleMerger` at
depth 4, K = -192, and the integer `1 - (-192)/6` equals 33. -/
theorem new_high_merger_champion :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 4) = -192 ∧
    (1 - (-192 : Int) / 6) = 33 :=
  ⟨edgeReversal_tripleMerger_depth4, by decide⟩

/-- `transient_causal_bubble`: for `edgeReversal + identityKeep`,
K = -6 at depth 2, K = -24 at depth 3 and K = 6 at depth 4. -/
theorem transient_causal_bubble :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys seedEdge12 2) = -6 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = -24 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys seedEdge12 4) = 6 :=
  ⟨edgeReversal_identity_depth2,
   edgeReversal_identity_knill_neg24,
   edgeReversal_identity_depth4_closes⟩

/-- `bbh_phase_structure_signature`: for `edgeReversal + forkRule_2`,
K = -6 at depth 2, K = -72 at depth 4 and K = -36 at depth 5. The name
is a label; the statement is these three values. -/
theorem bbh_phase_structure_signature :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 2) = -6 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 4) = -72 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 5) = -36 :=
  ⟨edgeReversal_fork_depth2,
   edgeReversal_fork_depth4,
   edgeReversal_fork_depth5_regresses⟩

/-! ## Summary

  * Seven Knill values of fire-all causal graphs for three rule pairs.
  * `new_high_merger_champion`: K = -192 for `eR + tripleMerger` at
    depth 4, and `1 - (-192)/6 = 33`.
  * `transient_causal_bubble`: K = -6, -24, 6 for `eR + identityKeep`
    at depths 2, 3, 4.
  * `bbh_phase_structure_signature`: K = -6, -72, -36 for
    `eR + forkRule_2` at depths 2, 4, 5.

The theorem names are labels. No statement in this module relates
these values to a binary black hole, a waveform or a merger.
-/

end MultiRuleDepthTrajectory
end InfraFormalization
