/-
Values of `discreteBranchialDensity` and `discreteRicciScalar` for the
systems `edgeReversal + tripleMerger` and `forkRule_2 + doubleCycle_5`
at depths 2, 3 and 4.

Both quantities are scaled Knill values of graphs built from
`tracedFireAllEvolve` on the single edge `seedEdge12`.
`discreteRicciScalar` uses the causal graph (`causalDAGOfFireAll`).
`discreteBranchialDensity` uses the same-step contention graph
(`branchialDAGOfFireAll`), which links two events of the same step that
consume a common edge value. It is not the branchial graph of the
Wolfram model. `fireAllStep` applies every match of every rule found in
the state, including matches that share edges. It is not a Wolfram model
update when matches overlap.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | depth | R(eR+tripleMerger) | B(eR+tripleMerger) | R(fork+dCyc) | B(fork+dCyc) |
  |-------|--------------------|--------------------|--------------|--------------|
  |   2   |          0         |        24          |       6      |       24     |
  |   3   |        -36         |        78          |       0      |       78     |
  |   4   |       -192         |       240          |       0      |      240     |

At each of the three depths the two systems have equal B values and
different R values.
-/

import InfraFormalization.BBHCurvatureEvolution
import InfraFormalization.BranchialUniversalAdditivity

namespace InfraFormalization
namespace BCoincidenceFinding

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

/-! ## Values of `discreteBranchialDensity` -/

theorem B_eR_tripleMerger_2 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 = 24 := by
  native_decide

theorem B_eR_tripleMerger_4 :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 = 240 := by
  native_decide

theorem B_fork_dCyc_2 : discreteBranchialDensity fork_doubleCycle_Sys 2 = 24 := by
  native_decide

theorem B_fork_dCyc_4 : discreteBranchialDensity fork_doubleCycle_Sys 4 = 240 := by
  native_decide

/-! ## Equal values at depths 2, 3 and 4 -/

/-- At depths 2, 3 and 4, the systems `edgeReversal + tripleMerger` and
`forkRule_2 + doubleCycle_5` have the same `discreteBranchialDensity`
(24, 78 and 240). Proved by `native_decide`. -/
theorem B_trajectory_coincidence :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 =
      discreteBranchialDensity fork_doubleCycle_Sys 2 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 =
      discreteBranchialDensity fork_doubleCycle_Sys 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Different R trajectories at the same depths -/

/-- At depths 2, 3 and 4, the two systems have different
`discreteRicciScalar` values:

  * d=2: 0 and 6.
  * d=3: -36 and 0.
  * d=4: -192 and 0. -/
theorem R_trajectories_different :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 ≠
      discreteRicciScalar fork_doubleCycle_Sys 2 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 ≠
      discreteRicciScalar fork_doubleCycle_Sys 3 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 ≠
      discreteRicciScalar fork_doubleCycle_Sys 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Conjunction of the six statements -/

/-- The conjunction of `B_trajectory_coincidence` and
`R_trajectories_different`: equal `discreteBranchialDensity` values and
different `discreteRicciScalar` values at depths 2, 3 and 4 for the two
systems. Proved by `native_decide`. -/
theorem B_R_decoupling_finding :
    -- Equal B at depths 2, 3, 4:
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 =
      discreteBranchialDensity fork_doubleCycle_Sys 2 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 =
      discreteBranchialDensity fork_doubleCycle_Sys 4 ∧
    -- Different R at depths 2, 3, 4:
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 ≠
      discreteRicciScalar fork_doubleCycle_Sys 2 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 ≠
      discreteRicciScalar fork_doubleCycle_Sys 3 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 ≠
      discreteRicciScalar fork_doubleCycle_Sys 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `B_trajectory_coincidence`: three equalities of
    `discreteBranchialDensity`.
  * `R_trajectories_different`: three inequalities of
    `discreteRicciScalar`.
  * `B_R_decoupling_finding`: the conjunction of the six statements.

The module proves these finite statements for two systems at depths 2,
3 and 4. It states nothing about other depths or other systems.
-/

end BCoincidenceFinding
end InfraFormalization
