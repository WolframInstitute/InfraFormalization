/-
R at depths 3 to 6 for three single rules.

R is `discreteRicciScalar sys d`, the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 d`. The evolution is
`fireAllStep`, which applies every match of every rule found in the
state, including matches that share edges. It is not a Wolfram model
update when matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE):

  | Rule              | d=3 | d=4 | d=5 | d=6 |
  |-------------------|-----|-----|-----|-----|
  | edgeReversalSys   |  6  |  0  | -6  | -18 |
  | identityKeepSys   |  6  | 12  | 30  |     |
  | doubleCycleSys_5  |  6  | -6  | -30 |     |

The three rules have R = 6 at depth 3. The module proves this for these
three rules only. It states no growth law and no limit of R as d grows.
The name `discreteRicciScalar` is a label; the module defines no
Ricci tensor.
-/

import InfraFormalization.DiscreteRicciScalar

namespace InfraFormalization
namespace RicciScalarDepthTrajectory

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open DiscreteRicciScalar

/-! ## Depth 3 -/

/-- `edgeReversalSys` has R = 6 at depth 3. -/
theorem R_universal_at_depth3_edgeReversal :
    discreteRicciScalar edgeReversalSys 3 = 6 := by
  native_decide

theorem R_universal_at_depth3_identityKeep :
    discreteRicciScalar identityKeepSys 3 = 6 := by
  native_decide

theorem R_universal_at_depth3_doubleCycle_5 :
    discreteRicciScalar doubleCycleSys_5 3 = 6 := by
  native_decide

/-! ## edgeReversalSys -/

theorem R_edgeReversal_4 : discreteRicciScalar edgeReversalSys 4 = 0 := by
  native_decide

theorem R_edgeReversal_6 : discreteRicciScalar edgeReversalSys 6 = -18 := by
  native_decide

/-! ## identityKeepSys -/

theorem R_identityKeep_5 : discreteRicciScalar identityKeepSys 5 = 30 := by
  native_decide

/-! ## doubleCycleSys_5 -/

theorem R_doubleCycle_5_5 : discreteRicciScalar doubleCycleSys_5 5 = -30 := by
  native_decide

/-! ## Ten values -/

/-- `R_depth_trajectory_three_classes`: R = 6 at depth 3 for
`edgeReversalSys`, `identityKeepSys` and `doubleCycleSys_5`; R = 0,
-6, -18 at depths 4, 5, 6 for `edgeReversalSys`; R = 12, 30 at depths
4, 5 for `identityKeepSys`; R = -6, -30 at depths 4, 5 for
`doubleCycleSys_5`. -/
theorem R_depth_trajectory_three_classes :
    -- Depth 3:
    discreteRicciScalar edgeReversalSys 3 = 6 ∧
    discreteRicciScalar identityKeepSys 3 = 6 ∧
    discreteRicciScalar doubleCycleSys_5 3 = 6 ∧
    -- edgeReversal at depths 4, 5, 6:
    discreteRicciScalar edgeReversalSys 4 = 0 ∧
    discreteRicciScalar edgeReversalSys 5 = -6 ∧
    discreteRicciScalar edgeReversalSys 6 = -18 ∧
    -- identityKeep at depths 4, 5:
    discreteRicciScalar identityKeepSys 4 = 12 ∧
    discreteRicciScalar identityKeepSys 5 = 30 ∧
    -- doubleCycle_5 at depths 4, 5:
    discreteRicciScalar doubleCycleSys_5 4 = -6 ∧
    discreteRicciScalar doubleCycleSys_5 5 = -30 :=
  ⟨R_universal_at_depth3_edgeReversal,
   R_universal_at_depth3_identityKeep,
   R_universal_at_depth3_doubleCycle_5,
   R_edgeReversal_4, R_edgeReversal_5, R_edgeReversal_6,
   R_identityKeep_4, R_identityKeep_5,
   R_doubleCycle_5_4, R_doubleCycle_5_5⟩

/-- `depth_3_universal_regime`: at depth 3, `edgeReversalSys`,
`identityKeepSys` and `doubleCycleSys_5` have equal R. The name says
universal; the statement is about these three rules. -/
theorem depth_3_universal_regime :
    discreteRicciScalar edgeReversalSys 3 =
      discreteRicciScalar identityKeepSys 3 ∧
    discreteRicciScalar edgeReversalSys 3 =
      discreteRicciScalar doubleCycleSys_5 3 := by
  refine ⟨?_, ?_⟩
  · rw [R_universal_at_depth3_edgeReversal, R_universal_at_depth3_identityKeep]
  · rw [R_universal_at_depth3_edgeReversal, R_universal_at_depth3_doubleCycle_5]

/-! ## Summary

  * `R_depth_trajectory_three_classes`: ten values of R for three
    single rules at depths 3 to 6.
  * `depth_3_universal_regime`: the three rules have equal R (6) at
    depth 3. The statement is a conjunction over these three rules.

No growth law or limit of R in d is stated or proved.
-/

end RicciScalarDepthTrajectory
end InfraFormalization
