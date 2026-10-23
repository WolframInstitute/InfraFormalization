/-
Causal and contention Knill values of `fork_doubleCycle_Sys` on three
seeds at depths 3 and 4.

R denotes the scaled Knill value of `causalDAGOfFireAll sys seed d`.
B denotes the scaled Knill value of `branchialDAGOfFireAll sys seed d`.
That graph joins two events of the same step that consume a common
edge. It is not the Wolfram-model branchial graph. The evolution is
`fireAllStep`, which applies every match of every rule found in the
state, including matches that share edges. It is not a Wolfram model
update when matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE):

  | d | seed         | R | B   | seed.length · B(seedEdge12) |
  |---|--------------|---|-----|-----------------------------|
  | 3 | seedEdge12   | 0 |  78 |            78               |
  | 3 | seedPath123  | 0 | 156 |          2·78 = 156         |
  | 3 | seedTriangle | 0 | 234 |          3·78 = 234         |
  | 4 | seedEdge12   | 0 | 240 |           240               |
  | 4 | seedPath123  | 0 | 480 |         2·240 = 480         |
  | 4 | seedTriangle | 0 | 720 |         3·240 = 720         |

The word "vacuum" in theorem names is a label for R = 0. The module
defines no metric, field equation or quantum state, and states nothing
for other seeds or depths.
-/

import InfraFormalization.PersistentRDegeneracy
import InfraFormalization.BranchialUniversalAdditivity
import InfraFormalization.UniversalAdditivity

namespace InfraFormalization
namespace VacuumLikeUniversal

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity
open UniversalAdditivity
open PersistentRDegeneracy

/-! ## Causal Knill on seedPath123 and seedTriangle -/

theorem fork_dCyc_R_path_3 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedPath123 3) = 0 := by
  native_decide

theorem fork_dCyc_R_triangle_3 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedTriangle 3) = 0 := by
  native_decide

theorem fork_dCyc_R_path_4 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedPath123 4) = 0 := by
  native_decide

theorem fork_dCyc_R_triangle_4 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedTriangle 4) = 0 := by
  native_decide

/-! ## Contention Knill on seedPath123 and seedTriangle -/

theorem fork_dCyc_B_path_3 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedPath123 3) = 156 := by
  native_decide

theorem fork_dCyc_B_triangle_3 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedTriangle 3) = 234 := by
  native_decide

theorem fork_dCyc_B_path_4 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedPath123 4) = 480 := by
  native_decide

theorem fork_dCyc_B_triangle_4 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedTriangle 4) = 720 := by
  native_decide

/-! ## Conjunctions -/

/-- `vacuum_like_universal_R_persistence`: for `fork_doubleCycle_Sys`,
the causal Knill value is 0 on `seedEdge12`, `seedPath123` and
`seedTriangle` at depths 3 and 4. The name says universal; the
statement is these six instances. -/
theorem vacuum_like_universal_R_persistence :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedEdge12 3) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedPath123 3) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedTriangle 3) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedEdge12 4) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedPath123 4) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedTriangle 4) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- `vacuum_like_B_universal_additivity`: for `fork_doubleCycle_Sys`,
the contention Knill value is `2 * 78` on `seedPath123` and `3 * 78`
on `seedTriangle` at depth 3, and `2 * 240` and `3 * 240` at depth 4.
The name says universal; the statement is these four instances. -/
theorem vacuum_like_B_universal_additivity :
    -- Depth 3:
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedPath123 3) = 2 * 78 ∧
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedTriangle 3) = 3 * 78 ∧
    -- Depth 4:
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedPath123 4) = 2 * 240 ∧
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedTriangle 4) = 3 * 240 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fork_dCyc_B_path_3]; rfl
  · rw [fork_dCyc_B_triangle_3]; rfl
  · rw [fork_dCyc_B_path_4]; rfl
  · rw [fork_dCyc_B_triangle_4]; rfl

/-! ## Three-part conjunction -/

/-- `vacuum_like_unified_structural_law`: for `fork_doubleCycle_Sys`,
the causal Knill value is 0 on `seedEdge12` at depth 3 and on
`seedTriangle` at depth 4, and the contention Knill value on
`seedTriangle` at depth 4 is 3 times the value on `seedEdge12`. -/
theorem vacuum_like_unified_structural_law :
    -- Causal Knill = 0:
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedEdge12 3) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedTriangle 4) = 0 ∧
    -- Contention Knill on seedTriangle = 3 × seedEdge12:
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedTriangle 4) =
      3 * knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys seedEdge12 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

  * `vacuum_like_universal_R_persistence`: causal Knill 0 for
    `fork_doubleCycle_Sys` on three seeds at depths 3 and 4.
  * `vacuum_like_B_universal_additivity`: contention Knill on
    `seedPath123` and `seedTriangle` equals 2 and 3 times the
    `seedEdge12` value at depths 3 and 4.
  * `vacuum_like_unified_structural_law`: a three-part conjunction of
    these values.

All statements concern one rule pair, three seeds and depths 3 and 4.
-/

end VacuumLikeUniversal
end InfraFormalization
