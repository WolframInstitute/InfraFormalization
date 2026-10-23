/-
Scaled Knill values of the same-step contention graph on seeds with one,
two and three edges, at depth 3.

The trace comes from `tracedFireAllEvolve`, which applies every match of
every rule found in the state, including matches that share edges. It is
not a Wolfram model update when matches overlap. `branchialDAGOfFireAll`
links two events of the same step that consume a common edge value. This
relation is not the branchial graph of the Wolfram model.

For `edgeReversal + identityKeep` at depth 3 the module computes by
`native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | Seed                        | value |
  |-----------------------------|-------|
  | `seedEdge12` (1 edge)       |   30  |
  | `seedPath123` (2 edges)     |   60  |
  | `seedTriangle` (3 edges)    |   90  |

For `edgeReversal + forkRule_2` at depth 3 the values are 66 on
`seedEdge12` and 132 on `seedPath123`.

In these five cases the value equals the number of seed edges times the
value on `seedEdge12`. The module also defines `discreteBranchialDensity`
(the value on `seedEdge12`) and the integer combination
`discreteUnifiedEH`.
-/

import InfraFormalization.UniversalAdditivity
import InfraFormalization.BranchialEventTrace

namespace InfraFormalization
namespace BranchialUniversalAdditivity

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open UniversalAdditivity

/-! ## Branchial Knill at multiple seed topologies (depth 3) -/

theorem branchial_eR_id_path :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedPath123 3) = 60 := by
  native_decide

theorem branchial_eR_id_triangle :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedTriangle 3) = 90 := by
  native_decide

/-! ## Three seeds for `edgeReversal + identityKeep` -/

/-- For `edgeReversal + identityKeep` at depth 3, the value on
`seedEdge12` is 30, on `seedPath123` it is `2 * 30`, and on
`seedTriangle` it is `3 * 30`. The statement is these three
equalities. -/
theorem branchial_universal_additivity_eR_id :
    -- Baseline:
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = 30 ∧
    -- Path (2 edges):
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedPath123 3) = 2 * 30 ∧
    -- Triangle (3 edges):
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys seedTriangle 3) = 3 * 30 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · rw [branchial_eR_id_path]; rfl
  · rw [branchial_eR_id_triangle]; rfl

/-! ## Two seeds for `edgeReversal + forkRule_2` -/

theorem branchial_eR_fork_path :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedPath123 3) = 132 := by
  native_decide

/-- For `edgeReversal + forkRule_2` at depth 3, the value on `seedEdge12`
is 66 and the value on `seedPath123` is `2 * 66`. The statement is
these two equalities. -/
theorem branchial_universal_additivity_eR_fork :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = 66 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys seedPath123 3) = 2 * 66 := by
  refine ⟨?_, ?_⟩
  · native_decide
  · rw [branchial_eR_fork_path]; rfl

/-! ## The value on `seedEdge12` -/

/-- `discreteBranchialDensity sys d` is the scaled Knill value of the
fire-all same-step contention graph of `sys` on `seedEdge12` after `d`
steps. -/
def discreteBranchialDensity (sys : ExecSystem) (d : Nat) : Int :=
  knillEulerScaled (branchialDAGOfFireAll sys seedEdge12 d)

/-- `discreteBranchialDensity edgeReversal_identity_Sys 3 = 30`. -/
theorem B_eR_id_3 : discreteBranchialDensity edgeReversal_identity_Sys 3 = 30 := by
  native_decide

/-! ## An integer combination of the causal and contention values -/

/-- `discreteUnifiedEH sys seed d α` is the integer
`seed.length * (R + α * B)`, where `R` is the scaled Knill value of
`causalDAGOfFireAll sys seedEdge12 d` and `B` is
`discreteBranchialDensity sys d`. The definition evaluates the
evolution on `seedEdge12` only. `seed` enters through its length. -/
def discreteUnifiedEH (sys : ExecSystem) (seed : ExecHG ℕ) (d : Nat) (α : Int) : Int :=
  (seed.length : Int) *
    (knillEulerScaled (causalDAGOfFireAll sys seedEdge12 d) +
     α * discreteBranchialDensity sys d)

/-- `discreteUnifiedEH edgeReversal_identity_Sys seedTriangle 3 1`
equals `3 * (-24 + 30)`. The factor 3 is `seedTriangle.length`, and
-24 and 30 are the causal and contention values on `seedEdge12` at
depth 3. -/
theorem unified_EH_at_alpha_1 :
    discreteUnifiedEH edgeReversal_identity_Sys seedTriangle 3 1 = 3 * (-24 + 30) := by
  native_decide

/-! ## Contents

  * `branchial_eR_id_path`, `branchial_eR_id_triangle`,
    `branchial_eR_fork_path`: values 60, 90 and 132.
  * `branchial_universal_additivity_eR_id`: three equalities for
    `edgeReversal + identityKeep` at depth 3 on `seedEdge12`,
    `seedPath123` and `seedTriangle`.
  * `branchial_universal_additivity_eR_fork`: two equalities for
    `edgeReversal + forkRule_2` at depth 3 on `seedEdge12` and
    `seedPath123`.
  * `discreteBranchialDensity` and `discreteUnifiedEH`: definitions.
  * `B_eR_id_3`, `unified_EH_at_alpha_1`: two values.

The proportionality to the number of seed edges is proved for these five
(system, seed) pairs at depth 3 only. The general statement
`∀ sys seed d, knillEulerScaled (branchialDAGOfFireAll sys seed d) =
seed.length * discreteBranchialDensity sys d` is not proved here.
-/

end BranchialUniversalAdditivity
end InfraFormalization
