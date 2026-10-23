/-
Values of `discreteRicciScalar` (R) and `discreteBranchialDensity` (B)
for `edgeReversal + identityKeep` and `edgeReversal + forkRule_2`.

R is the scaled Knill value of `causalDAGOfFireAll sys seedEdge12 d`. B
is the scaled Knill value of `branchialDAGOfFireAll sys seedEdge12 d`,
the graph that links two events of the same step that consume a common
edge value. This relation is not the branchial graph of the Wolfram
model. Both graphs come from `tracedFireAllEvolve`, which applies every
match of every rule found in the state, including matches that share
edges. It is not a Wolfram model update when matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE; the depth-2 and depth-3 values of
`edgeReversal + forkRule_2` are stated through `same_R_different_B` and
in other modules):

  `edgeReversal + identityKeep`:

  | d=2 | d=3 | d=4 |
  |-----|-----|-----|
  | R=-6, B=18 | R=-24, B=30 | R=6, B=42 |

  `edgeReversal + forkRule_2`:

  | d=2 | d=3 | d=4 |
  |-----|-----|-----|
  | R=-6, B=24 | R=-42, B=66 | R=-72, B=168 |

For `edgeReversal + identityKeep`, R decreases from depth 2 to 3 and
increases from depth 3 to 4, while B increases at both steps. At depth 2
the two systems have equal R and different B. It follows that no
function f satisfies B = f(R, d) for both systems at d = 2.
-/

import InfraFormalization.BranchialUniversalAdditivity
import InfraFormalization.DiscreteRicciScalar

namespace InfraFormalization
namespace DualSideIndependence

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## Values of R and B -/

/-- `eR + id` at depth 2: R = -6, B = 18. -/
theorem RB_eR_id_2 :
    discreteRicciScalar edgeReversal_identity_Sys 2 = -6 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 2 = 18 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- `eR + id` at depth 3: R = -24, B = 30. -/
theorem RB_eR_id_3 :
    discreteRicciScalar edgeReversal_identity_Sys 3 = -24 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 3 = 30 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- `eR + id` at depth 4: R = 6, B = 42. -/
theorem RB_eR_id_4 :
    discreteRicciScalar edgeReversal_identity_Sys 4 = 6 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 4 = 42 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- `eR + fork` at depth 4: R = -72, B = 168. -/
theorem RB_eR_fork_4 :
    discreteRicciScalar edgeReversal_fork_Sys 4 = -72 ∧
    discreteBranchialDensity edgeReversal_fork_Sys 4 = 168 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Comparisons -/

/-- For `edgeReversal + identityKeep`: R is -6, -24, 6 and B is 18, 30,
42 at depths 2, 3, 4. -/
theorem R_nonmonotonic_B_monotonic :
    -- R sequence: -6, -24, 6 (non-monotonic):
    discreteRicciScalar edgeReversal_identity_Sys 2 = -6 ∧
    discreteRicciScalar edgeReversal_identity_Sys 3 = -24 ∧
    discreteRicciScalar edgeReversal_identity_Sys 4 = 6 ∧
    -- B sequence: 18, 30, 42 (strictly monotonic increasing):
    discreteBranchialDensity edgeReversal_identity_Sys 2 = 18 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 3 = 30 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 4 = 42 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- At depth 2, `edgeReversal + identityKeep` and
`edgeReversal + forkRule_2` have equal R (-6) and different B (18 and
24). -/
theorem same_R_different_B :
    discreteRicciScalar edgeReversal_identity_Sys 2 =
      discreteRicciScalar edgeReversal_fork_Sys 2 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 2 ≠
      discreteBranchialDensity edgeReversal_fork_Sys 2 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Conjunction -/

/-- A conjunction of six finite statements:

  1. For `edgeReversal + identityKeep`, R at depth 3 is at most R at
     depth 2, and R at depth 4 is greater than R at depth 3.
  2. For the same system, B strictly increases from depth 2 to 3 and
     from depth 3 to 4.
  3. At depth 2, `edgeReversal + identityKeep` and
     `edgeReversal + forkRule_2` have equal R and different B. -/
theorem dual_side_independence :
    -- (1) R can be non-monotonic while B is monotonic:
    discreteRicciScalar edgeReversal_identity_Sys 3 ≤
      discreteRicciScalar edgeReversal_identity_Sys 2 ∧
    discreteRicciScalar edgeReversal_identity_Sys 4 >
      discreteRicciScalar edgeReversal_identity_Sys 3 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 2 <
      discreteBranchialDensity edgeReversal_identity_Sys 3 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 3 <
      discreteBranchialDensity edgeReversal_identity_Sys 4 ∧
    -- (2) Same R, different B:
    discreteRicciScalar edgeReversal_identity_Sys 2 =
      discreteRicciScalar edgeReversal_fork_Sys 2 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 2 ≠
      discreteBranchialDensity edgeReversal_fork_Sys 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `RB_eR_id_2`, `RB_eR_id_3`, `RB_eR_id_4`, `RB_eR_fork_4`: pairs of
    values.
  * `R_nonmonotonic_B_monotonic`: six values for
    `edgeReversal + identityKeep` at depths 2, 3 and 4.
  * `same_R_different_B`: equal R and different B for the two systems at
    depth 2.
  * `dual_side_independence`: four order relations and the two depth-2
    statements.

All statements concern two systems, depths 2 to 4, and the seed
`seedEdge12`.
-/

end DualSideIndependence
end InfraFormalization
