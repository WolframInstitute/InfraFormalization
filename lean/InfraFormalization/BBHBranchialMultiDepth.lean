/-
Scaled Knill values of the same-step contention graph on the seed
`bbhInitial` at depths 2, 3 and 4.

`bbhInitial` (from `BBHInitialData`) is a 7-edge graph: two triangles on
`{0,1,2}` and `{3,4,5}` joined by the edge `{2,3}`. The evolution is
`tracedFireAllEvolve`, which applies every match of every rule found in
the state, including matches that share edges. It is not a Wolfram model
update when matches overlap. `branchialDAGOfFireAll` relates two events
of the same step that consume a common edge value. This relation is not
the branchial graph of the Wolfram model.

For the system `edgeReversal + identityKeep`, the module computes by
`native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | depth | `discreteBranchialDensity` (seed `seedEdge12`) | value on `bbhInitial` |
  |-------|---------------------------------------------|-----------------------|
  |   2   |    18                                       |      126              |
  |   3   |    30                                       |      210              |
  |   4   |    42                                       |      294              |

At each of these three depths the value on `bbhInitial` equals 7 times
the value on the single edge `seedEdge12`.
-/

import InfraFormalization.BranchialUniversalAdditivity
import InfraFormalization.BBHInitialData

namespace InfraFormalization
namespace BBHBranchialMultiDepth

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open BBHInitialData
open BranchialUniversalAdditivity

/-! ## Values on `bbhInitial` at depths 2 and 4 -/

theorem bbh_branchial_eR_id_2 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 2) = 126 := by
  native_decide

theorem bbh_branchial_eR_id_4 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 4) = 294 := by
  native_decide

/-! ## Factor 7 at depths 2, 3 and 4 -/

/-- At depths 2, 3 and 4, the scaled Knill value of the fire-all
same-step contention graph of `edgeReversal + identityKeep` on
`bbhInitial` equals 7 times `discreteBranchialDensity` at the same
depth. Proved by `native_decide`. -/
theorem bbh_branchial_multi_depth_additivity :
    -- Depth 2: value on bbhInitial = 7 × value on seedEdge12 (18)
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 2) =
      7 * discreteBranchialDensity edgeReversal_identity_Sys 2 ∧
    -- Depth 3: value on bbhInitial = 7 × value on seedEdge12 (30)
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) =
      7 * discreteBranchialDensity edgeReversal_identity_Sys 3 ∧
    -- Depth 4: value on bbhInitial = 7 × value on seedEdge12 (42)
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 4) =
      7 * discreteBranchialDensity edgeReversal_identity_Sys 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `bbh_branchial_eR_id_2`, `bbh_branchial_eR_id_4`: the values 126 and
    294 at depths 2 and 4.
  * `bbh_branchial_multi_depth_additivity`: the three equalities with
    7 times `discreteBranchialDensity` at depths 2, 3 and 4.

The module proves these three depths only. It states nothing about
other depths, other rules or other seeds.
-/

end BBHBranchialMultiDepth
end InfraFormalization
