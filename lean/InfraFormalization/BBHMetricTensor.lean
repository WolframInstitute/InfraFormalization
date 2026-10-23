/-
Scaled Knill values of the fire-all causal graph and the fire-all
same-step contention graph on the seed `bbhInitial` at depth 3, for the
systems `edgeReversal + identityKeep` and `edgeReversal + forkRule_2`.

`bbhInitial` (from `BBHInitialData`) is a 7-edge graph: two triangles on
`{0,1,2}` and `{3,4,5}` joined by the edge `{2,3}`. The traces come from
`tracedFireAllEvolve`, which applies every match of every rule found in
the state, including matches that share edges. It is not a Wolfram model
update when matches overlap. `branchialDAGOfFireAll` relates two events
of the same step that consume a common edge value. This relation is not
the branchial graph of the Wolfram model.

`DiscreteMetricTensor.discreteMetricTensor sys d` is the integer pair
`(discreteRicciScalar sys d, discreteBranchialDensity sys d)`: the two
scaled Knill values on the single-edge seed `seedEdge12`. The module
computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  * `edgeReversal + identityKeep`, depth 3: causal value -168, contention
    value 210. These equal 7 × (-24) and 7 × 30.
  * `edgeReversal + forkRule_2`, depth 3: causal value -294, contention
    value 462. These equal 7 × (-42) and 7 × 66.

The two theorems `bbh_lineElement_*` are the integer identities
`-168 + 210 = 42` and `-294 + 462 = 168`. They do not mention any
system or seed.
-/

import InfraFormalization.DiscreteMetricTensor
import InfraFormalization.BBHInitialData

namespace InfraFormalization
namespace BBHMetricTensor

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open BBHInitialData
open DiscreteRicciScalar
open BranchialUniversalAdditivity
open DiscreteMetricTensor

/-! ## Values for `edgeReversal + identityKeep` on `bbhInitial` at depth 3 -/

theorem bbh_causal_eR_id_3 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) = -168 := by
  native_decide

theorem bbh_branchial_eR_id_3 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) = 210 := by
  native_decide

/-! ## Values for `edgeReversal + forkRule_2` on `bbhInitial` at depth 3 -/

theorem bbh_causal_eR_fork_3 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) = -294 := by
  native_decide

theorem bbh_branchial_eR_fork_3 :
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) = 462 := by
  native_decide

/-! ## The four depth-3 values -/

/-- The four depth-3 scaled Knill values on `bbhInitial`: causal and
contention values for `edgeReversal + identityKeep` and for
`edgeReversal + forkRule_2`. -/
theorem bbh_metric_tensor_characterization :
    -- eR + id on bbhInitial at d=3: (-168, 210)
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) = -168 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) = 210 ∧
    -- eR + fork on bbhInitial at d=3: (-294, 462)
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) = -294 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) = 462 :=
  ⟨bbh_causal_eR_id_3, bbh_branchial_eR_id_3,
   bbh_causal_eR_fork_3, bbh_branchial_eR_fork_3⟩

/-! ## Factor 7 relative to the single-edge seed -/

/-- At depth 3, for the two systems `edgeReversal + identityKeep` and
`edgeReversal + forkRule_2`, each scaled Knill value on `bbhInitial`
equals 7 times the corresponding value on `seedEdge12`:

  * `edgeReversal + identityKeep`: (-168, 210) = 7 × (-24, 30).
  * `edgeReversal + forkRule_2`: (-294, 462) = 7 × (-42, 66).

The statement is these four equalities. Proved by `native_decide`.
-/
theorem bbh_tensor_universal_additivity :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) =
      7 * discreteRicciScalar edgeReversal_identity_Sys 3 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) =
      7 * discreteBranchialDensity edgeReversal_identity_Sys 3 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) =
      7 * discreteRicciScalar edgeReversal_fork_Sys 3 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) =
      7 * discreteBranchialDensity edgeReversal_fork_Sys 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Two integer identities -/

/-- The integer identity `-168 + 210 = 42`. The two summands are the
depth-3 values for `edgeReversal + identityKeep` on `bbhInitial`. -/
theorem bbh_lineElement_eR_id_1_1 :
    -168 + 210 = 42 := by decide

/-- The integer identity `-294 + 462 = 168`. The two summands are the
depth-3 values for `edgeReversal + forkRule_2` on `bbhInitial`. -/
theorem bbh_lineElement_eR_fork_1_1 :
    -294 + 462 = 168 := by decide

/-! ## Contents

  * `bbh_causal_eR_id_3`, `bbh_branchial_eR_id_3`, `bbh_causal_eR_fork_3`,
    `bbh_branchial_eR_fork_3`: four values computed by `native_decide`.
  * `bbh_metric_tensor_characterization`: the conjunction of the four.
  * `bbh_tensor_universal_additivity`: the four equalities with 7 times
    the `seedEdge12` values at depth 3.
  * `bbh_lineElement_eR_id_1_1`, `bbh_lineElement_eR_fork_1_1`: two
    integer identities.

The module states nothing about other depths, other rules, other seeds,
or any continuum metric.
-/

end BBHMetricTensor
end InfraFormalization
