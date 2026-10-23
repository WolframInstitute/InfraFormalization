/-
Sign of `discreteUnifiedEH` at α = 0 and α = 1, and the ratio -R/B,
for two rule pairs at depth 3.

`discreteUnifiedEH sys seed d α` is the integer
`seed.length * (R + α * B)` with α an integer. R is the scaled Knill
value of `causalDAGOfFireAll sys seedEdge12 d` and B is
`discreteBranchialDensity sys d`, the scaled Knill value of
`branchialDAGOfFireAll sys seedEdge12 d`. The evolution is evaluated on
`seedEdge12` only. With `seed = bbhInitial` the result is 7 times the
`seedEdge12` value; `bbhInitial` is never evolved. The branchial graph
joins two events of the same step that consume a common edge; it is
not the Wolfram-model branchial graph. The evolution is `fireAllStep`,
which applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

Values at depth 3 (PROVED-WITH-NATIVE-DECIDE):

  * `eR + id`: -168 at α = 0, 42 at α = 1, and `5R + 4B = 0`
    (`-R/B = 4/5`).
  * `eR + fork`: -294 at α = 0, 168 at α = 1, and `11R + 7B = 0`
    (`-R/B = 7/11`).

The name "Einstein-Hilbert" is a label. The module defines no action
on a manifold and no physical constant.
-/

import InfraFormalization.BranchialUniversalAdditivity
import InfraFormalization.BBHInitialData
import InfraFormalization.DiscreteRicciScalar

namespace InfraFormalization
namespace UnifiedEHBalance

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

/-! ## eR + id at α = 0 and α = 1 -/

/-- For `eR + id` at depth 3 with seed `bbhInitial`,
`discreteUnifiedEH` at α = 0 is `7 · (-24) = -168`. -/
theorem unifiedEH_BBH_alpha_0_negative :
    discreteUnifiedEH edgeReversal_identity_Sys bbhInitial 3 0 = -168 := by
  native_decide

/-- For `eR + id` at depth 3 with seed `bbhInitial`,
`discreteUnifiedEH` at α = 1 is `7 · (-24 + 30) = 42`. -/
theorem unifiedEH_BBH_alpha_1_positive :
    discreteUnifiedEH edgeReversal_identity_Sys bbhInitial 3 1 = 42 := by
  native_decide

/-! ## Sign change between α = 0 and α = 1 -/

/-- `balance_alpha_in_unit_interval`: for `eR + id` at depth 3 with
seed `bbhInitial`, `discreteUnifiedEH` is negative at α = 0 and
positive at α = 1. -/
theorem balance_alpha_in_unit_interval :
    discreteUnifiedEH edgeReversal_identity_Sys bbhInitial 3 0 < 0 ∧
    discreteUnifiedEH edgeReversal_identity_Sys bbhInitial 3 1 > 0 := by
  refine ⟨?_, ?_⟩
  · rw [unifiedEH_BBH_alpha_0_negative]; decide
  · rw [unifiedEH_BBH_alpha_1_positive]; decide

/-- `balance_alpha_BBH_eR_id`: `5 * R + 4 * B = 0` for `eR + id` at
depth 3 (`5·(-24) + 4·30 = 0`), so `-R/B = 4/5`. -/
theorem balance_alpha_BBH_eR_id :
    5 * discreteRicciScalar edgeReversal_identity_Sys 3 +
      4 * discreteBranchialDensity edgeReversal_identity_Sys 3 = 0 := by
  native_decide

/-! ## eR + fork -/

theorem unifiedEH_BBH_alpha_0_eR_fork :
    discreteUnifiedEH edgeReversal_fork_Sys bbhInitial 3 0 = -294 := by
  native_decide

theorem unifiedEH_BBH_alpha_1_eR_fork :
    discreteUnifiedEH edgeReversal_fork_Sys bbhInitial 3 1 = 168 := by
  native_decide

/-- `balance_alpha_BBH_eR_fork`: for `eR + fork` at depth 3 with seed
`bbhInitial`, `discreteUnifiedEH` is negative at α = 0 and positive at
α = 1, and `11 * R + 7 * B = 0`, so `-R/B = 7/11`. -/
theorem balance_alpha_BBH_eR_fork :
    discreteUnifiedEH edgeReversal_fork_Sys bbhInitial 3 0 < 0 ∧
    discreteUnifiedEH edgeReversal_fork_Sys bbhInitial 3 1 > 0 ∧
    -- -R/B = 42/66 = 7/11:
    -- 11 * R(eR+fork, 3) + 7 * B(eR+fork, 3) = 0
    11 * discreteRicciScalar edgeReversal_fork_Sys 3 +
      7 * discreteBranchialDensity edgeReversal_fork_Sys 3 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [unifiedEH_BBH_alpha_0_eR_fork]; decide
  · rw [unifiedEH_BBH_alpha_1_eR_fork]; decide
  · native_decide

/-! ## Summary

  * `balance_alpha_in_unit_interval`: for `eR + id`, the value with
    seed `bbhInitial` at depth 3 is -168 at α = 0 and 42 at α = 1.
  * `balance_alpha_BBH_eR_id`: `5R + 4B = 0` for `eR + id` at depth 3.
  * `balance_alpha_BBH_eR_fork`: for `eR + fork`, the value is -294 at
    α = 0 and 168 at α = 1, and `11R + 7B = 0` at depth 3.

All values are PROVED-WITH-NATIVE-DECIDE. The module defines no
coupling constant and no continuum limit.
-/

end UnifiedEHBalance
end InfraFormalization
