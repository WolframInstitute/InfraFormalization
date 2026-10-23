/-
Values of R + B and of R for `edgeReversal + tripleMerger` at depths 2
to 5, compared with `12·d + 6·(d mod 2)` and
`3 - 3^(d+1) + 12·d + 6·(d mod 2)`.

R is `discreteRicciScalar`, the scaled Knill value of
`causalDAGOfFireAll sys seedEdge12 d`. B is `discreteBranchialDensity`,
the scaled Knill value of `branchialDAGOfFireAll sys seedEdge12 d`, the
graph that links two events of the same step that consume a common edge
value. This relation is not the branchial graph of the Wolfram model.
Both graphs come from `tracedFireAllEvolve`, which applies every match
of every rule found in the state, including matches that share edges.
It is not a Wolfram model update when matches overlap.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | d | R      | B     | R+B  | 12·d + 6·(d mod 2) |
  |---|--------|-------|------|--------------------|
  | 2 |    0   |   24  |  24  |          24        |
  | 3 |  -36   |   78  |  42  |          42        |
  | 4 | -192   |  240  |  48  |          48        |
  | 5 | -660   |  726  |  66  |          66        |

The B values are from `BClosedForm`. The statements
`∀ d ≥ 2, R d + B d = 12·d + 6·(d mod 2)` and
`∀ d ≥ 2, R d = 3 - 3^(d+1) + 12·d + 6·(d mod 2)` are OPEN.
-/

import InfraFormalization.BClosedFormExtended

namespace InfraFormalization
namespace RClosedForm

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

/-! ## Values of R + B -/

/-- R(2) + B(2) = 0 + 24 = 24 = 12·2. -/
theorem R_plus_B_d2 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 : Int) = 24 := by
  native_decide

/-- R(3) + B(3) = -36 + 78 = 42 = 12·3 + 6. -/
theorem R_plus_B_d3 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 : Int) = 42 := by
  native_decide

/-- R(4) + B(4) = -192 + 240 = 48 = 12·4. -/
theorem R_plus_B_d4 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 : Int) = 48 := by
  native_decide

/-- R(5) + B(5) = -660 + 726 = 66 = 12·5 + 6. -/
theorem R_plus_B_d5 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 5 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 : Int) = 66 := by
  native_decide

/-! ## The four values of R + B -/

/-- R + B equals `12·d` at d = 2, 4 and `12·d + 6` at d = 3, 5 for
`edgeReversal + tripleMerger`. -/
theorem R_plus_B_closed_form :
    -- d=2 (even): 24 = 12·2
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 : Int) = 12 * 2 ∧
    -- d=3 (odd): 42 = 12·3 + 6
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 : Int) = 12 * 3 + 6 ∧
    -- d=4 (even): 48 = 12·4
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 : Int) = 12 * 4 ∧
    -- d=5 (odd): 66 = 12·5 + 6
    discreteRicciScalar edgeReversal_tripleMerger_Sys 5 +
      (discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 : Int) = 12 * 5 + 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Values of R -/

/-- R(3) = 3 - 3^4 + 12·3 + 6 = -36. -/
theorem R_explicit_closed_form_d3 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 = 3 - 3^4 + 12 * 3 + 6 := by
  native_decide

/-- R(4) = 3 - 3^5 + 12·4 = -192. -/
theorem R_explicit_closed_form_d4 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 = 3 - 3^5 + 12 * 4 := by
  native_decide

/-- R(5) = 3 - 3^6 + 12·5 + 6 = -660. -/
theorem R_explicit_closed_form_d5 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 5 = 3 - 3^6 + 12 * 5 + 6 := by
  native_decide

/-! ## Contents

  * `R_plus_B_d2` to `R_plus_B_d5`: R + B at depths 2 to 5.
  * `R_plus_B_closed_form`: the same four values written as `12·d` (even
    d) or `12·d + 6` (odd d).
  * `R_explicit_closed_form_d3` to `R_explicit_closed_form_d5`: R at
    depths 3, 4 and 5 written as `3 - 3^(d+1) + 12·d + 6·(d mod 2)`.

All statements concern `edgeReversal + tripleMerger` on `seedEdge12`.
The formulas for all d are OPEN. They do not hold for
`forkRule_2 + doubleCycle_5`, whose R is 6, 0, 0 at depths 2, 3, 4
(`PersistentRDegeneracy`).
-/

end RClosedForm
end InfraFormalization
