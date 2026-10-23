/-
Seven times the one-edge R values for two rule pairs.

`discreteRicciScalar sys d` is the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 d`. The evolution is
`fireAllStep`, which applies every match of every rule found in the
state, including matches that share edges. It is not a Wolfram model
update when matches overlap.

The theorems below state `7 * discreteRicciScalar sys d` for
`sys = edgeReversal_tripleMerger_Sys` and
`sys = edgeReversal_doubleCycle_Sys` at depths 2 to 5. These are
values on `seedEdge12` multiplied by 7. They are not computed on
`bbhInitial`. Only `BBH_universal_additivity_at_d3` evaluates the
fire-all causal graph on `bbhInitial`, for one rule pair at depth 3.
No theorem states that the factor 7 holds at other depths or for
other rules. All values are PROVED-WITH-NATIVE-DECIDE.

  For `eR + tripleMerger`:

  | d | R_edge12 |     7·R_edge12      |
  |---|----------|---------------------|
  | 2 |     0    |          0           |
  | 3 |   -36    |       -252           |
  | 4 |  -192    |      -1344           |
  | 5 |  -660    |      -4620           |

  For `eR + dCyc`:

  | d | R_edge12 |     7·R_edge12      |
  |---|----------|---------------------|
  | 2 |     0    |          0           |
  | 3 |   -24    |       -168           |
  | 4 |  -108    |       -756           |
  | 5 |  -276    |      -1932           |

The column `7·R_edge12` is the product stated in the theorems. It
equals the value on `bbhInitial` only where a theorem evaluates
`bbhInitial` directly (depth 3, `eR + tripleMerger`).
-/

import InfraFormalization.RGrowthRates
import InfraFormalization.BBHInitialData

namespace InfraFormalization
namespace BBHCurvatureEvolution

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open BBHInitialData
open DiscreteRicciScalar

/-! ## 7 · R for eR + tripleMerger -/

/-- `BBH_R_eR_tripleMerger_predicted`: `7 * discreteRicciScalar` of
`edgeReversal_tripleMerger_Sys` at depths 2, 3, 4, 5 is 0, -252,
-1344, -4620 (one-edge values 0, -36, -192, -660). -/
theorem BBH_R_eR_tripleMerger_predicted :
    7 * discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 ∧
    7 * discreteRicciScalar edgeReversal_tripleMerger_Sys 3 = -252 ∧
    7 * discreteRicciScalar edgeReversal_tripleMerger_Sys 4 = -1344 ∧
    7 * discreteRicciScalar edgeReversal_tripleMerger_Sys 5 = -4620 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## 7 · R for eR + dCyc -/

/-- `BBH_R_eR_dCyc_predicted`: `7 * discreteRicciScalar` of
`edgeReversal_doubleCycle_Sys` at depths 2, 3, 4, 5 is 0, -168,
-756, -1932. -/
theorem BBH_R_eR_dCyc_predicted :
    7 * discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 ∧
    7 * discreteRicciScalar edgeReversal_doubleCycle_Sys 3 = -168 ∧
    7 * discreteRicciScalar edgeReversal_doubleCycle_Sys 4 = -756 ∧
    7 * discreteRicciScalar edgeReversal_doubleCycle_Sys 5 = -1932 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## 7 · R = 0 at depth 2 -/

/-- `BBH_R_zero_at_init`: `7 * discreteRicciScalar` is 0 at depth 2
for both rule pairs. The value is computed on `seedEdge12`. -/
theorem BBH_R_zero_at_init :
    7 * discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 ∧
    7 * discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Direct evaluation on bbhInitial at depth 3 -/

/-- `BBH_universal_additivity_at_d3`: for `edgeReversal_tripleMerger_Sys`
at depth 3, the scaled Knill value of the fire-all causal graph on
`bbhInitial` equals 7 times the value on `seedEdge12`. -/
theorem BBH_universal_additivity_at_d3 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_tripleMerger_Sys bbhInitial 3) =
      7 * discreteRicciScalar edgeReversal_tripleMerger_Sys 3 := by
  native_decide

/-! ## Summary

  * `BBH_R_eR_tripleMerger_predicted`: four values of `7 · R` for
    eR + tripleMerger.
  * `BBH_R_eR_dCyc_predicted`: four values of `7 · R` for eR + dCyc.
  * `BBH_R_zero_at_init`: both pairs give 0 at depth 2.
  * `BBH_universal_additivity_at_d3`: the factor 7 holds on
    `bbhInitial` for eR + tripleMerger at depth 3.

Whether the factor 7 holds at other depths or for other rules is
OPEN; no theorem in this module states it.
-/

end BBHCurvatureEvolution
end InfraFormalization
