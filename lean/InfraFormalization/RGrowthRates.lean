/-
R at depths 3 to 5 for two rule pairs.

R is `discreteRicciScalar sys d`, the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 d`. The evolution is
`fireAllStep`, which applies every match of every rule found in the
state, including matches that share edges. It is not a Wolfram model
update when matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE):

  | d | R(eR + tripleMerger) | R(eR + dCyc) |
  |---|----------------------|--------------|
  | 3 |         -36          |     -24      |
  | 4 |        -192          |    -108      |
  | 5 |        -660          |    -276      |

The ratio `|R(d)/R(d-1)|` is 5.33 then 3.44 for `eR + tripleMerger`,
and 4.5 then 2.56 for `eR + dCyc`. `R_growth_rates_decreasing` states
the two comparisons as integer inequalities. The module states no
growth law and no limit.
-/

import InfraFormalization.RZeroCrossings

namespace InfraFormalization
namespace RGrowthRates

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DiscreteRicciScalar

/-! ## R trajectory for eR + tripleMerger -/

theorem R_eR_tripleMerger_5 :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 5 = -660 := by
  native_decide

/-- `eR_tripleMerger_R_growth`: for `edgeReversal_tripleMerger_Sys`,
R = -36, -192, -660 at d = 3, 4, 5, `R(4) < 5 · R(3)` and
`R(5) < 3 · R(4)`. -/
theorem eR_tripleMerger_R_growth :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 = -36 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 = -192 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 5 = -660 ∧
    -- R(4) < 5·R(3): -192 < -180
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 <
      5 * discreteRicciScalar edgeReversal_tripleMerger_Sys 3 ∧
    -- R(5) < 3·R(4): -660 < -576
    discreteRicciScalar edgeReversal_tripleMerger_Sys 5 <
      3 * discreteRicciScalar edgeReversal_tripleMerger_Sys 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## R trajectory for eR + dCyc -/

theorem R_eR_dCyc_4 : discreteRicciScalar edgeReversal_doubleCycle_Sys 4 = -108 := by
  native_decide

theorem R_eR_dCyc_5 : discreteRicciScalar edgeReversal_doubleCycle_Sys 5 = -276 := by
  native_decide

/-- `eR_dCyc_R_growth`: for `edgeReversal_doubleCycle_Sys`, R = -24,
-108, -276 at d = 3, 4, 5, and `R(5) < 2 · R(4)`. -/
theorem eR_dCyc_R_growth :
    discreteRicciScalar edgeReversal_doubleCycle_Sys 3 = -24 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 4 = -108 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 5 = -276 ∧
    -- R(5) < 2·R(4): -276 < -216
    discreteRicciScalar edgeReversal_doubleCycle_Sys 5 <
      2 * discreteRicciScalar edgeReversal_doubleCycle_Sys 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Ratio comparison -/

/-- `R_growth_rates_decreasing`: the integer inequalities
`660 * 36 < 192 * 192` and `276 * 24 < 108 * 108`. With the values
above they give `|R(5)/R(4)| < |R(4)/R(3)|` for `eR + tripleMerger`
and for `eR + dCyc`. The statement mentions no rule system and is
proved by `decide`. -/
theorem R_growth_rates_decreasing :
    -- eR + tripleMerger values: 660/192 < 192/36
    -- as 660·36 < 192·192
    660 * 36 < 192 * 192 ∧
    -- eR + dCyc values: 276·24 < 108·108
    276 * 24 < 108 * 108 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Summary

  * `eR_tripleMerger_R_growth`: R = -36, -192, -660 at d = 3, 4, 5,
    with `R(4) < 5·R(3)` and `R(5) < 3·R(4)`.
  * `eR_dCyc_R_growth`: R = -24, -108, -276 at d = 3, 4, 5, with
    `R(5) < 2·R(4)`.
  * `R_growth_rates_decreasing`: two integer inequalities.

No growth law for R beyond depth 5 is stated or proved.
-/

end RGrowthRates
end InfraFormalization
