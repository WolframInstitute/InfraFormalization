/-
R at depth 4 for rule pairs, compared with sums and products of the
single-rule values.

R is `discreteRicciScalar sys d`, the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 d`. The evolution is
`fireAllStep`, which applies every match of every rule found in the
state, including matches that share edges. It is not a Wolfram model
update when matches overlap. For a rule pair with a common LHS, both
rules fire on the same edge in one step.

Values (PROVED-WITH-NATIVE-DECIDE):

  | Rule pair                   | R(pair, 4) | R(rule1, 4) | R(rule2, 4) |
  |-----------------------------|------------|-------------|-------------|
  | edgeReversal + identity     |      6     |      0      |     12      |
  | edgeReversal + fork         |    -72     |      0      |     18      |
  | edgeReversal + doubleCycle  |   -108     |      0      |     -6      |
  | fork + doubleCycle          |      0     |     18      |     -6      |
  | edgeReversal + tripleMerger |   -192     |      0      |    -12      |

`R_sum_combination_fails` gives three instances where R of the pair
differs from the sum. `R_product_combination_fails` gives one instance
where it differs from the product. The module does not consider other
combination laws, and states nothing about depths other than 4.
-/

import InfraFormalization.DiscreteRicciScalar
import InfraFormalization.MultiRuleDiscovered

namespace InfraFormalization
namespace MultiRuleRDivergence

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DiscreteRicciScalar

/-! ## R for rule pairs at depth 4 -/

theorem R_eR_id_4 : discreteRicciScalar edgeReversal_identity_Sys 4 = 6 := by
  native_decide

theorem R_eR_fork_4 : discreteRicciScalar edgeReversal_fork_Sys 4 = -72 := by
  native_decide

theorem R_eR_dCyc_4 : discreteRicciScalar edgeReversal_doubleCycle_Sys 4 = -108 := by
  native_decide

theorem R_fork_dCyc_4 : discreteRicciScalar fork_doubleCycle_Sys 4 = 0 := by
  native_decide

theorem R_eR_tripleMerger_4 : discreteRicciScalar edgeReversal_tripleMerger_Sys 4 = -192 := by
  native_decide

/-! ## Comparison with sums and products -/

/-- `R_sum_combination_fails`: at depth 4, R of the pair differs from
the sum of the single-rule values in three instances:

  * R(eR + id) = 6 and 0 + 12 = 12.
  * R(eR + fork) = -72 and 0 + 18 = 18.
  * R(eR + dCyc) = -108 and 0 + (-6) = -6. -/
theorem R_sum_combination_fails :
    discreteRicciScalar edgeReversal_identity_Sys 4 ≠
      discreteRicciScalar edgeReversalSys 4 + discreteRicciScalar identityKeepSys 4 ∧
    discreteRicciScalar edgeReversal_fork_Sys 4 ≠
      discreteRicciScalar edgeReversalSys 4 + discreteRicciScalar forkSys_2 4 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 4 ≠
      discreteRicciScalar edgeReversalSys 4 + discreteRicciScalar doubleCycleSys_5 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- `R_product_combination_fails`: R(fork + dCyc, 4) = 0 differs from
`R(forkSys_2, 4) * R(doubleCycleSys_5, 4) = 18 * (-6) = -108`. -/
theorem R_product_combination_fails :
    discreteRicciScalar fork_doubleCycle_Sys 4 ≠
      discreteRicciScalar forkSys_2 4 * discreteRicciScalar doubleCycleSys_5 4 := by
  native_decide

/-! ## Ten values -/

/-- `multi_rule_R_divergence`: R at depth 4 for five rule pairs (6,
-72, -108, 0, -192) and for five single rules (0, 12, 18, -6, -12). -/
theorem multi_rule_R_divergence :
    -- Rule pairs:
    discreteRicciScalar edgeReversal_identity_Sys 4 = 6 ∧
    discreteRicciScalar edgeReversal_fork_Sys 4 = -72 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 4 = -108 ∧
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 = -192 ∧
    -- Single rules:
    discreteRicciScalar edgeReversalSys 4 = 0 ∧
    discreteRicciScalar identityKeepSys 4 = 12 ∧
    discreteRicciScalar forkSys_2 4 = 18 ∧
    discreteRicciScalar doubleCycleSys_5 4 = -6 ∧
    discreteRicciScalar tripleMergerSys 4 = -12 :=
  ⟨R_eR_id_4, R_eR_fork_4, R_eR_dCyc_4, R_fork_dCyc_4, R_eR_tripleMerger_4,
   by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide⟩

/-! ## Summary

  * Five values of R for rule pairs and five for single rules at
    depth 4.
  * `R_sum_combination_fails`: three instances where R of a pair
    differs from the sum of the single-rule values.
  * `R_product_combination_fails`: one instance where R of a pair
    differs from the product.
  * `multi_rule_R_divergence`: the ten values.

`UniversalAdditivity.universal_additivity_multi_rule` states, for
`edgeReversal_identity_Sys` at depth 3, that the Knill value on
`seedPath123` and `seedTriangle` is 2 and 3 times the value on
`seedEdge12`.
-/

end MultiRuleRDivergence
end InfraFormalization
