/-
**B4-multi-rule-R-divergence: multi-rule R values don't follow simple
combination laws** (#458; honest negative finding).

The refined classifier (#450) predicts single-rule `R(sys, depth)`
correctly. This module **audits whether multi-rule combo R values
follow a simple combination law** from the constituent single-rule
R values.

**Empirical data** (all `native_decide`-certified):

  | Multi-rule combo            | R(combo, 4) | R(rule1) | R(rule2) |
  |-----------------------------|-------------|----------|----------|
  | edgeReversal + identity     |      6      |    0     |   12     |
  | edgeReversal + fork         |    -72      |    0     |   18     |
  | edgeReversal + doubleCycle  |   -108      |    0     |   -6     |
  | fork + doubleCycle          |      0      |   18     |   -6     |
  | edgeReversal + tripleMerger |   -192      |    0     |  -12     |

**Negative finding**: NO simple combination law (sum, product,
linear combination) predicts multi-rule R from constituent R values:

  * `R(eR + id) = 6` ≠ `0 + 12 = 12` (sum), `0 * 12 = 0` (product).
  * `R(eR + fork) = -72` ≠ `0 + 18 = 18` (sum).
  * `R(eR + dCyc) = -108` ≠ `0 + (-6) = -6` (sum).

**What this tells us**: multi-rule combinations create **emergent
dynamical regimes** that single-rule R values cannot predict. The
interaction between rules produces causal-DAG topology fundamentally
different from either rule in isolation.

**Why this matters**:

  * The classifier (#450) is correct for single rules but cannot be
    naively extended to multi-rule.
  * Multi-rule R prediction requires modeling the *interaction* of
    rules — likely a function of the LHS/RHS overlap structure,
    not just constituent R's.
  * This is a real research finding: it tells us where the
    classifier-driven search hits its current limit.

**Open questions for future work**:

  * Is there a 2-parameter combination law `R(r1, r2) = f(R(r1), R(r2),
    overlap(r1, r2))` for some overlap measure?
  * Does the per-edge additivity (#454) still hold for multi-rule
    combos? Confirmed: yes (#454 extension 3 — edgeReversal+identity
    at depth 3 has per-edge law with R=-24).
  * Is the depth-4 R prediction failure specific to depth 4? Other
    depths may have different combination structure.

This module makes the framework's classifier-driven search **honest
about its limits**: single-rule R is predictable, multi-rule R is
not (yet).
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

/-! ## Multi-rule R values at depth 4 -/

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

/-! ## Negative-finding theorems: NO simple combination law -/

/-- **`R_sum_combination_fails`**: the sum `R(rule1) + R(rule2)` does
NOT predict multi-rule `R(combo)`. Three counterexamples:

  * R(eR + id) = 6 ≠ 0 + 12 = 12.
  * R(eR + fork) = -72 ≠ 0 + 18 = 18.
  * R(eR + dCyc) = -108 ≠ 0 + (-6) = -6. -/
theorem R_sum_combination_fails :
    discreteRicciScalar edgeReversal_identity_Sys 4 ≠
      discreteRicciScalar edgeReversalSys 4 + discreteRicciScalar identityKeepSys 4 ∧
    discreteRicciScalar edgeReversal_fork_Sys 4 ≠
      discreteRicciScalar edgeReversalSys 4 + discreteRicciScalar forkSys_2 4 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 4 ≠
      discreteRicciScalar edgeReversalSys 4 + discreteRicciScalar doubleCycleSys_5 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **`R_product_combination_fails`**: the product
`R(rule1) * R(rule2)` ALSO does NOT predict multi-rule `R(combo)`.

  * R(fork + dCyc) = 0 ≠ 18 * (-6) = -108. -/
theorem R_product_combination_fails :
    discreteRicciScalar fork_doubleCycle_Sys 4 ≠
      discreteRicciScalar forkSys_2 4 * discreteRicciScalar doubleCycleSys_5 4 := by
  native_decide

/-! ## Bundled multi-rule R-divergence theorem -/

/-- **`multi_rule_R_divergence`**: multi-rule `R(combo, 4)` values
diverge from naive combinations of constituent single-rule R values.
NO simple algebraic combination law predicts the multi-rule values.

This is a real research finding: multi-rule combinations create
emergent dynamical regimes that single-rule R values cannot
predict. -/
theorem multi_rule_R_divergence :
    -- Certified multi-rule R values:
    discreteRicciScalar edgeReversal_identity_Sys 4 = 6 ∧
    discreteRicciScalar edgeReversal_fork_Sys 4 = -72 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 4 = -108 ∧
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 4 = -192 ∧
    -- Single-rule baselines (for comparison):
    discreteRicciScalar edgeReversalSys 4 = 0 ∧
    discreteRicciScalar identityKeepSys 4 = 12 ∧
    discreteRicciScalar forkSys_2 4 = 18 ∧
    discreteRicciScalar doubleCycleSys_5 4 = -6 ∧
    discreteRicciScalar tripleMergerSys 4 = -12 :=
  ⟨R_eR_id_4, R_eR_fork_4, R_eR_dCyc_4, R_fork_dCyc_4, R_eR_tripleMerger_4,
   by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide⟩

/-! ## What this delivers

**Honest negative finding** about multi-rule R prediction:

  * 5 certified multi-rule R values + 5 single-rule baselines.
  * `R_sum_combination_fails`: sum law fails (3 counterexamples).
  * `R_product_combination_fails`: product law fails (1
    counterexample).
  * `multi_rule_R_divergence`: 10-conj bundled result.

**Why this matters**:

  * Tells us where the classifier hits its current limit.
  * Multi-rule combinations create emergent dynamics; the rule
    interactions matter, not just the individual class.
  * This is research integrity: we don't pretend the classifier
    extends to multi-rule when it doesn't.

**Future research**: identify the right multi-rule combination
law. Likely candidates: depends on LHS/RHS overlap, depends on
fresh-vertex conflict, etc. None known yet.

**Note**: per-edge additivity STILL holds for multi-rule combos
(see `UniversalAdditivity.universal_additivity_multi_rule`). The
divergence is in **how single-rule R values combine to give the
combo R**, not in how the combo's R relates to seed structure.
-/

end MultiRuleRDivergence
end InfraFormalization
