/-
Values of `hasLorentzianSignature` at depths 2, 3 and 4 for two two-rule
systems on `seedEdge12`.

`DiscreteMetricTensor.discreteMetricTensor sys d` is the integer pair
`(R, B)`. R is the scaled Knill value of
`causalDAGOfFireAll sys seedEdge12 d`. B is the scaled Knill value of
`branchialDAGOfFireAll sys seedEdge12 d`, the graph that links two
events of the same step that consume a common edge value. This relation
is not the branchial graph of the Wolfram model. Both graphs come from
`tracedFireAllEvolve`, which applies every match of every rule found in
the state, including matches that share edges. It is not a Wolfram model
update when matches overlap. `hasLorentzianSignature sys d` is `true`
when R and B are nonzero and of opposite sign. The names "metric" and
"Lorentzian" refer to this sign test on two integers.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  `edgeReversal + identityKeep`:

  | depth | R   | B  | `hasLorentzianSignature` |
  |-------|-----|----|--------------------------|
  |   2   | -6  | 18 | true                     |
  |   3   | -24 | 30 | true                     |
  |   4   |  6  | 42 | false                    |

  `edgeReversal + forkRule_2`:

  | depth | R    | B   | `hasLorentzianSignature` |
  |-------|------|-----|--------------------------|
  |   2   |  -6  |  24 | true                     |
  |   3   |  -42 |  66 | true                     |
  |   4   |  -72 | 168 | true                     |
-/

import InfraFormalization.DiscreteMetricTensor

namespace InfraFormalization
namespace MetricSignatureEvolution

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity
open DiscreteMetricTensor

/-! ## `edgeReversal + identityKeep` -/

theorem eR_id_metric_2 :
    discreteMetricTensor edgeReversal_identity_Sys 2 = (-6, 18) := by
  native_decide

theorem eR_id_metric_4 :
    discreteMetricTensor edgeReversal_identity_Sys 4 = (6, 42) := by
  native_decide

/-- `hasLorentzianSignature edgeReversal_identity_Sys d` is `true` for
d = 2 and d = 3 and `false` for d = 4, where R = 6 and B = 42 are both
positive. -/
theorem eR_id_signature_changes :
    -- Depths 2 and 3: R < 0 and B > 0:
    hasLorentzianSignature edgeReversal_identity_Sys 2 = true ∧
    hasLorentzianSignature edgeReversal_identity_Sys 3 = true ∧
    -- Depth 4: R > 0 and B > 0, so the predicate is false:
    hasLorentzianSignature edgeReversal_identity_Sys 4 = false := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## `edgeReversal + forkRule_2` -/

theorem eR_fork_metric_2 :
    discreteMetricTensor edgeReversal_fork_Sys 2 = (-6, 24) := by
  native_decide

theorem eR_fork_metric_4 :
    discreteMetricTensor edgeReversal_fork_Sys 4 = (-72, 168) := by
  native_decide

/-- `hasLorentzianSignature edgeReversal_fork_Sys d = true` for
d = 2, 3, 4. -/
theorem eR_fork_persistently_lorentzian :
    hasLorentzianSignature edgeReversal_fork_Sys 2 = true ∧
    hasLorentzianSignature edgeReversal_fork_Sys 3 = true ∧
    hasLorentzianSignature edgeReversal_fork_Sys 4 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Four Boolean values at depths 3 and 4 -/

/-- `hasLorentzianSignature` at depths 3 and 4: `true`, `false` for
`edgeReversal + identityKeep`, and `true`, `true` for
`edgeReversal + forkRule_2`. -/
theorem signature_evolution_dichotomy :
    -- eR + id: true at depth 3, false at depth 4:
    hasLorentzianSignature edgeReversal_identity_Sys 3 = true ∧
    hasLorentzianSignature edgeReversal_identity_Sys 4 = false ∧
    -- eR + fork: true at depths 3 and 4:
    hasLorentzianSignature edgeReversal_fork_Sys 3 = true ∧
    hasLorentzianSignature edgeReversal_fork_Sys 4 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `eR_id_metric_2`, `eR_id_metric_4`, `eR_fork_metric_2`,
    `eR_fork_metric_4`: four pairs `(R, B)`.
  * `eR_id_signature_changes`: `hasLorentzianSignature` is `true` at
    depths 2 and 3 and `false` at depth 4 for
    `edgeReversal + identityKeep`.
  * `eR_fork_persistently_lorentzian`: `hasLorentzianSignature` is `true`
    at depths 2, 3 and 4 for `edgeReversal + forkRule_2`.
  * `signature_evolution_dichotomy`: four of these Boolean values.

All statements concern two systems, depths 2 to 4, and the seed
`seedEdge12`. The module defines no metric on a manifold and states
nothing about a continuum limit.
-/

end MetricSignatureEvolution
end InfraFormalization
