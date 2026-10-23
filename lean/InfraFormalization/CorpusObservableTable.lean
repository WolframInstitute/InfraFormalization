/-
A table of `discreteRicciScalar` (R) and `discreteBranchialDensity` (B)
for five two-rule systems at depth 3 on the single edge `seedEdge12`.

R is the scaled Knill value of `causalDAGOfFireAll sys seedEdge12 3`. B
is the scaled Knill value of `branchialDAGOfFireAll sys seedEdge12 3`,
the graph that links two events of the same step that consume a common
edge value. This relation is not the branchial graph of the Wolfram
model. Both graphs come from `tracedFireAllEvolve`, which applies every
match of every rule found in the state, including matches that share
edges. It is not a Wolfram model update when matches overlap.

`DiscreteMetricTensor.hasLorentzianSignature sys d` is `true` when R and
B are nonzero and of opposite sign.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | System                       | R    | B   | `hasLorentzianSignature` |
  |------------------------------|------|-----|--------------------------|
  | edgeReversal + identityKeep  | -24  | 30  | true                     |
  | edgeReversal + forkRule_2    | -42  | 66  | true                     |
  | edgeReversal + doubleCycle_5 | -24  | 42  | true                     |
  | forkRule_2 + doubleCycle_5   |   0  | 78  | false                    |
  | edgeReversal + tripleMerger  | -36  | 78  | true                     |

For `forkRule_2 + doubleCycle_5`, R is 0 while R of each of its two rules
alone is nonzero. `edgeReversal + tripleMerger` and
`forkRule_2 + doubleCycle_5` have the same B and different R.
-/

import InfraFormalization.CorpusBalanceSpectrum
import InfraFormalization.DiscreteMetricTensor

namespace InfraFormalization
namespace CorpusObservableTable

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
open DiscreteMetricTensor

/-! ## Corpus values for fork + doubleCycle -/

theorem R_fork_dCyc_3 : discreteRicciScalar fork_doubleCycle_Sys 3 = 0 := by
  native_decide

theorem B_fork_dCyc_3 : discreteBranchialDensity fork_doubleCycle_Sys 3 = 78 := by
  native_decide

/-- For `edgeReversal + doubleCycle_5` at depth 3: R = -24 and B = 42. -/
theorem RB_eR_dCyc_3 :
    discreteRicciScalar edgeReversal_doubleCycle_Sys 3 = -24 ∧
    discreteBranchialDensity edgeReversal_doubleCycle_Sys 3 = 42 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## The table -/

/-- The pairs `discreteMetricTensor sys 3 = (R, B)` for five two-rule
systems:

  * `edgeReversal + identityKeep`: (-24, 30).
  * `edgeReversal + forkRule_2`: (-42, 66).
  * `edgeReversal + doubleCycle_5`: (-24, 42).
  * `forkRule_2 + doubleCycle_5`: (0, 78).
  * `edgeReversal + tripleMerger`: (-36, 78).
-/
theorem corpus_observable_table :
    discreteMetricTensor edgeReversal_identity_Sys 3 = (-24, 30) ∧
    discreteMetricTensor edgeReversal_fork_Sys 3 = (-42, 66) ∧
    discreteMetricTensor edgeReversal_doubleCycle_Sys 3 = (-24, 42) ∧
    discreteMetricTensor fork_doubleCycle_Sys 3 = (0, 78) ∧
    discreteMetricTensor edgeReversal_tripleMerger_Sys 3 = (-36, 78) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- `hasLorentzianSignature sys 3` is `true` for four of the five
systems and `false` for `forkRule_2 + doubleCycle_5`, whose R is 0. -/
theorem corpus_signature_classification :
    hasLorentzianSignature edgeReversal_identity_Sys 3 = true ∧
    hasLorentzianSignature edgeReversal_fork_Sys 3 = true ∧
    hasLorentzianSignature edgeReversal_doubleCycle_Sys 3 = true ∧
    hasLorentzianSignature fork_doubleCycle_Sys 3 = false ∧
    hasLorentzianSignature edgeReversal_tripleMerger_Sys 3 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## R of `forkRule_2 + doubleCycle_5` and of its two rules -/

/-- At depth 3 on `seedEdge12`, `discreteRicciScalar` is 0 for the
two-rule system `forkRule_2 + doubleCycle_5`, and is nonzero for each of
the single-rule systems `forkSys_2` and `doubleCycleSys_5`. -/
theorem R_degeneracy_from_interaction :
    discreteRicciScalar fork_doubleCycle_Sys 3 = 0 ∧
    discreteRicciScalar forkSys_2 3 ≠ 0 ∧
    discreteRicciScalar doubleCycleSys_5 3 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Equal B, different R -/

/-- At depth 3, `edgeReversal + tripleMerger` and
`forkRule_2 + doubleCycle_5` have equal B (78) and different R (-36 and
0). -/
theorem same_B_different_R :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 ≠
      discreteRicciScalar fork_doubleCycle_Sys 3 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `R_fork_dCyc_3`, `B_fork_dCyc_3`, `RB_eR_dCyc_3`: four values.
  * `corpus_observable_table`: the five pairs `(R, B)` at depth 3.
  * `corpus_signature_classification`: the five values of
    `hasLorentzianSignature` at depth 3.
  * `R_degeneracy_from_interaction`: R = 0 for `forkRule_2 + doubleCycle_5`
    and R ≠ 0 for each of its two rules alone.
  * `same_B_different_R`: equal B and different R for
    `edgeReversal + tripleMerger` and `forkRule_2 + doubleCycle_5`.

All statements concern depth 3 and the seed `seedEdge12`.
-/

end CorpusObservableTable
end InfraFormalization
