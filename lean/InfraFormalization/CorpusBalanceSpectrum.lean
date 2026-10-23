/-
The ratio -R/B at depth 3 for three rule pairs.

R is `discreteRicciScalar sys 3`, the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 3`. B is
`discreteBranchialDensity sys 3`, the scaled Knill Euler characteristic
of `branchialDAGOfFireAll sys seedEdge12 3`. The branchial graph joins
two events of the same step that consume a common edge. It is not the
Wolfram-model branchial graph. The evolution is `fireAllStep`, which
applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

The ratio α* = -R/B is the value of α for which `R + α·B = 0`. Each
ratio is stated as an integer identity `b·R + a·B = 0`
(PROVED-WITH-NATIVE-DECIDE):

  | Rule pair                   | R(d=3) | B(d=3) | -R/B  |
  |-----------------------------|--------|--------|-------|
  | edgeReversal + identityKeep |  -24   |   30   |  4/5  |
  | edgeReversal + forkRule_2   |  -42   |   66   |  7/11 |
  | edgeReversal + tripleMerger |  -36   |   78   |  6/13 |

The module defines no coupling constant and no continuum limit.
-/

import InfraFormalization.UnifiedEHBalance

namespace InfraFormalization
namespace CorpusBalanceSpectrum

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open BBHInitialData
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## R and B for eR + tripleMerger at depth 3 -/

theorem R_eR_tripleMerger_3 : discreteRicciScalar edgeReversal_tripleMerger_Sys 3 = -36 := by
  native_decide

theorem B_eR_tripleMerger_3 : discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 78 := by
  native_decide

/-! ## Ratio for eR + tripleMerger -/

/-- `balance_eR_tripleMerger`: at depth 3,
`13 * R + 6 * B = 0` for `edgeReversal_tripleMerger_Sys`, so
`-R/B = 36/78 = 6/13`. -/
theorem balance_eR_tripleMerger :
    13 * discreteRicciScalar edgeReversal_tripleMerger_Sys 3 +
      6 * discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 0 := by
  native_decide

/-! ## Ratios for three rule pairs -/

/-- `corpus_balance_spectrum`: at depth 3, `5R + 4B = 0` for
`edgeReversal_identity_Sys`, `11R + 7B = 0` for `edgeReversal_fork_Sys`
and `13R + 6B = 0` for `edgeReversal_tripleMerger_Sys`. -/
theorem corpus_balance_spectrum :
    -- eR + id: -R/B = 4/5
    5 * discreteRicciScalar edgeReversal_identity_Sys 3 +
      4 * discreteBranchialDensity edgeReversal_identity_Sys 3 = 0 ∧
    -- eR + fork: -R/B = 7/11
    11 * discreteRicciScalar edgeReversal_fork_Sys 3 +
      7 * discreteBranchialDensity edgeReversal_fork_Sys 3 = 0 ∧
    -- eR + tripleMerger: -R/B = 6/13
    13 * discreteRicciScalar edgeReversal_tripleMerger_Sys 3 +
      6 * discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Order of the three ratios -/

/-- `most_GR_like_combo`: the integer inequalities `6 * 5 < 13 * 4`
and `6 * 11 < 13 * 7`, which give `6/13 < 4/5` and `6/13 < 7/11`.
The statement mentions no rule system. It is proved by `decide`. -/
theorem most_GR_like_combo :
    -- 6/13 < 4/5: cross-multiplication 6 * 5 < 13 * 4
    6 * 5 < 13 * 4 ∧
    -- 6/13 < 7/11: cross-multiplication 6 * 11 < 13 * 7
    6 * 11 < 13 * 7 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Summary

  * `corpus_balance_spectrum`: `b·R + a·B = 0` at depth 3 for three
    rule pairs, with a/b equal to 4/5, 7/11 and 6/13.
  * `balance_eR_tripleMerger`: the 6/13 case.
  * `most_GR_like_combo`: the integer inequalities `6·5 < 13·4` and
    `6·11 < 13·7`.
-/

end CorpusBalanceSpectrum
end InfraFormalization
