/-
A conjunction of finite computed values from several modules.

R is `discreteRicciScalar sys d`, the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 d`. B is
`discreteBranchialDensity sys d`, the scaled Knill Euler characteristic
of `branchialDAGOfFireAll sys seedEdge12 d`. The branchial graph joins
two events of the same step that consume a common edge. It is not the
Wolfram-model branchial graph. The evolution is `fireAllStep`, which
applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

The theorem `discrete_QG_predictions_capstone` collects eleven values
or comparisons at depths 2 to 6. Each is a statement about one named
rule system and one depth, PROVED-WITH-NATIVE-DECIDE.

The following statements appear in other modules as conjectures and
are OPEN; this module proves none of them:

  * For every rule, seed and depth, the causal Knill value on `seed`
    equals `seed.length * R` (and likewise for B).
  * `R(fork + dCyc, d) = 0` for every `d ≥ 3`.
  * `B(d) = 3^(d+1) - 3` for every `d ≥ 2` for
    `edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`.

The module defines no continuum limit, quantum system or gravitational
field.
-/

import InfraFormalization.BClosedFormExtended
import InfraFormalization.RZeroCrossings
import InfraFormalization.CorpusBalanceSpectrum
import InfraFormalization.DualSideIndependence

namespace InfraFormalization
namespace DiscreteQGPredictions

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
open BClosedForm
open BClosedFormExtended
open RZeroCrossings
open CorpusBalanceSpectrum
open DualSideIndependence

/-! ## The conjunction -/

/-- `discrete_QG_predictions_capstone`: the conjunction of

  1. `edgeReversal_identity_Sys` at depth 3: the causal Knill value on
     `seedPath123` is twice R.
  2. `fork_doubleCycle_Sys`: R = 0 at depth 4.
  3. `edgeReversal_tripleMerger_Sys`: B = 3^3 - 3 at depth 2 and
     B = 3^7 - 3 at depth 6.
  4. At depth 6, B for `edgeReversal_tripleMerger_Sys` equals B for
     `fork_doubleCycle_Sys`.
  5. `edgeReversal_identity_Sys` at depth 3: `5R + 4B = 0`.
  6. At depth 2, `edgeReversal_identity_Sys` and `edgeReversal_fork_Sys`
     have equal R and different B.
  7. R = 0 for `edgeReversal_tripleMerger_Sys` at depth 2, R < 0 for
     `edgeReversal_fork_Sys` at depth 5, and R = 0 for
     `fork_doubleCycle_Sys` at depth 4. -/
theorem discrete_QG_predictions_capstone :
    -- (1) seedPath123 value = 2 × seedEdge12 value:
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys
      UniversalAdditivity.seedPath123 3) =
      2 * discreteRicciScalar edgeReversal_identity_Sys 3 ∧
    -- (2) R = 0:
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 ∧
    -- (3) B = 3^(d+1) - 3 at d = 2 and d = 6:
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 = 3^3 - 3 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 6 = 3^7 - 3 ∧
    -- (4) Equal B at d = 6:
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 6 =
      discreteBranchialDensity fork_doubleCycle_Sys 6 ∧
    -- (5) 5R + 4B = 0:
    5 * discreteRicciScalar edgeReversal_identity_Sys 3 +
      4 * discreteBranchialDensity edgeReversal_identity_Sys 3 = 0 ∧
    -- (6) Same R different B:
    discreteRicciScalar edgeReversal_identity_Sys 2 =
      discreteRicciScalar edgeReversal_fork_Sys 2 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 2 ≠
      discreteBranchialDensity edgeReversal_fork_Sys 2 ∧
    -- (7) Signs of R:
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 ∧
    discreteRicciScalar edgeReversal_fork_Sys 5 < 0 ∧
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

`discrete_QG_predictions_capstone` is a conjunction of 11 integer
identities and inequalities for named rule systems on `seedEdge12`
(and `seedPath123` in conjunct 1) at depths 2 to 6. It is
PROVED-WITH-NATIVE-DECIDE. It states no continuum limit and no
statement for unbounded depth.
-/

end DiscreteQGPredictions
end InfraFormalization
