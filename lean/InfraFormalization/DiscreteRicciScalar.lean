/-
The integer R(rule, depth) and the product seed.length · R.

`discreteRicciScalar sys d` is the scaled Knill Euler characteristic of
`causalDAGOfFireAll sys seedEdge12 d`, the causal graph of `d`
fire-all steps from the one-edge seed `{1, 2}`. The evolution is
`fireAllStep`, which applies every match of every rule found in the
state, including matches that share edges. It is not a Wolfram model
update when matches overlap. The name is a label. The module defines
no Ricci tensor and no metric.

Values (PROVED-WITH-NATIVE-DECIDE):

  | Rule               | depth | R  |
  |--------------------|-------|----|
  | edgeReversalSys    |   5   | -6 |
  | doubleCycleSys_5   |   4   | -6 |
  | bidirectedEdgeSys  |   4   | 126|
  | identityKeepSys    |   4   | 12 |
  | forkSys_2          |   4   | 18 |
  | tripleMergerSys    |   4   |-12 |

`discreteEinsteinHilbert sys seed d` is `seed.length * R`. For
`doubleCycleSys_5` at depth 4 it equals the Knill value of the fire-all
causal graph on three seeds (`einsteinHilbert_equals_knill_doubleCycle5`).
The equality for every rule, seed and depth is OPEN.
-/

import InfraFormalization.UniversalAdditivity

namespace InfraFormalization
namespace DiscreteRicciScalar

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open UniversalAdditivity

/-! ## Definition -/

/-- `discreteRicciScalar sys d`: the scaled Knill Euler characteristic
of `causalDAGOfFireAll sys seedEdge12 d`. The name is a label. -/
def discreteRicciScalar (sys : ExecSystem) (d : Nat) : Int :=
  knillEulerScaled (causalDAGOfFireAll sys seedEdge12 d)

/-! ## Values of R -/

/-- `R(edgeReversal, 5) = -6`. -/
theorem R_edgeReversal_5 : discreteRicciScalar edgeReversalSys 5 = -6 := by
  native_decide

/-- `R(doubleCycle_5, 4) = -6`. -/
theorem R_doubleCycle_5_4 : discreteRicciScalar doubleCycleSys_5 4 = -6 := by
  native_decide

/-- `R(bidirectedEdgeSys, 4) = 126`. -/
theorem R_bidirected_4 : discreteRicciScalar bidirectedEdgeSys 4 = 126 := by
  native_decide

/-- `R(identityKeepSys, 4) = 12`. -/
theorem R_identityKeep_4 : discreteRicciScalar identityKeepSys 4 = 12 := by
  native_decide

/-- `R(forkSys_2, 4) = 18`. -/
theorem R_fork_4 : discreteRicciScalar forkSys_2 4 = 18 := by
  native_decide

/-- `R(tripleMergerSys, 4) = -12`. -/
theorem R_tripleMerger_4 : discreteRicciScalar
    DiscoveredRulesExpanded.tripleMergerSys 4 = -12 := by
  native_decide

/-! ## The product seed.length · R -/

/-- `discreteEinsteinHilbert sys seed d`: the integer
`seed.length * discreteRicciScalar sys d`. The name is a label. -/
def discreteEinsteinHilbert (sys : ExecSystem) (seed : ExecHG ℕ) (d : Nat) :
    Int :=
  (seed.length : Int) * discreteRicciScalar sys d

/-- `einsteinHilbert_equals_knill_doubleCycle5`: for `doubleCycleSys_5`
at depth 4, `discreteEinsteinHilbert` equals the scaled Knill value of
the fire-all causal graph on `seedEdge12`, `seedPath123` and
`seedTriangle`. The statement is a conjunction over these three
seeds. -/
theorem einsteinHilbert_equals_knill_doubleCycle5 :
    discreteEinsteinHilbert doubleCycleSys_5 seedEdge12 4 =
      knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedEdge12 4) ∧
    discreteEinsteinHilbert doubleCycleSys_5 seedPath123 4 =
      knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedPath123 4) ∧
    discreteEinsteinHilbert doubleCycleSys_5 seedTriangle 4 =
      knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedTriangle 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Six values -/

/-- `discreteRicciScalar_corpus`: the conjunction of the six values
above. -/
theorem discreteRicciScalar_corpus :
    discreteRicciScalar edgeReversalSys 5 = -6 ∧
    discreteRicciScalar doubleCycleSys_5 4 = -6 ∧
    discreteRicciScalar bidirectedEdgeSys 4 = 126 ∧
    discreteRicciScalar identityKeepSys 4 = 12 ∧
    discreteRicciScalar forkSys_2 4 = 18 ∧
    discreteRicciScalar DiscoveredRulesExpanded.tripleMergerSys 4 = -12 :=
  ⟨R_edgeReversal_5, R_doubleCycle_5_4, R_bidirected_4,
   R_identityKeep_4, R_fork_4, R_tripleMerger_4⟩

/-! ## Summary

  * `discreteRicciScalar sys d`: the scaled Knill value of
    `causalDAGOfFireAll sys seedEdge12 d`.
  * `discreteEinsteinHilbert sys seed d`: `seed.length * R`.
  * `discreteRicciScalar_corpus`: six values of R.
  * `einsteinHilbert_equals_knill_doubleCycle5`: for
    `doubleCycleSys_5` at depth 4, `seed.length * R` equals the Knill
    value on `seedEdge12`, `seedPath123` and `seedTriangle`.

The equality of `discreteEinsteinHilbert` with the Knill value for
every seed is OPEN. The module proves no relation to the
Einstein-Hilbert action of a Lorentzian manifold.
-/

end DiscreteRicciScalar
end InfraFormalization
