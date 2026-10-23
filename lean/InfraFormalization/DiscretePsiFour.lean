/-
A list of integer pairs built from the fire-all evolution.

`discretePsiFour sys H n` is a list of `n` pairs. The first entry of the
k-th pair is the change in the scaled Knill value of
`causalDAGOfFireAll sys H` from depth k to depth k+1. The second entry is
the number of events at step k (`DiscreteBondiFlux.perStepEventCount`).
`fireAllStep` applies every match of every rule found in the state,
including matches that share edges. It is not a Wolfram model update
when matches overlap.

The module name refers to the Newman-Penrose scalar Ψ₄. The module does
not define a Weyl tensor, a tetrad, a complex number or any spacetime
quantity. `psiFourModSq` is the sum of the squares of the two entries,
and `integratedModSq` is its sum over a list.

For `edgeReversal + tripleMerger` on `seedEdge12` the module computes by
`native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | step k | event count | Knill at depth k+1 | change |
  |--------|-------------|--------------------|--------|
  |   0    |    2        |     0              |     0  |
  |   1    |    6        |     0              |     0  |
  |   2    |   18        |   -36              |   -36  |
  |   3    |   54        |  -192              |  -156  |
-/

import InfraFormalization.MergerGrowthDepthTrajectory
import InfraFormalization.DiscreteBondiFlux

namespace InfraFormalization
namespace DiscretePsiFour

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open BBHInitialData
open MultiRuleDiscovered
open DiscreteBondiFlux
open MergerGrowthDepthTrajectory

/-! ## Definition -/

/-- `discretePsiFour sys H n` is the list of `n` integer pairs. The k-th
pair has first entry `K(k+1) - K(k)`, where `K(j)` is the scaled Knill
value of `causalDAGOfFireAll sys H j`, and second entry the k-th entry
of `perStepEventCount sys H n`. -/
def discretePsiFour (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    List (Int × Nat) :=
  let flux := perStepEventCount sys H n
  let knills := (List.range (n+1)).map (fun k =>
    knillEulerScaled (causalDAGOfFireAll sys H k))
  let deltas := (List.range n).map (fun k =>
    (knills.getD (k+1) 0) - (knills.getD k 0))
  deltas.zip flux

/-! ## Sums of squares -/

/-- `psiFourModSq (a, b) = a² + b²`. -/
def psiFourModSq (entry : Int × Nat) : Int :=
  entry.1 * entry.1 + (entry.2 : Int) * (entry.2 : Int)

/-- `integratedModSq` is the sum of `psiFourModSq` over a list. -/
def integratedModSq (psi : List (Int × Nat)) : Int :=
  (psi.map psiFourModSq).foldr (· + ·) 0

/-! ## `edgeReversal` on `seedEdge12` -/

/-- `discretePsiFour` of `edgeReversal` on `seedEdge12` over 6 steps.

Scaled causal Knill values at depths 0 to 6: 0, 0, 6, 6, 0, -6, -18.
Differences: 0, 6, 0, -6, -6, -12.
Per-step event count: 1 at every step.

List: (0,1), (6,1), (0,1), (-6,1), (-6,1), (-12,1). -/
theorem edgeReversal_psi4_trajectory :
    discretePsiFour edgeReversalSys seedEdge12 6 =
      [(0, 1), (6, 1), (0, 1), (-6, 1), (-6, 1), (-12, 1)] := by
  native_decide

/-! ## `edgeReversal + tripleMerger` on `seedEdge12` -/

/-- `discretePsiFour` of `edgeReversal + tripleMerger` on `seedEdge12`
over 4 steps is `[(0, 2), (0, 6), (-36, 18), (-156, 54)]`. -/
theorem exponential_psi4_signature :
    discretePsiFour edgeReversal_tripleMerger_Sys seedEdge12 4 =
      [(0, 2), (0, 6), (-36, 18), (-156, 54)] := by
  native_decide

/-! ## Sum of squares for `edgeReversal + tripleMerger` -/

/-- `integratedModSq` of the `edgeReversal + tripleMerger` list on
`seedEdge12` over 4 steps:

Σ (re² + im²) = (0 + 4) + (0 + 36) + (1296 + 324) + (24336 + 2916)
              =  4 + 36 + 1620 + 27252 = 28912 -/
theorem integrated_psi4_modsq_champion :
    integratedModSq (discretePsiFour edgeReversal_tripleMerger_Sys seedEdge12 4) = 28912 := by
  native_decide

/-! ## Sum of squares for `edgeReversal` -/

/-- `integratedModSq` of the `edgeReversal` list on `seedEdge12` over 6
steps:

Σ = (0+1) + (36+1) + (0+1) + (36+1) + (36+1) + (144+1)
  = 1 + 37 + 1 + 37 + 37 + 145 = 258 -/
theorem integrated_psi4_modsq_baseline :
    integratedModSq (discretePsiFour edgeReversalSys seedEdge12 6) = 258 := by
  native_decide

/-! ## A literal list with entries 7 times those of `exponential_psi4_signature`

`bbhPsiFourPredicted_tripleMerger` is written out as a literal. It is not
computed from any evolution, and the module does not prove that it equals
`discretePsiFour edgeReversal_tripleMerger_Sys bbhInitial 4`. Because
every entry is 7 times the corresponding entry of the `seedEdge12` list,
its sum of squares is 49 times 28912. -/

/-- The literal list `[(0, 14), (0, 42), (-252, 126), (-1092, 378)]`.
Each entry is 7 times the corresponding entry of
`discretePsiFour edgeReversal_tripleMerger_Sys seedEdge12 4`. -/
def bbhPsiFourPredicted_tripleMerger : List (Int × Nat) :=
  [(0, 14), (0, 42), (-252, 126), (-1092, 378)]

/-- `integratedModSq bbhPsiFourPredicted_tripleMerger = 49 * 28912`.
The statement is arithmetic on the literal list. -/
theorem bbh_psi4_predicted_modsq :
    integratedModSq bbhPsiFourPredicted_tripleMerger = 49 * 28912 := by
  native_decide

/-! ## Contents

  * `discretePsiFour`: the list of pairs (change of scaled causal Knill
    value, per-step event count).
  * `psiFourModSq`, `integratedModSq`: the sum of squares of a pair and
    its sum over a list.
  * `edgeReversal_psi4_trajectory`, `exponential_psi4_signature`: two
    computed lists on `seedEdge12`.
  * `integrated_psi4_modsq_baseline` (258), `integrated_psi4_modsq_champion`
    (28912): their sums of squares.
  * `bbhPsiFourPredicted_tripleMerger`, `bbh_psi4_predicted_modsq`: a
    literal list and its sum of squares, 49 · 28912.

The module computes no list on `bbhInitial`, and states nothing about a
continuum limit or a waveform.
-/

end DiscretePsiFour
end InfraFormalization
