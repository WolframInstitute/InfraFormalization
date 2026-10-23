/-
Per-step event counts of the fire-all evolution.

`perStepEventCount sys H n` lists, for each of the first `n` steps, the
number of events of `tracedFireAllEvolve sys H n` with that step index.
`fireAllStep` applies every match of every rule found in the state,
including matches that share edges. It is not a Wolfram model update
when matches overlap. The module name refers to the Bondi flux of
general relativity. The module does not define a flux, an energy or any
spacetime quantity. It defines and computes the counts below.

The seeds are `seedEdge12` (one edge) and `bbhInitial` (7 edges: two
triangles on `{0,1,2}` and `{3,4,5}` joined by the edge `{2,3}`). The
module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | System                       | seed         | steps | per-step counts           |
  |------------------------------|--------------|-------|---------------------------|
  | edgeReversal                 | bbhInitial   | 6     | 7, 7, 7, 7, 7, 7          |
  | doubleCycle_5                | bbhInitial   | 5     | 7, 14, 28, 56, 112        |
  | edgeReversal + tripleMerger  | bbhInitial   | 4     | 14, 42, 126, 378          |
  | edgeReversal + forkRule_2    | bbhInitial   | 5     | 14, 42, 98, 238, 574      |
  | edgeReversal                 | seedEdge12   | 6     | 1, 1, 1, 1, 1, 1          |
  | doubleCycle_5                | seedEdge12   | 5     | 1, 2, 4, 8, 16            |
  | edgeReversal + tripleMerger  | seedEdge12   | 4     | 2, 6, 18, 54              |

For the first three systems, the counts on `bbhInitial` are 7 times the
counts on `seedEdge12` at every computed step.
-/

import InfraFormalization.BBHInitialData
import InfraFormalization.MultiRuleDiscovered

namespace InfraFormalization
namespace DiscreteBondiFlux

open MultiwayExec
open RuleSignatureExecMetrics
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open BBHInitialData
open MultiRuleDiscovered

/-! ## Per-step event count definition -/

/-- `perStepEventCount sys H n` is the list, for k = 0, ..., n-1, of the
number of events with step index k in `tracedFireAllEvolve sys H n`. -/
def perStepEventCount (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    List Nat :=
  let (_, events) := tracedFireAllEvolve sys H n
  (List.range n).map (fun k => (events.filter (·.step == k)).length)

/-! ## Per-step counts on `bbhInitial` -/

/-- `edgeReversal` on `bbhInitial`: per-step count 7 at each of 6 steps. -/
theorem edgeReversal_bbh_flux :
    perStepEventCount edgeReversalSys bbhInitial 6 = [7, 7, 7, 7, 7, 7] := by
  native_decide

/-- `doubleCycle_5` on `bbhInitial`: per-step counts 7, 14, 28, 56, 112 over 5 steps. -/
theorem doubleCycle_5_bbh_flux :
    perStepEventCount doubleCycleSys_5 bbhInitial 5 = [7, 14, 28, 56, 112] := by
  native_decide

/-- `edgeReversal + tripleMerger` on `bbhInitial`: per-step counts
14, 42, 126, 378 over 4 steps. -/
theorem edgeReversal_tripleMerger_bbh_flux :
    perStepEventCount edgeReversal_tripleMerger_Sys bbhInitial 4 = [14, 42, 126, 378] := by
  native_decide

/-- `edgeReversal + forkRule_2` on `bbhInitial`: per-step counts
14, 42, 98, 238, 574 over 5 steps. -/
theorem edgeReversal_fork_bbh_flux :
    perStepEventCount edgeReversal_fork_Sys bbhInitial 5 = [14, 42, 98, 238, 574] := by
  native_decide

/-! ## Per-step counts on `seedEdge12` -/

/-- `edgeReversal` on `seedEdge12`: per-step count 1 at each of 6 steps. -/
theorem edgeReversal_edge12_flux :
    perStepEventCount edgeReversalSys seedEdge12 6 = [1, 1, 1, 1, 1, 1] := by
  native_decide

/-- `doubleCycle_5` on `seedEdge12`: per-step counts 1, 2, 4, 8, 16 over 5 steps. -/
theorem doubleCycle_5_edge12_flux :
    perStepEventCount doubleCycleSys_5 seedEdge12 5 = [1, 2, 4, 8, 16] := by
  native_decide

/-- `edgeReversal + tripleMerger` on `seedEdge12`: per-step counts
2, 6, 18, 54 over 4 steps. -/
theorem edgeReversal_tripleMerger_edge12_flux :
    perStepEventCount edgeReversal_tripleMerger_Sys seedEdge12 4 = [2, 6, 18, 54] := by
  native_decide

/-! ## Factor 7 between the two seeds -/

/-- For `edgeReversalSys` over 6 steps, `doubleCycleSys_5` over 5 steps
and `edgeReversal + tripleMerger` over 4 steps, the per-step count list
on `bbhInitial` equals the list on `seedEdge12` with every entry
multiplied by 7. -/
theorem bbh_flux_equals_7x_baseline :
    perStepEventCount edgeReversalSys bbhInitial 6 =
      (perStepEventCount edgeReversalSys seedEdge12 6).map (· * 7) ∧
    perStepEventCount doubleCycleSys_5 bbhInitial 5 =
      (perStepEventCount doubleCycleSys_5 seedEdge12 5).map (· * 7) ∧
    perStepEventCount edgeReversal_tripleMerger_Sys bbhInitial 4 =
      (perStepEventCount edgeReversal_tripleMerger_Sys seedEdge12 4).map (· * 7) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeReversal_bbh_flux, edgeReversal_edge12_flux]; rfl
  · rw [doubleCycle_5_bbh_flux, doubleCycle_5_edge12_flux]; rfl
  · rw [edgeReversal_tripleMerger_bbh_flux, edgeReversal_tripleMerger_edge12_flux]; rfl

/-! ## Ratios of consecutive counts -/

/-- The per-step counts of `edgeReversal + tripleMerger` on `bbhInitial`
over 4 steps are `[14, 42, 126, 378]`, together with the integer
identities 42 = 3·14, 126 = 3·42 and 378 = 3·126. -/
theorem exponential_merger_growth_x3 :
    perStepEventCount edgeReversal_tripleMerger_Sys bbhInitial 4 = [14, 42, 126, 378] ∧
    42 = 3 * 14 ∧
    126 = 3 * 42 ∧
    378 = 3 * 126 :=
  ⟨edgeReversal_tripleMerger_bbh_flux, by decide, by decide, by decide⟩

/-- The per-step counts of `doubleCycleSys_5` on `bbhInitial` over 5
steps are `[7, 14, 28, 56, 112]`, together with the integer identities
14 = 2·7, 28 = 2·14, 56 = 2·28 and 112 = 2·56. -/
theorem exponential_merger_growth_x2 :
    perStepEventCount doubleCycleSys_5 bbhInitial 5 = [7, 14, 28, 56, 112] ∧
    14 = 2 * 7 ∧
    28 = 2 * 14 ∧
    56 = 2 * 28 ∧
    112 = 2 * 56 :=
  ⟨doubleCycle_5_bbh_flux, by decide, by decide, by decide, by decide⟩

/-! ## Contents

  * `perStepEventCount`: the number of events at each of the first `n`
    fire-all steps.
  * Seven lists of per-step counts on `bbhInitial` and `seedEdge12`.
  * `bbh_flux_equals_7x_baseline`: for three (system, depth) pairs, the
    list on `bbhInitial` is the list on `seedEdge12` multiplied by 7.
  * `exponential_merger_growth_x3`, `exponential_merger_growth_x2`: one
    computed list each, with the integer identities that each entry is
    3 (or 2) times the previous one.

The module states nothing about steps beyond those computed, other
systems or other seeds.
-/

end DiscreteBondiFlux
end InfraFormalization
