/-
Distinct edge counts of two rule pairs at depths 0 to 3.

`distinctEdgeCount H` is the number of distinct vertex lists among the
edges of `H`. The states are `fireAllEvolve sys seedEdge12 d`. The
evolution is `fireAllStep`, which applies every match of every rule
found in the state, including matches that share edges. It is not a
Wolfram model update when matches overlap.

Values for `edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`
(PROVED-WITH-NATIVE-DECIDE; depth 4 is in `H9StructuralProgress`):

  | d | eR + tripleMerger | fork + dCyc | 3^d |
  |---|-------------------|-------------|-----|
  | 0 |         1         |      1      |  1  |
  | 1 |         3         |      3      |  3  |
  | 2 |         9         |      9      |  9  |
  | 3 |        27         |     27      |  27 |

The count `3^d` for every `d` is OPEN for both rule pairs. This module
proves no relation between these counts and the contention Knill
values B.
-/

import InfraFormalization.MultiRuleDiscovered

namespace InfraFormalization
namespace DistinctEdgeIdentity

open MultiwayExec
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered

/-! ## The distinct-edge count function -/

/-- `distinctEdgeCount H`: the number of distinct `verts` lists among
the edges of `H`. Order matters: `[1,2]` and `[2,1]` are different
lists. -/
def distinctEdgeCount (H : ExecHG ℕ) : Nat :=
  ((H.map (·.verts)).foldr
    (fun v acc => if v ∈ acc then acc else v :: acc) []).length

/-! ## Identity at small depths -/

theorem distinct_eR_tripleMerger_d0 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 0) = 1 := by
  native_decide

theorem distinct_eR_tripleMerger_d1 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 1) = 3 := by
  native_decide

theorem distinct_eR_tripleMerger_d2 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 2) = 9 := by
  native_decide

theorem distinct_eR_tripleMerger_d3 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 3) = 27 := by
  native_decide

theorem distinct_fork_dCyc_d0 :
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 0) = 1 := by
  native_decide

theorem distinct_fork_dCyc_d1 :
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 1) = 3 := by
  native_decide

theorem distinct_fork_dCyc_d2 :
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 2) = 9 := by
  native_decide

theorem distinct_fork_dCyc_d3 :
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 3) = 27 := by
  native_decide

/-! ## Conjunction over depths 0-3 -/

/-- `distinct_edge_identity_at_low_depths`: the distinct edge count is
`3^d` for `edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`
on `seedEdge12` at depths 0, 1, 2, 3. -/
theorem distinct_edge_identity_at_low_depths :
    -- eR + tripleMerger
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 0) = 3^0 ∧
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 1) = 3^1 ∧
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 2) = 3^2 ∧
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 3) = 3^3 ∧
    -- fork + dCyc
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 0) = 3^0 ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 1) = 3^1 ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 2) = 3^2 ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 3) = 3^3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- `persistent_class_distinct_equal`: at depths 0, 1, 2, 3, the
distinct edge counts of `edgeReversal_tripleMerger_Sys` and
`fork_doubleCycle_Sys` on `seedEdge12` are equal. -/
theorem persistent_class_distinct_equal :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 0) =
      distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 0) ∧
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 1) =
      distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 1) ∧
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 2) =
      distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 2) ∧
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 3) =
      distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

  * Eight values of `distinctEdgeCount` (two rule pairs, depths 0-3).
  * `distinct_edge_identity_at_low_depths`: the count is `3^d` for
    both pairs at depths 0, 1, 2, 3.
  * `persistent_class_distinct_equal`: the two counts are equal at
    each of these depths.

Equal distinct-edge counts do not imply equal contention graphs; no
theorem here relates `distinctEdgeCount` to
`discreteBranchialDensity`. The step lemma
`distinct(fireAllStep sys H) = 3 · distinct(H)` is OPEN; the related
Prop `BridgeStepLemma` in `H9Bridge` is unproved.
-/

end DistinctEdgeIdentity
end InfraFormalization
