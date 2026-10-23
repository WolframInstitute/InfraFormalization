/-
Distinct edge counts at depth 4 and the open tripling statement.

`distinctEdgeCount H` is the number of distinct vertex lists among the
edges of `H`. The states are `fireAllEvolve sys seedEdge12 d`. The
evolution is `fireAllStep`, which applies every match of every rule
found in the state, including matches that share edges. It is not a
Wolfram model update when matches overlap.

PROVED-WITH-NATIVE-DECIDE:

  * The count is 81 at depth 4 for `edgeReversal_tripleMerger_Sys` and
    for `fork_doubleCycle_Sys`.
  * The count is `3^n` for `edgeReversal_tripleMerger_Sys` at
    `n = 0, ..., 4`.

OPEN:

  * `distinct_tripling_conjecture`: the count is `3^n` for every `n`,
    for both rule pairs.
  * `B(d) = 3^(d+1) - 3` for every `d ≥ 2`, where B is
    `discreteBranchialDensity`. No Lean statement derives it from the
    tripling statement. The recurrence `B(d+1) = 3·B(d) + 6` is not
    stated in this module.

The module contains an unproved outline (INV, INV1, INV2) for the
tripling statement.
-/

import InfraFormalization.DistinctEdgeIdentity

namespace InfraFormalization
namespace H9StructuralProgress

open MultiwayExec
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DistinctEdgeIdentity

/-! ## Depth 4 -/

theorem distinct_eR_tripleMerger_d4 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 81 := by
  native_decide

theorem distinct_fork_dCyc_d4 :
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 4) = 81 := by
  native_decide

/-- `distinct_identity_5_depths`: the distinct edge count at depth 4 is
`3^4` for `edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`.
The name says five depths; the statement is the two depth-4 instances.
Depths 0 to 3 are in `DistinctEdgeIdentity`. -/
theorem distinct_identity_5_depths :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 3^4 ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 4) = 3^4 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Unproved outline for the tripling statement

None of the following is stated in Lean.

INV(H) would assert:
  * a finite set `V₀ ⊆ ℕ` of original vertices (`{1, 2}` initially);
  * generations `F₀, F₁, ..., F_k` of fresh vertices, pairwise
    disjoint and disjoint from `V₀`;
  * a decomposition of the distinct edges of H into a recursive
    triadic structure (one reversed base edge and two edges through a
    fresh vertex) per sub-trajectory.

INV1: `INV(seedEdge12)` holds and `INV(H) → INV(fireAllStep sys H)`
for both rule pairs.

INV2: if H satisfies INV with k generations, then
`distinctEdgeCount H = 3^k`.

Lemma chain:
  1. `allMatches` gives one match per rule per distinct edge of H.
  2. Each match consumes one distinct edge of H.
  3. Each match produces |RHS| edges.
  4. Fresh vertices are pairwise distinct across matches in one step.
  5. The new distinct edges form the triadic extension. -/

/-- `distinct_tripling_conjecture` (OPEN): for
`edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`, and every
`n`, `distinctEdgeCount (fireAllEvolve sys seedEdge12 n) = 3^n`. No
theorem in the library proves it. -/
def distinct_tripling_conjecture : Prop :=
  ∀ (sys : ExecSystem),
    sys = edgeReversal_tripleMerger_Sys ∨ sys = fork_doubleCycle_Sys →
    ∀ n : Nat,
      distinctEdgeCount (fireAllEvolve sys seedEdge12 n) = 3^n

/-- `distinct_tripling_holds_through_depth_4`: the instances `n = 0`
to `n = 4` of `distinct_tripling_conjecture` for
`edgeReversal_tripleMerger_Sys` only. -/
theorem distinct_tripling_holds_through_depth_4 :
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 0) = 3^0) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 1) = 3^1) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 2) = 3^2) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 3) = 3^3) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 3^4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

PROVED-WITH-NATIVE-DECIDE:

  * `distinct_identity_5_depths`: count `3^4` at depth 4 for both
    rule pairs.
  * `distinct_tripling_holds_through_depth_4`: count `3^n` for
    `edgeReversal_tripleMerger_Sys` at depths 0 to 4.
  * `B_closed_form_persistent_class` (in `BClosedForm`) and
    `B_closed_form_d6` (in `BClosedFormExtended`) give
    `B(d) = 3^(d+1) - 3` at depths 2 to 6.

OPEN:

  * `distinct_tripling_conjecture`.
  * `B(d) = 3^(d+1) - 3` for every `d ≥ 2`. No Lean statement derives
    it from `distinct_tripling_conjecture`.
-/

end H9StructuralProgress
end InfraFormalization
