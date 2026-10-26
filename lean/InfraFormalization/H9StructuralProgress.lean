/-
Distinct edge counts under `fireAllEvolve` at depths 0 to 4.

`distinctEdgeCount H` is the number of distinct vertex lists among the edges of `H`, evaluated on
`fireAllEvolve sys seedEdge12 d`.
`fireAllEvolve` iterates `fireAllStep`, which applies every match of every rule, including
overlapping matches, and is not a Wolfram model update.
The module proves, by `native_decide`, that the count is 81 at depth 4 for
`edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`, and that it is `3^n` for
`edgeReversal_tripleMerger_Sys` at `n = 0, …, 4`.
It defines the proposition `distinct_tripling_conjecture`, that the count is `3^n` for every `n`
for both systems, which no theorem in the library proves.
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

/-- The distinct edge count of `fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4` is 81.
Checked by `native_decide`. -/
theorem distinct_eR_tripleMerger_d4 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 81 := by
  native_decide

/-- The distinct edge count of `fireAllEvolve fork_doubleCycle_Sys seedEdge12 4` is 81. Checked by
`native_decide`. -/
theorem distinct_fork_dCyc_d4 :
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 4) = 81 := by
  native_decide

/-- The distinct edge count at depth 4 is `3^4` for `edgeReversal_tripleMerger_Sys` and for
`fork_doubleCycle_Sys`. The statement covers depth 4 only. Checked by `native_decide`. -/
theorem distinct_identity_5_depths :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 3^4 ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 4) = 3^4 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## The tripling proposition -/

/-- For `edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`, and every `n`,
`distinctEdgeCount (fireAllEvolve sys seedEdge12 n) = 3^n`. No theorem in the library proves it. -/
def distinct_tripling_conjecture : Prop :=
  ∀ (sys : ExecSystem),
    sys = edgeReversal_tripleMerger_Sys ∨ sys = fork_doubleCycle_Sys →
    ∀ n : Nat,
      distinctEdgeCount (fireAllEvolve sys seedEdge12 n) = 3^n

/-- The instances `n = 0, …, 4` of `distinct_tripling_conjecture` for
`edgeReversal_tripleMerger_Sys`. Checked by `native_decide`. -/
theorem distinct_tripling_holds_through_depth_4 :
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 0) = 3^0) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 1) = 3^1) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 2) = 3^2) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 3) = 3^3) ∧
    (distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 3^4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide


end H9StructuralProgress
end InfraFormalization
