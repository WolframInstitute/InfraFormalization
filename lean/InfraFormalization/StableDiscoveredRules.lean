/-
Knill values of eleven rules on a two-edge path seed.

For eleven rules of `DiscoveredRules.lean`, this module computes the
scaled Knill value of `causalDAGOfEvolution sys seedPath123 4`, built from
`singleWayStep`, and proves that it is twice the value on `seedEdge12`.
The path values, checked by `native_decide`, are 0 (`edgeReversal`), −12
(`doubleCycle_5`, `_9`, `_13`, `_18`), 252 (`bidirectedEdge`), 36
(`forkRule_2`, `_7`, `_11`, `_16`) and 24 (`identityKeep`). No statement
covers other seeds or depths.
-/

import InfraFormalization.DiscoveredRules

namespace InfraFormalization
namespace StableDiscoveredRules

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules

/-- The two-edge path seed `0 → 1 → 2`. -/
def seedPath123 : ExecHG ℕ :=
  [⟨[0, 1], List.cons_ne_nil _ _⟩,
   ⟨[1, 2], List.cons_ne_nil _ _⟩]

/-! ## Values on the path seed at depth 4, checked by `native_decide` -/

theorem edgeReversal_path_knill :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedPath123 4) = 0 := by
  native_decide

theorem doubleCycle_5_path_knill :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) = -12 := by
  native_decide

theorem doubleCycle_9_path_knill :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedPath123 4) = -12 := by
  native_decide

theorem doubleCycle_13_path_knill :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedPath123 4) = -12 := by
  native_decide

theorem doubleCycle_18_path_knill :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedPath123 4) = -12 := by
  native_decide

theorem bidirectedEdge_path_knill :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedPath123 4) = 252 := by
  native_decide

theorem fork_2_path_knill :
    knillEulerScaled (causalDAGOfEvolution forkSys_2 seedPath123 4) = 36 := by
  native_decide

theorem fork_7_path_knill :
    knillEulerScaled (causalDAGOfEvolution forkSys_7 seedPath123 4) = 36 := by
  native_decide

theorem fork_11_path_knill :
    knillEulerScaled (causalDAGOfEvolution forkSys_11 seedPath123 4) = 36 := by
  native_decide

theorem fork_16_path_knill :
    knillEulerScaled (causalDAGOfEvolution forkSys_16 seedPath123 4) = 36 := by
  native_decide

theorem identityKeep_path_knill :
    knillEulerScaled (causalDAGOfEvolution identityKeepSys seedPath123 4) = 24 := by
  native_decide

/-! ## Path value equals twice the single-edge value

Each theorem combines the path value above with the single-edge value from
`DiscoveredRules`. -/

theorem edgeReversal_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) := by
  rw [edgeReversal_path_knill, edgeReversal_knill_zero]; rfl

theorem doubleCycle_5_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) := by
  rw [doubleCycle_5_path_knill, doubleCycle_5_knill_neg6]; rfl

theorem doubleCycle_9_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedEdge12 4) := by
  rw [doubleCycle_9_path_knill, doubleCycle_9_knill_neg6]; rfl

theorem doubleCycle_13_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedEdge12 4) := by
  rw [doubleCycle_13_path_knill, doubleCycle_13_knill_neg6]; rfl

theorem doubleCycle_18_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedEdge12 4) := by
  rw [doubleCycle_18_path_knill, doubleCycle_18_knill_neg6]; rfl

theorem bidirectedEdge_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) := by
  rw [bidirectedEdge_path_knill, bidirectedEdge_knill_126]; rfl

theorem fork_2_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution forkSys_2 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution forkSys_2 seedEdge12 4) := by
  rw [fork_2_path_knill, fork_2_knill_18]; rfl

theorem fork_7_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution forkSys_7 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution forkSys_7 seedEdge12 4) := by
  rw [fork_7_path_knill, fork_7_knill_18]; rfl

theorem fork_11_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution forkSys_11 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution forkSys_11 seedEdge12 4) := by
  rw [fork_11_path_knill, fork_11_knill_18]; rfl

theorem fork_16_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution forkSys_16 seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution forkSys_16 seedEdge12 4) := by
  rw [fork_16_path_knill, fork_16_knill_18]; rfl

theorem identityKeep_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution identityKeepSys seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution identityKeepSys seedEdge12 4) := by
  rw [identityKeep_path_knill, identityKeep_knill_12]; rfl

/-! ## Conjunction -/

/-- For each of the eleven rules at depth 4, the value on `seedPath123` is
twice the value on `seedEdge12`. -/
theorem stable_per_seed_edge_invariants :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution forkSys_2 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution forkSys_2 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution forkSys_7 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution forkSys_7 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution forkSys_11 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution forkSys_11 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution forkSys_16 seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution forkSys_16 seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution identityKeepSys seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution identityKeepSys seedEdge12 4) :=
  ⟨edgeReversal_per_edge_invariant,
   doubleCycle_5_per_edge_invariant,
   doubleCycle_9_per_edge_invariant,
   doubleCycle_13_per_edge_invariant,
   doubleCycle_18_per_edge_invariant,
   bidirectedEdge_per_edge_invariant,
   fork_2_per_edge_invariant,
   fork_7_per_edge_invariant,
   fork_11_per_edge_invariant,
   fork_16_per_edge_invariant,
   identityKeep_per_edge_invariant⟩

end StableDiscoveredRules
end InfraFormalization
