/-
Scaled Knill values of causal graphs on seeds with 1, 2, 3 and 7 edges.

Most theorems use `causalDAGOfEvolution`, built from
`tracedSingleWayEvolve`. `singleWayStep` applies a maximal set of
edge-disjoint matches, chosen greedily in enumeration order. The theorems
for `edgeReversal + identityKeep` use `causalDAGOfFireAll`, built from
`tracedFireAllEvolve`. `fireAllStep` applies every match of every rule
found in the state, including matches that share edges. It is not a
Wolfram model update when matches overlap.

For `doubleCycle_5` at depth 4 (single-way trace) the following values are
checked by `native_decide`:

  | Seed                        | edges | value |
  |-----------------------------|-------|-------|
  | `seedEdge12`                |   1   |  -6   |
  | `seedPath123`               |   2   | -12   |
  | `seedTwoDisjoint`           |   2   | -12   |
  | `seedTriangle`              |   3   | -18   |
  | `twoTriangleSeed`                |   7   | -42   |

In each row the value is the number of edges times -6. The module proves
the same proportionality for `edgeReversal` at depth 5 (four seeds),
`bidirectedEdge` at depth 4 (three seeds), and the fire-all trace of
`edgeReversal + identityKeep` at depth 3 (three seeds). Each statement
is a finite conjunction. The proportionality for every rule, seed and
depth is not stated.
-/

import InfraFormalization.TwoTriangleSeed
import InfraFormalization.MultiRuleDiscovered

namespace InfraFormalization
namespace UniversalAdditivity

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open TwoTriangleSeed

/-! ## Seeds -/

/-- Two-edge path: `{1,2}, {2,3}`. -/
def seedPath123 : ExecHG ℕ :=
  [⟨[1, 2], List.cons_ne_nil _ _⟩, ⟨[2, 3], List.cons_ne_nil _ _⟩]

/-- Triangle: `{1,2}, {2,3}, {1,3}`. -/
def seedTriangle : ExecHG ℕ :=
  [⟨[1, 2], List.cons_ne_nil _ _⟩,
   ⟨[2, 3], List.cons_ne_nil _ _⟩,
   ⟨[1, 3], List.cons_ne_nil _ _⟩]

/-- Two disconnected edges: `{1,2}, {3,4}`. -/
def seedTwoDisjoint : ExecHG ℕ :=
  [⟨[1, 2], List.cons_ne_nil _ _⟩, ⟨[3, 4], List.cons_ne_nil _ _⟩]

/-! ## Values of `doubleCycle_5` at depth 4 -/

theorem doubleCycle_5_path_knill_neg12 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) = -12 := by
  native_decide

theorem doubleCycle_5_triangle_knill_neg18 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedTriangle 4) = -18 := by
  native_decide

theorem doubleCycle_5_disjoint_knill_neg12 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedTwoDisjoint 4) = -12 := by
  native_decide

/-! ## `doubleCycle_5` at depth 4 on five seeds -/

/-- Single-way trace of `doubleCycleSys_5` at depth 4. The statement is
five equalities: the value on a seed with n edges is `n * (-6)` for the
seeds `seedEdge12` (1), `seedPath123` (2), `seedTwoDisjoint` (2),
`seedTriangle` (3) and `twoTriangleSeed` (7). -/
theorem per_edge_additivity_instances :
    -- Single edge (1 edge):
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) = -6 ∧
    -- Path (2 edges):
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) = 2 * (-6) ∧
    -- Disjoint (2 edges):
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedTwoDisjoint 4) = 2 * (-6) ∧
    -- Triangle (3 edges):
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedTriangle 4) = 3 * (-6) ∧
    -- twoTriangleSeed (7 edges):
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 twoTriangleSeed 4) = 7 * (-6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact doubleCycle_5_knill_neg6
  · rw [doubleCycle_5_path_knill_neg12]; rfl
  · rw [doubleCycle_5_disjoint_knill_neg12]; rfl
  · rw [doubleCycle_5_triangle_knill_neg18]; rfl
  · rw [doubleCycle_5_twoTriangle_knill_neg42]; rfl

/-! ## `edgeReversal` at depth 5 -/

theorem edgeReversal_path_depth5 :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedPath123 5) = -12 := by
  native_decide

theorem edgeReversal_triangle_depth5 :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedTriangle 5) = -18 := by
  native_decide

theorem edgeReversal_disjoint_depth5 :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedTwoDisjoint 5) = -12 := by
  native_decide

/-- Single-way trace of `edgeReversalSys` at depth 5. The statement is
four equalities: -6 on `seedEdge12`, `2 * (-6)` on `seedPath123` and on
`seedTwoDisjoint`, and `3 * (-6)` on `seedTriangle`.
`BBHDeepEvolution` gives -42 = 7 × (-6) on `twoTriangleSeed` at depth 5. -/
theorem additivity_edgeReversal_depth5 :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 5) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedPath123 5) = 2 * (-6) ∧
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedTwoDisjoint 5) = 2 * (-6) ∧
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedTriangle 5) = 3 * (-6) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · native_decide
  · rw [edgeReversal_path_depth5]; rfl
  · rw [edgeReversal_disjoint_depth5]; rfl
  · rw [edgeReversal_triangle_depth5]; rfl

/-! ## `bidirectedEdge` at depth 4 -/

theorem bidirectedEdge_path_depth4 :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedPath123 4) = 252 := by
  native_decide

theorem bidirectedEdge_triangle_depth4 :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedTriangle 4) = 378 := by
  native_decide

/-- Single-way trace of `bidirectedEdgeSys` at depth 4. The statement is
three equalities:

  * `seedEdge12` (1 edge): 126
  * `seedPath123` (2 edges): 252 = 2 × 126
  * `seedTriangle` (3 edges): 378 = 3 × 126 -/
theorem additivity_bidirected_instances :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) = 126 ∧
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedPath123 4) = 2 * 126 ∧
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedTriangle 4) = 3 * 126 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · rw [bidirectedEdge_path_depth4]; rfl
  · rw [bidirectedEdge_triangle_depth4]; rfl

/-! ## `edgeReversal + identityKeep` (fire-all trace) -/

theorem edgeReversal_identity_path_depth3 :
    knillEulerScaled (causalDAGOfFireAll
      MultiRuleDiscovered.edgeReversal_identity_Sys seedPath123 3) = -48 := by
  native_decide

theorem edgeReversal_identity_triangle_depth3 :
    knillEulerScaled (causalDAGOfFireAll
      MultiRuleDiscovered.edgeReversal_identity_Sys seedTriangle 3) = -72 := by
  native_decide

/-- Fire-all trace of `edgeReversal + identityKeep` at depth 3. The
statement is three equalities:

  * `seedEdge12` (1 edge): -24
  * `seedPath123` (2 edges): -48 = 2 × -24
  * `seedTriangle` (3 edges): -72 = 3 × -24 -/
theorem additivity_multi_rule_instances :
    knillEulerScaled (causalDAGOfFireAll
      MultiRuleDiscovered.edgeReversal_identity_Sys seedEdge12 3) = -24 ∧
    knillEulerScaled (causalDAGOfFireAll
      MultiRuleDiscovered.edgeReversal_identity_Sys seedPath123 3) = 2 * (-24) ∧
    knillEulerScaled (causalDAGOfFireAll
      MultiRuleDiscovered.edgeReversal_identity_Sys seedTriangle 3) = 3 * (-24) := by
  refine ⟨?_, ?_, ?_⟩
  · exact MultiRuleDiscovered.edgeReversal_identity_knill_neg24
  · rw [edgeReversal_identity_path_depth3]; rfl
  · rw [edgeReversal_identity_triangle_depth3]; rfl

/-- For `doubleCycle_5` at depth 4 (single-way trace), the values on
`seedPath123` and `seedTwoDisjoint` are equal (both -12). -/
theorem topology_independence_2_edges :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) =
      knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedTwoDisjoint 4) := by
  rw [doubleCycle_5_path_knill_neg12, doubleCycle_5_disjoint_knill_neg12]

end UniversalAdditivity
end InfraFormalization
