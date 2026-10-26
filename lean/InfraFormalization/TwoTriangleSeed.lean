/-
Seven-edge seed `twoTriangleSeed` and two single-way Knill values on it.

This module defines `twoTriangleSeed`, the hypergraph with the triangles on
`{0,1,2}` and `{3,4,5}` and the edge `{2,3}`: 6 vertices and 7 edges. It
proves that the scaled Knill value of the depth-4 single-way causal
graph `causalDAGOfEvolution sys twoTriangleSeed 4` is 0 for
`edgeReversalSys` and -42 for `doubleCycleSys_5`, checked by
`native_decide`. Both values equal 7 times the value on `seedEdge12`.
The module defines no black hole or spacetime quantity.
-/

import InfraFormalization.DiscoveredRules

namespace InfraFormalization
namespace TwoTriangleSeed

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules

/-! ## The seed `twoTriangleSeed` -/

/-- The hypergraph with the triangles on `{0,1,2}` and `{3,4,5}` and
the edge `{2,3}`: 6 vertices and 7 edges. -/
def twoTriangleSeed : ExecHG ℕ :=
  [-- Triangle on {0, 1, 2}
   ⟨[0,1], List.cons_ne_nil _ _⟩,
   ⟨[1,2], List.cons_ne_nil _ _⟩,
   ⟨[0,2], List.cons_ne_nil _ _⟩,
   -- Triangle on {3, 4, 5}
   ⟨[3,4], List.cons_ne_nil _ _⟩,
   ⟨[4,5], List.cons_ne_nil _ _⟩,
   ⟨[3,5], List.cons_ne_nil _ _⟩,
   -- Edge {2, 3}
   ⟨[2,3], List.cons_ne_nil _ _⟩]

/-- `twoTriangleSeed` has 7 edges. -/
theorem twoTriangleSeed_edge_count : twoTriangleSeed.length = 7 := by decide

/-! ## Single-way causal Knill values at depth 4 -/

/-- For `edgeReversalSys` on `twoTriangleSeed` at depth 4 the value is 0. -/
theorem edgeReversal_twoTriangle_knill_zero :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys twoTriangleSeed 4) = 0 := by
  native_decide

/-- For `doubleCycleSys_5` on `twoTriangleSeed` at depth 4 the value is -42. -/
theorem doubleCycle_5_twoTriangle_knill_neg42 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 twoTriangleSeed 4) = -42 := by
  native_decide

/-! ## Factor 7 relative to `seedEdge12` -/

/-- For `edgeReversalSys` and `doubleCycleSys_5` at depth 4, the
single-way causal Knill value on `twoTriangleSeed` is 7 times the value on
`seedEdge12`. -/
theorem twoTriangle_knill_seven_times_edge :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys twoTriangleSeed 4) =
      7 * knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 twoTriangleSeed 4) =
      7 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) := by
  refine ⟨?_, ?_⟩
  · rw [edgeReversal_twoTriangle_knill_zero, edgeReversal_knill_zero]; rfl
  · rw [doubleCycle_5_twoTriangle_knill_neg42, doubleCycle_5_knill_neg6]; rfl

end TwoTriangleSeed
end InfraFormalization
