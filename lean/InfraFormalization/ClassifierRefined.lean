/-
Scaled Knill values for five rules with repeated right-hand-side edges, and a predictor
function `predictedKnillRefined`.

The rules rewrite the edge `{0, 1}`. For each rule the module computes
`knillEulerScaled (causalDAGOfEvolution sys seedEdge12 4)` with `singleWayStep`:

  * RHS `[{0,1}, {0,1}, {0,2}]` gives 18.
  * RHS `[{0,1}, {0,1}, {0,2}, {0,2}]` gives 18.
  * RHS `[{0,1}, {0,2}, {1,2}, {0,2}]` gives 24.
  * RHS `[{1,0}, {1,0}]` and `[{1,0}, {1,0}, {1,0}]` give -18.

`predictedKnillRefined` is a function of the right-hand side that uses the number of
distinct edges. The module evaluates it on seven right-hand sides. All values are checked
by `native_decide`.
-/

import InfraFormalization.ClassifierMaxRHS4

namespace InfraFormalization
namespace ClassifierRefined

open MultiwayExec
open RuleSignatureExecMetrics
open RuleSignatureExecSearch
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open RuleClassifier
open ClassifierMaxRHS4

/-! ## Rules with forward edges -/

/-- The rule with RHS `[{0,1}, {0,1}, {0,2}]`, which has 2 distinct edges. -/
def treeDistinct2A : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 1,
     mkEdgeFin (p := 3) 0 2]
def treeDistinct2A_sys : ExecSystem := ⟨[treeDistinct2A]⟩

theorem treeDistinct2A_knill_18 :
    knillEulerScaled (causalDAGOfEvolution treeDistinct2A_sys seedEdge12 4) = 18 := by
  native_decide

/-- The rule with RHS `[{0,1}, {0,1}, {0,2}, {0,2}]`, which has 2 distinct edges. -/
def treeDistinct2B : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 1,
     mkEdgeFin (p := 3) 0 2, mkEdgeFin (p := 3) 0 2]
def treeDistinct2B_sys : ExecSystem := ⟨[treeDistinct2B]⟩

theorem treeDistinct2B_knill_18 :
    knillEulerScaled (causalDAGOfEvolution treeDistinct2B_sys seedEdge12 4) = 18 := by
  native_decide

/-- The rule with RHS `[{0,1}, {0,2}, {1,2}, {0,2}]`, which has 3 distinct edges. -/
def treeDistinct3C : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 2,
     mkEdgeFin (p := 3) 1 2, mkEdgeFin (p := 3) 0 2]
def treeDistinct3C_sys : ExecSystem := ⟨[treeDistinct3C]⟩

theorem treeDistinct3C_knill_24 :
    knillEulerScaled (causalDAGOfEvolution treeDistinct3C_sys seedEdge12 4) = 24 := by
  native_decide

/-- At depth 4 on `seedEdge12`, `treeDistinct2A` and `treeDistinct2B` both give 18 and
`treeDistinct3C` gives 24. -/
theorem tree_distinct_count_law :
    knillEulerScaled (causalDAGOfEvolution treeDistinct2A_sys seedEdge12 4) =
      knillEulerScaled (causalDAGOfEvolution treeDistinct2B_sys seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution treeDistinct2A_sys seedEdge12 4) = 18 ∧
    knillEulerScaled (causalDAGOfEvolution treeDistinct3C_sys seedEdge12 4) = 24 :=
  ⟨by rw [treeDistinct2A_knill_18, treeDistinct2B_knill_18],
   treeDistinct2A_knill_18, treeDistinct3C_knill_24⟩

/-! ## Rules whose right-hand side repeats the reversed edge -/

/-- The rule with RHS `[{1,0}, {1,0}]`. -/
def mergerSaturate2 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 1 0]
def mergerSaturate2_sys : ExecSystem := ⟨[mergerSaturate2]⟩

theorem mergerSaturate2_knill_neg18 :
    knillEulerScaled (causalDAGOfEvolution mergerSaturate2_sys seedEdge12 4) = -18 := by
  native_decide

/-- The rule with RHS `[{1,0}, {1,0}, {1,0}]`. -/
def mergerSaturate3 : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 1 0,
     mkEdgeFin (p := 3) 1 0]
def mergerSaturate3_sys : ExecSystem := ⟨[mergerSaturate3]⟩

theorem mergerSaturate3_knill_neg18 :
    knillEulerScaled (causalDAGOfEvolution mergerSaturate3_sys seedEdge12 4) = -18 := by
  native_decide

/-- At depth 4 on `seedEdge12`, the rules with RHS `{1,0}` repeated 2, 3 and 4 times
(`mergerSaturate2`, `mergerSaturate3`, `quadrupleMergerRule`) each give -18. -/
theorem merger_pure_duplicate_saturation :
    knillEulerScaled (causalDAGOfEvolution mergerSaturate2_sys seedEdge12 4) = -18 ∧
    knillEulerScaled (causalDAGOfEvolution mergerSaturate3_sys seedEdge12 4) = -18 ∧
    knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) = -18 :=
  ⟨mergerSaturate2_knill_neg18,
   mergerSaturate3_knill_neg18,
   quadrupleMerger_knill_neg18⟩

/-! ## Predictor -/

/-- The number of distinct vertex lists among the edges of `rhs`. -/
def distinctEdgeCount (rhs : ExecHG (Fin 3)) : Nat :=
  let pairs := rhs.map (·.verts)
  let dedup := pairs.foldr (fun v acc => if v ∈ acc then acc else v :: acc) []
  dedup.length

/-- A function of the right-hand side, piecewise in whether it contains forward edges,
reversed edges, its length `n` and its distinct-edge count `d`. -/
def predictedKnillRefined (rhs : ExecHG (Fin 3)) : Int :=
  let hasForward := rhs.any isForwardEdge
  let hasReverse := rhs.any isReverseEdge
  let n := rhs.length
  let d := distinctEdgeCount rhs
  if hasForward then
    if hasReverse then 126 + 30 * (n - 2 : Int)
    else 6 * ((d : Int) + 1)                -- forward edges only: uses d
  else if hasReverse then
    if d = 1 ∧ n ≥ 2 then -18                -- one reversed edge, repeated
    else if d = 1 then 0                     -- one reversed edge, once
    else -6 * (n : Int) + 6                  -- several distinct reversed edges: uses n
  else 6

/-- Values of `predictedKnillRefined` on seven right-hand sides. They equal the depth-4
values proved for the same rules in this module and in `ClassifierMaxRHS4`. Checked by
`native_decide`. -/
theorem predictedKnillRefined_matches :
    predictedKnillRefined treeDistinct2A.rhs = 18 ∧
    predictedKnillRefined treeDistinct2B.rhs = 18 ∧
    predictedKnillRefined treeDistinct3C.rhs = 24 ∧
    predictedKnillRefined mergerSaturate2.rhs = -18 ∧
    predictedKnillRefined mergerSaturate3.rhs = -18 ∧
    predictedKnillRefined quadrupleMergerRule.rhs = -18 ∧
    predictedKnillRefined fiveTreeRule.rhs = 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end ClassifierRefined
end InfraFormalization
