/-
A classification of rules by the right-hand side, with predicted Knill
values.

This module defines `ruleClassFromRhs`, which assigns a rule on `Fin 3`
patterns to one of four classes according to whether its right-hand side
contains the edge `[0, 1]`, the edge `[1, 0]`, both or neither, and
`predictedKnill`, an integer assigned to each class. For eight rules it
checks by `native_decide` that `predictedKnill` equals the scaled Knill
value of `causalDAGOfEvolution sys seedEdge12 4`, which is built from
`singleWayStep`. No statement covers rules outside these eight.
-/

import InfraFormalization.DiscoveredRulesExpanded

namespace InfraFormalization
namespace RuleClassifier

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded

/-! ## Classes and classifier -/

/-- Four rule classes, three of them carrying a natural number. -/
inductive RuleClass : Type
  | Tree (nEdges : Nat) : RuleClass
  | Merger (nEdges : Nat) : RuleClass
  | Bidirected (nExtras : Nat) : RuleClass
  | Other : RuleClass
deriving DecidableEq

/-- `e` has vertex list `[0, 1]`. -/
def isForwardEdge (e : Hyperedge (Fin 3)) : Bool :=
  e.verts == [0, 1]

/-- `e` has vertex list `[1, 0]`. -/
def isReverseEdge (e : Hyperedge (Fin 3)) : Bool :=
  e.verts == [1, 0]

/-- With `n` the number of right-hand-side edges: `Bidirected (n − 2)` if
both `[0, 1]` and `[1, 0]` occur, `Tree n` if only `[0, 1]` occurs,
`Merger n` if only `[1, 0]` occurs, and `Other` otherwise. -/
def ruleClassFromRhs (rhs : ExecHG (Fin 3)) : RuleClass :=
  let hasForward := rhs.any isForwardEdge
  let hasReverse := rhs.any isReverseEdge
  let n := rhs.length
  if hasForward then
    if hasReverse then RuleClass.Bidirected (n - 2)
    else RuleClass.Tree n
  else if hasReverse then RuleClass.Merger n
  else RuleClass.Other

/-- Equal to `ruleClassFromRhs`. -/
def classifyDiscovered (rhs : ExecHG (Fin 3)) : RuleClass :=
  ruleClassFromRhs rhs

/-! ## Predicted values -/

/-- `Tree n ↦ 6(n + 1)`, `Merger n ↦ −6n + 6`, `Bidirected n ↦ 126 + 30n`,
`Other ↦ 6`. -/
def predictedKnill : RuleClass → Int
  | RuleClass.Tree n => 6 * ((n : Int) + 1)
  | RuleClass.Merger n => -6 * (n : Int) + 6
  | RuleClass.Bidirected n => 126 + 30 * (n : Int)
  | RuleClass.Other => 6

/-! ## Comparison with computed values, checked by `native_decide` -/

theorem edgeReversal_predicted :
    predictedKnill (ruleClassFromRhs edgeReversalRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) := by
  native_decide

theorem doubleCycle_5_predicted :
    predictedKnill (ruleClassFromRhs doubleCycleRule_5.rhs) =
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) := by
  native_decide

theorem tripleMerger_predicted :
    predictedKnill (ruleClassFromRhs tripleMergerRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution tripleMergerSys seedEdge12 4) := by
  native_decide

theorem identityKeep_predicted :
    predictedKnill (ruleClassFromRhs identityKeepRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution identityKeepSys seedEdge12 4) := by
  native_decide

theorem forkRule_2_predicted :
    predictedKnill (ruleClassFromRhs forkRule_2.rhs) =
    knillEulerScaled (causalDAGOfEvolution forkSys_2 seedEdge12 4) := by
  native_decide

theorem fourTree_predicted :
    predictedKnill (ruleClassFromRhs fourTreeRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution fourTreeSys seedEdge12 4) := by
  native_decide

theorem bidirectedEdge_predicted :
    predictedKnill (ruleClassFromRhs bidirectedEdgeRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) := by
  native_decide

theorem superHyper_predicted :
    predictedKnill (ruleClassFromRhs superHyperRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution superHyperSys seedEdge12 4) := by
  native_decide

/-! ## Conjunction -/

/-- The conjunction of the eight equalities above: for each of the eight
rules, `predictedKnill` of its class equals the scaled Knill value of
`causalDAGOfEvolution sys seedEdge12 4`. -/
theorem classifier_predicts_correctly :
    predictedKnill (ruleClassFromRhs edgeReversalRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) ∧
    predictedKnill (ruleClassFromRhs doubleCycleRule_5.rhs) =
      knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) ∧
    predictedKnill (ruleClassFromRhs tripleMergerRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution tripleMergerSys seedEdge12 4) ∧
    predictedKnill (ruleClassFromRhs identityKeepRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution identityKeepSys seedEdge12 4) ∧
    predictedKnill (ruleClassFromRhs forkRule_2.rhs) =
      knillEulerScaled (causalDAGOfEvolution forkSys_2 seedEdge12 4) ∧
    predictedKnill (ruleClassFromRhs fourTreeRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution fourTreeSys seedEdge12 4) ∧
    predictedKnill (ruleClassFromRhs bidirectedEdgeRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) ∧
    predictedKnill (ruleClassFromRhs superHyperRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution superHyperSys seedEdge12 4) :=
  ⟨edgeReversal_predicted, doubleCycle_5_predicted,
   tripleMerger_predicted, identityKeep_predicted,
   forkRule_2_predicted, fourTree_predicted,
   bidirectedEdge_predicted, superHyper_predicted⟩

end RuleClassifier
end InfraFormalization
