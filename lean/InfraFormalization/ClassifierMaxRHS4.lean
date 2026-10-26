/-
Classifier `predictedKnill` on two rules with four right-hand edges.

This module defines `fiveTreeRule`, whose right-hand side is four copies
of `{0,1}`, and `quadrupleMergerRule`, whose right-hand side is four
copies of `{1,0}`. For the depth-4 single-way causal graph
`causalDAGOfEvolution sys seedEdge12 4`, the scaled Knill value is 12
for `fiveTreeRule`, where `predictedKnill` gives 30, and -18 for
`quadrupleMergerRule`, where `predictedKnill` also gives -18. Values
are checked by `native_decide`.
-/

import InfraFormalization.RuleClassifier

namespace InfraFormalization
namespace ClassifierMaxRHS4

open MultiwayExec
open RuleSignatureExecMetrics
open RuleSignatureExecSearch
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open RuleClassifier

/-! ## `fiveTreeRule` -/

/-- The rule whose right-hand side is four copies of `{0,1}`. -/
def fiveTreeRule : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 1,
     mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 1]

def fiveTreeSys : ExecSystem := ⟨[fiveTreeRule]⟩

/-- For `fiveTreeSys`, the scaled Knill value of the depth-4 single-way
causal graph from `seedEdge12` is 12. -/
theorem fiveTree_actual_knill_12 :
    knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) = 12 := by
  native_decide

/-- For `fiveTreeRule`, `predictedKnill` gives 30, the depth-4
single-way causal Knill value is 12, and the two differ. -/
theorem fiveTree_prediction_fails :
    predictedKnill (ruleClassFromRhs fiveTreeRule.rhs) = 30 ∧
    knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) = 12 ∧
    predictedKnill (ruleClassFromRhs fiveTreeRule.rhs) ≠
      knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) := by
  refine ⟨?_, fiveTree_actual_knill_12, ?_⟩
  · native_decide
  · native_decide

/-! ## `quadrupleMergerRule` -/

/-- The rule whose right-hand side is four copies of `{1,0}`. -/
def quadrupleMergerRule : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 1 0,
     mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 1 0]

def quadrupleMergerSys : ExecSystem := ⟨[quadrupleMergerRule]⟩

/-- For `quadrupleMergerSys`, the scaled Knill value of the depth-4
single-way causal graph from `seedEdge12` is -18. -/
theorem quadrupleMerger_knill_neg18 :
    knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) = -18 := by
  native_decide

/-- For `quadrupleMergerRule`, `predictedKnill` equals the depth-4
single-way causal Knill value. -/
theorem quadrupleMerger_predicted_correctly :
    predictedKnill (ruleClassFromRhs quadrupleMergerRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) := by
  native_decide

/-! ## Both rules -/

/-- `predictedKnill` equals the depth-4 single-way causal Knill value
for `quadrupleMergerRule` and differs from it for `fiveTreeRule`. -/
theorem classifier_domain_audit :
    -- quadrupleMergerRule:
    predictedKnill (ruleClassFromRhs quadrupleMergerRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) ∧
    -- fiveTreeRule:
    predictedKnill (ruleClassFromRhs fiveTreeRule.rhs) ≠
      knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) := by
  refine ⟨quadrupleMerger_predicted_correctly, ?_⟩
  rw [fiveTree_actual_knill_12]
  native_decide

end ClassifierMaxRHS4
end InfraFormalization
