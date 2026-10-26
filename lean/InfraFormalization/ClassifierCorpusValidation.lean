/-
Refined classifier compared on fifteen named rules.

This module compares `predictedKnillRefined rule.rhs` with the scaled
Knill Euler characteristic of the depth-4 single-way causal graph
`causalDAGOfEvolution sys seedEdge12 4` for fifteen named rules: five
with at most two right-hand edges (edgeReversal, doubleCycle_5,
bidirectedEdge, identityKeep, forkRule_2), three with three (fourTree,
tripleMerger, superHyper), two with four (fiveTree, quadrupleMerger),
and treeDistinct2A, treeDistinct2B, treeDistinct3C, mergerSaturate2,
mergerSaturate3. The two values are equal for all fifteen, checked by
`native_decide`.
-/

import InfraFormalization.ClassifierRefined

namespace InfraFormalization
namespace ClassifierCorpusValidation

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open RuleClassifier
open ClassifierMaxRHS4
open ClassifierRefined

/-! ## Fifteen-rule comparison -/

/-- For each of fifteen named rules, `predictedKnillRefined` of the
right-hand side equals `knillEulerScaled` of the depth-4 single-way
causal graph from `seedEdge12`. Checked by `native_decide`. -/
theorem classifier_corpus_validation :
    -- At most two right-hand edges:
    predictedKnillRefined edgeReversalRule.rhs =
      knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) ∧
    predictedKnillRefined doubleCycleRule_5.rhs =
      knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) ∧
    predictedKnillRefined bidirectedEdgeRule.rhs =
      knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) ∧
    predictedKnillRefined identityKeepRule.rhs =
      knillEulerScaled (causalDAGOfEvolution identityKeepSys seedEdge12 4) ∧
    predictedKnillRefined forkRule_2.rhs =
      knillEulerScaled (causalDAGOfEvolution forkSys_2 seedEdge12 4) ∧
    -- Three right-hand edges:
    predictedKnillRefined fourTreeRule.rhs =
      knillEulerScaled (causalDAGOfEvolution fourTreeSys seedEdge12 4) ∧
    predictedKnillRefined tripleMergerRule.rhs =
      knillEulerScaled (causalDAGOfEvolution tripleMergerSys seedEdge12 4) ∧
    predictedKnillRefined superHyperRule.rhs =
      knillEulerScaled (causalDAGOfEvolution superHyperSys seedEdge12 4) ∧
    -- Four right-hand edges:
    predictedKnillRefined fiveTreeRule.rhs =
      knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) ∧
    predictedKnillRefined quadrupleMergerRule.rhs =
      knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) ∧
    -- Rules defined in ClassifierRefined:
    predictedKnillRefined treeDistinct2A.rhs =
      knillEulerScaled (causalDAGOfEvolution treeDistinct2A_sys seedEdge12 4) ∧
    predictedKnillRefined treeDistinct2B.rhs =
      knillEulerScaled (causalDAGOfEvolution treeDistinct2B_sys seedEdge12 4) ∧
    predictedKnillRefined treeDistinct3C.rhs =
      knillEulerScaled (causalDAGOfEvolution treeDistinct3C_sys seedEdge12 4) ∧
    predictedKnillRefined mergerSaturate2.rhs =
      knillEulerScaled (causalDAGOfEvolution mergerSaturate2_sys seedEdge12 4) ∧
    predictedKnillRefined mergerSaturate3.rhs =
      knillEulerScaled (causalDAGOfEvolution mergerSaturate3_sys seedEdge12 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end ClassifierCorpusValidation
end InfraFormalization
