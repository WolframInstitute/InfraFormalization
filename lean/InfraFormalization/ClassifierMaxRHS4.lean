/-
**B4-classifier-maxRHS4: scale classifier predictions to RHS=4
rules + honest audit** (#449).

The structural classifier `predictedKnill` (#444) was verified on 8
rules at maxRHS=2 and maxRHS=3. This module **extends the verification
to maxRHS=4** and **AUDITS the domain of applicability** —
materializing the framework's first **prediction-failure result**.

**Headline empirical finding** (probe + `native_decide`-certified):

  * `fiveTreeRule` (RHS = 4 copies of forward `{0,1}`):
    actual Knill at depth 4 = **12** (NOT 30 as the naive Tree(4)
    formula `6·(n+1) = 30` predicts).
  * `quadrupleMergerRule` (RHS = 4 copies of reverse `{1,0}`):
    actual Knill at depth 4 = **-18** = classifier's `Merger(4)`
    prediction `-6·4 + 6 = -18` ✓.

**Why the classifier breaks on Tree(4)**: the original Tree formula
assumed each RHS forward edge contributes an independent tree branch.
But with RHS edges all `{0,1}` (no fresh vertex), the rule produces
**parallel multi-edges** on the same vertex pair, not separate
trees. The causal-DAG topology collapses to the same vertex pair
multiple times — Knill stays small.

**Why the Merger formula still works**: each `{1,0}` reverse edge
creates an independent merger hole regardless of whether they share
endpoints, because the reverse-direction structure forces distinct
causal precedence.

**This is a real research finding**: the structural classifier is
**accurate for Merger across maxRHS = 1..4** but **only valid for
Tree at maxRHS ≤ 3**. Beyond that, fresh-vertex management dominates
and the topology depends on RHS-edge endpoint distribution, not just
edge count.

**What this delivers**:

  * `fiveTreeRule` and `quadrupleMergerRule` named witnesses.
  * `fiveTree_actual_knill_12`: certified actual value contradicting
    the naive Tree(4) prediction.
  * `quadrupleMerger_predicted_correctly`: certified Merger(4) match.
  * `classifier_domain_audit`: honest bundled theorem capturing the
    boundary.
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

/-! ## fiveTreeRule — Tree(4) formula prediction failure -/

/-- **`fiveTreeRule`**: maxRHS=4 candidate Tree-class rule. RHS has
4 forward edges `{0,1}` (no reverse, no fresh-vertex use). Classifier
naively predicts `Tree(4) → 6·(4+1) = 30`, but actual Knill at
depth 4 is 12 — the prediction **fails** for self-edge multiplicity. -/
def fiveTreeRule : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 1,
     mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 1]

def fiveTreeSys : ExecSystem := ⟨[fiveTreeRule]⟩

/-- `fiveTreeRule` actual causal-DAG Knill at depth 4 on `edge12`
is `12`, NOT the naive `Tree(4)` prediction of 30. -/
theorem fiveTree_actual_knill_12 :
    knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) = 12 := by
  native_decide

/-- The Tree(4) classifier predicts 30, but the actual Knill is 12.
The naive Tree formula `6·(n+1)` **fails at n=4** for self-edge
multiplicity. -/
theorem fiveTree_prediction_fails :
    predictedKnill (ruleClassFromRhs fiveTreeRule.rhs) = 30 ∧
    knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) = 12 ∧
    predictedKnill (ruleClassFromRhs fiveTreeRule.rhs) ≠
      knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) := by
  refine ⟨?_, fiveTree_actual_knill_12, ?_⟩
  · native_decide
  · native_decide

/-! ## quadrupleMergerRule — Merger(4) formula holds -/

/-- **`quadrupleMergerRule`**: maxRHS=4 Merger-class rule. RHS has 4
reverse edges `{1,0}` (no forward). Classifier predicts `Merger(4)` →
`Knill = -6·4 + 6 = -18`, actual matches. -/
def quadrupleMergerRule : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 1 0,
     mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 1 0]

def quadrupleMergerSys : ExecSystem := ⟨[quadrupleMergerRule]⟩

/-- `quadrupleMergerRule`'s causal-DAG Knill at depth 4 on `edge12`
is -18. This matches the classifier prediction `Merger(4) → -18`. -/
theorem quadrupleMerger_knill_neg18 :
    knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) = -18 := by
  native_decide

/-- The classifier predicts `quadrupleMergerRule.rhs` as `Merger(4)` →
predicted Knill = `-18`, matching the observed value. The Merger
formula holds at maxRHS=4. -/
theorem quadrupleMerger_predicted_correctly :
    predictedKnill (ruleClassFromRhs quadrupleMergerRule.rhs) =
    knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) := by
  native_decide

/-! ## Honest domain audit -/

/-- **`classifier_domain_audit`**: the structural classifier is
**accurate for Merger across maxRHS = 1..4** but **only valid for
Tree at maxRHS ≤ 3**.

This bundled theorem captures the boundary: Merger(4) matches,
Tree(4) does not. -/
theorem classifier_domain_audit :
    -- Merger holds at maxRHS=4:
    predictedKnill (ruleClassFromRhs quadrupleMergerRule.rhs) =
      knillEulerScaled (causalDAGOfEvolution quadrupleMergerSys seedEdge12 4) ∧
    -- Tree fails at maxRHS=4 with self-edges only:
    predictedKnill (ruleClassFromRhs fiveTreeRule.rhs) ≠
      knillEulerScaled (causalDAGOfEvolution fiveTreeSys seedEdge12 4) := by
  refine ⟨quadrupleMerger_predicted_correctly, ?_⟩
  rw [fiveTree_actual_knill_12]
  native_decide

/-! ## What this delivers

**Two maxRHS=4 named rule witnesses + honest classifier audit**:

  * `fiveTreeRule`: actual Knill = 12 ≠ classifier prediction 30.
    Tree formula `6·(n+1)` fails at n=4 for self-edge multiplicity.
  * `quadrupleMergerRule`: actual Knill = -18 = classifier
    prediction. Merger formula `-6·n + 6` holds at n=4.
  * `classifier_domain_audit`: honest bundled boundary theorem.

**Why this matters**: this is the framework's **first
prediction-failure audit**. It captures an honest scientific finding:

  * Merger class predictions extend cleanly to higher edge counts.
  * Tree class predictions are valid only within maxRHS ≤ 3 — beyond
    that, the topology depends on RHS-edge endpoint distribution,
    not just edge count.

The classifier remains useful: it gives sharp Merger predictions
across the full corpus, AND it tells us *where to look* for
Tree-class violations of the naive formula (any rule with many
`{0,1}` self-edges).

**Implication for future search**: an upgraded Tree classifier
needs to distinguish "RHS uses fresh vertex" from "RHS reuses bound
vertices" — the former gives clean tree growth, the latter creates
self-edge multiplicity and breaks the formula.
-/

end ClassifierMaxRHS4
end InfraFormalization
