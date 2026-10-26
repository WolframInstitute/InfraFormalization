/-
Three rules with three right-hand edges and their single-way Knill values.

This module defines three rules with left-hand side `{0,1}`, bound
vertices 0 and 1, and fresh vertex 2: `superHyperRule` with right-hand
side `{0,1},{0,2},{1,0}`, `fourTreeRule` with `{0,1},{0,2},{1,2}`, and
`tripleMergerRule` with `{0,2},{1,0},{1,2}`. For the depth-4 single-way
causal graph `causalDAGOfEvolution sys seed 4`, the scaled Knill values
(6χ) are 156, 24 and -12 on `seedEdge12` and 312, 48 and -24 on
`seedPath123`, checked by `native_decide`.
-/

import InfraFormalization.StableDiscoveredRules

namespace InfraFormalization
namespace DiscoveredRulesExpanded

open MultiwayExec
open RuleSignatureExecMetrics
open RuleSignatureExecSearch
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules

/-! ## The three rules -/

/-- The rule `{0,1} → {0,1},{0,2},{1,0}`. -/
def superHyperRule : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 1,
     mkEdgeFin (p := 3) 0 2,
     mkEdgeFin (p := 3) 1 0]
def superHyperSys : ExecSystem := ⟨[superHyperRule]⟩

/-- The rule `{0,1} → {0,1},{0,2},{1,2}`. -/
def fourTreeRule : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 1,
     mkEdgeFin (p := 3) 0 2,
     mkEdgeFin (p := 3) 1 2]
def fourTreeSys : ExecSystem := ⟨[fourTreeRule]⟩

/-- The rule `{0,1} → {0,2},{1,0},{1,2}`. -/
def tripleMergerRule : ExecRule :=
  mkDiscoveredRule
    [mkEdgeFin (p := 3) 0 2,
     mkEdgeFin (p := 3) 1 0,
     mkEdgeFin (p := 3) 1 2]
def tripleMergerSys : ExecSystem := ⟨[tripleMergerRule]⟩

/-! ## Single-way causal Knill values on `seedEdge12` at depth 4 -/

theorem superHyper_knill_156 :
    knillEulerScaled (causalDAGOfEvolution superHyperSys seedEdge12 4) = 156 := by
  native_decide

theorem fourTree_knill_24 :
    knillEulerScaled (causalDAGOfEvolution fourTreeSys seedEdge12 4) = 24 := by
  native_decide

theorem tripleMerger_knill_neg12 :
    knillEulerScaled (causalDAGOfEvolution tripleMergerSys seedEdge12 4) = -12 := by
  native_decide

/-! ## Values on `seedPath123` at depth 4

On the two-edge seed `seedPath123` each value is twice the value on
`seedEdge12`. -/

theorem superHyper_path_knill :
    knillEulerScaled (causalDAGOfEvolution superHyperSys StableDiscoveredRules.seedPath123 4) = 312 := by
  native_decide

theorem fourTree_path_knill :
    knillEulerScaled (causalDAGOfEvolution fourTreeSys StableDiscoveredRules.seedPath123 4) = 48 := by
  native_decide

theorem tripleMerger_path_knill :
    knillEulerScaled (causalDAGOfEvolution tripleMergerSys StableDiscoveredRules.seedPath123 4) = -24 := by
  native_decide

theorem superHyper_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution superHyperSys StableDiscoveredRules.seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution superHyperSys seedEdge12 4) := by
  rw [superHyper_path_knill, superHyper_knill_156]; rfl

theorem fourTree_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution fourTreeSys StableDiscoveredRules.seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution fourTreeSys seedEdge12 4) := by
  rw [fourTree_path_knill, fourTree_knill_24]; rfl

theorem tripleMerger_per_edge_invariant :
    knillEulerScaled (causalDAGOfEvolution tripleMergerSys StableDiscoveredRules.seedPath123 4) =
    2 * knillEulerScaled (causalDAGOfEvolution tripleMergerSys seedEdge12 4) := by
  rw [tripleMerger_path_knill, tripleMerger_knill_neg12]; rfl

/-! ## Conjunctions -/

/-- The three depth-4 values on `seedEdge12`: 156, 24 and -12. -/
theorem new_classes_summary :
    knillEulerScaled (causalDAGOfEvolution superHyperSys seedEdge12 4) = 156 ∧
    knillEulerScaled (causalDAGOfEvolution fourTreeSys seedEdge12 4) = 24 ∧
    knillEulerScaled (causalDAGOfEvolution tripleMergerSys seedEdge12 4) = -12 :=
  ⟨superHyper_knill_156, fourTree_knill_24, tripleMerger_knill_neg12⟩

/-- For the three rules at depth 4, the value on `seedPath123` is twice
the value on `seedEdge12`. -/
theorem new_classes_stable_per_edge :
    knillEulerScaled (causalDAGOfEvolution superHyperSys StableDiscoveredRules.seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution superHyperSys seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution fourTreeSys StableDiscoveredRules.seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution fourTreeSys seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution tripleMergerSys StableDiscoveredRules.seedPath123 4) =
      2 * knillEulerScaled (causalDAGOfEvolution tripleMergerSys seedEdge12 4) :=
  ⟨superHyper_per_edge_invariant,
   fourTree_per_edge_invariant,
   tripleMerger_per_edge_invariant⟩

end DiscoveredRulesExpanded
end InfraFormalization
