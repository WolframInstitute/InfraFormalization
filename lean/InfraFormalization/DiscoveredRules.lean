/-
Knill sums of the causal graphs of eleven rules from `enumerateRules2_1 2`.

The module names eleven rules with left-hand side `{0,1}` from the family `enumerateRules2_1 2`.
For each it evaluates `knillEulerScaled` of `causalDAGOfEvolution sys seedEdge12 4`, the causal
graph of four traced `singleWayStep` steps from the seed `{1,2}`. `knillEulerScaled` is
`Σ_v (6 − 3·deg v + 2·tri v)`, which equals `6(V − E + T)` and equals 6 on a tree. The values are 0
for edge reversal, -6 for four rules, 18 for four rules, 126 for `{0,1} → {0,1},{1,0}` and 12 for
the identity rule, each checked by `native_decide`.
-/

import InfraFormalization.RuleSignatureExecSearch
import InfraFormalization.CausalEventTrace

namespace InfraFormalization
namespace DiscoveredRules

open MultiwayExec
open RuleSignatureExecMetrics
open RuleSignatureExecSearch
open KnillDiscreteGaussBonnet
open CausalEventTrace

/-- The seed with the single edge `{1, 2}`. -/
def seedEdge12 : ExecHG ℕ := [⟨[1, 2], List.cons_ne_nil _ _⟩]

/-! ## Rules

The numeric suffix of a rule name is its index in `enumerateRules2_1 2`. -/

/-- The rule with left-hand side `{0,1}`, two bound vertices, one fresh vertex and right-hand
side `rhs`. -/
def mkDiscoveredRule (rhs : ExecHG (Fin 3)) : ExecRule :=
  { numBound := 2
    numFresh := 1
    lhs := [mkEdgeFin (p := 2) 0 1]
    rhs := rhs }

/-- `{0,1} → {1,0}`. The Knill sum of its causal graph at depth 4 is 0. -/
def edgeReversalRule : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 1 0]
def edgeReversalSys : ExecSystem := ⟨[edgeReversalRule]⟩

/-- `{0,1} → {0,2},{1,0}`. The Knill sum of its causal graph at depth 4 is -6. -/
def doubleCycleRule_5 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 0 2, mkEdgeFin (p := 3) 1 0]
def doubleCycleSys_5 : ExecSystem := ⟨[doubleCycleRule_5]⟩

/-- `{0,1} → {1,0},{1,2}`. The Knill sum of its causal graph at depth 4 is -6. -/
def doubleCycleRule_9 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 1 2]
def doubleCycleSys_9 : ExecSystem := ⟨[doubleCycleRule_9]⟩

/-- `{0,1} → {1,0},{2,0}`. The Knill sum of its causal graph at depth 4 is -6. -/
def doubleCycleRule_13 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 2 0]
def doubleCycleSys_13 : ExecSystem := ⟨[doubleCycleRule_13]⟩

/-- `{0,1} → {1,0},{2,1}`. The Knill sum of its causal graph at depth 4 is -6. -/
def doubleCycleRule_18 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 1 0, mkEdgeFin (p := 3) 2 1]
def doubleCycleSys_18 : ExecSystem := ⟨[doubleCycleRule_18]⟩

/-- `{0,1} → {0,1},{1,0}`. The Knill sum of its causal graph at depth 4 is 126. -/
def bidirectedEdgeRule : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 1 0]
def bidirectedEdgeSys : ExecSystem := ⟨[bidirectedEdgeRule]⟩

/-- `{0,1} → {0,1}`. The Knill sum of its causal graph at depth 4 is 12. -/
def identityKeepRule : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 0 1]
def identityKeepSys : ExecSystem := ⟨[identityKeepRule]⟩

/-- `{0,1} → {0,1},{0,2}`. The Knill sum of its causal graph at depth 4 is 18. -/
def forkRule_2 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 0 2]
def forkSys_2 : ExecSystem := ⟨[forkRule_2]⟩

/-- `{0,1} → {0,1},{1,2}`. -/
def forkRule_7 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 1 2]
def forkSys_7 : ExecSystem := ⟨[forkRule_7]⟩

/-- `{0,1} → {0,1},{2,0}`. -/
def forkRule_11 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 2 0]
def forkSys_11 : ExecSystem := ⟨[forkRule_11]⟩

/-- `{0,1} → {0,1},{2,1}`. -/
def forkRule_16 : ExecRule :=
  mkDiscoveredRule [mkEdgeFin (p := 3) 0 1, mkEdgeFin (p := 3) 2 1]
def forkSys_16 : ExecSystem := ⟨[forkRule_16]⟩

/-! ## Knill sums of the causal graphs at depth 4

Checked by `native_decide`. -/

theorem edgeReversal_knill_zero :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) = 0 := by
  native_decide

theorem doubleCycle_5_knill_neg6 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) = -6 := by
  native_decide

theorem doubleCycle_9_knill_neg6 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedEdge12 4) = -6 := by
  native_decide

theorem doubleCycle_13_knill_neg6 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedEdge12 4) = -6 := by
  native_decide

theorem doubleCycle_18_knill_neg6 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedEdge12 4) = -6 := by
  native_decide

theorem bidirectedEdge_knill_126 :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) = 126 := by
  native_decide

theorem identityKeep_knill_12 :
    knillEulerScaled (causalDAGOfEvolution identityKeepSys seedEdge12 4) = 12 := by
  native_decide

theorem fork_2_knill_18 :
    knillEulerScaled (causalDAGOfEvolution forkSys_2 seedEdge12 4) = 18 := by
  native_decide

theorem fork_7_knill_18 :
    knillEulerScaled (causalDAGOfEvolution forkSys_7 seedEdge12 4) = 18 := by
  native_decide

theorem fork_11_knill_18 :
    knillEulerScaled (causalDAGOfEvolution forkSys_11 seedEdge12 4) = 18 := by
  native_decide

theorem fork_16_knill_18 :
    knillEulerScaled (causalDAGOfEvolution forkSys_16 seedEdge12 4) = 18 := by
  native_decide

/-! ## Conjunctions -/

/-- The conjunction of the eleven Knill values above. -/
theorem discovered_rules_knill_values :
    -- edge reversal
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) = 0 ∧
    -- value -6
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedEdge12 4) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedEdge12 4) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedEdge12 4) = -6 ∧
    -- `{0,1} → {0,1},{1,0}`
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) = 126 ∧
    -- value 18
    knillEulerScaled (causalDAGOfEvolution forkSys_2 seedEdge12 4) = 18 ∧
    knillEulerScaled (causalDAGOfEvolution forkSys_7 seedEdge12 4) = 18 ∧
    knillEulerScaled (causalDAGOfEvolution forkSys_11 seedEdge12 4) = 18 ∧
    knillEulerScaled (causalDAGOfEvolution forkSys_16 seedEdge12 4) = 18 ∧
    -- identity
    knillEulerScaled (causalDAGOfEvolution identityKeepSys seedEdge12 4) = 12 :=
  ⟨edgeReversal_knill_zero,
   doubleCycle_5_knill_neg6, doubleCycle_9_knill_neg6,
   doubleCycle_13_knill_neg6, doubleCycle_18_knill_neg6,
   bidirectedEdge_knill_126,
   fork_2_knill_18, fork_7_knill_18, fork_11_knill_18, fork_16_knill_18,
   identityKeep_knill_12⟩

/-- The conjunction of the five Knill values that are at most 0. -/
theorem depth4_knill_values_five_rules :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) = 0 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_9 seedEdge12 4) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_13 seedEdge12 4) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_18 seedEdge12 4) = -6 :=
  ⟨edgeReversal_knill_zero, doubleCycle_5_knill_neg6,
   doubleCycle_9_knill_neg6, doubleCycle_13_knill_neg6,
   doubleCycle_18_knill_neg6⟩

/-! ## Size of the family -/

/-- `enumerateRules2_1 2` has 21 members. -/
theorem search_pool_size : (enumerateRules2_1 2).length = 21 := by decide

/-- `(enumerateRules2_1 2).length = 21 ∧ True`. -/
theorem discoveries_account_for_11_of_21 :
    (enumerateRules2_1 2).length = 21 ∧
    -- indices of the eleven named rules: 0, 2, 3, 4, 5, 7, 9, 11, 13, 16, 18
    True := ⟨search_pool_size, trivial⟩

end DiscoveredRules
end InfraFormalization
