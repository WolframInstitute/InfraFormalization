/-
Five two-rule systems and the scaled Knill values of their fire-all
causal graphs on `seedEdge12` at depth 3.

Each system is a list of two rules. The causal graph is
`causalDAGOfFireAll`, built from `tracedFireAllEvolve`. `fireAllStep`
applies every match of every rule found in the state, including matches
that share edges. Both rules of a system therefore fire on the same edge
in one step. It is not a Wolfram model update when matches overlap, and
the values below do not describe Wolfram model evolutions.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE). The
column "1 - K/6" is the integer `1 - K / 6`. Other modules call it the
number of holes. It is a value computed from K, and this module proves
no statement about cycles or holes of the graph.

| System                                | K at depth 3 | 1 - K/6 |
|---------------------------------------|--------------|---------|
| `edgeReversal + identityKeep`         |  -24         |   5     |
| `edgeReversal + forkRule_2`           |  -42         |   8     |
| `edgeReversal + doubleCycle_5`        |  -24         |   5     |
| `forkRule_2 + doubleCycle_5`          |    0         |   1     |
| `edgeReversal + tripleMerger`         |  -36         |   7     |

The module proves no comparison with single-rule systems.
-/

import InfraFormalization.DiscoveredRulesExpanded

namespace InfraFormalization
namespace MultiRuleDiscovered

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded

/-! ## Five named 2-rule systems -/

/-- `edgeReversalRule` and `identityKeepRule`. Under the fire-all
operator both rules fire on every match in each step. Depth-3 scaled
Knill value -24. -/
def edgeReversal_identity_Sys : ExecSystem :=
  ⟨[edgeReversalRule, identityKeepRule]⟩

/-- `edgeReversalRule` and `forkRule_2`. Depth-3 scaled Knill value
-42. -/
def edgeReversal_fork_Sys : ExecSystem :=
  ⟨[edgeReversalRule, forkRule_2]⟩

/-- `edgeReversalRule` and `doubleCycleRule_5`. Depth-3 scaled Knill
value -24. -/
def edgeReversal_doubleCycle_Sys : ExecSystem :=
  ⟨[edgeReversalRule, doubleCycleRule_5]⟩

/-- `forkRule_2` and `doubleCycleRule_5`. Depth-3 scaled Knill value 0. -/
def fork_doubleCycle_Sys : ExecSystem :=
  ⟨[forkRule_2, doubleCycleRule_5]⟩

/-- `edgeReversalRule` and `tripleMergerRule`. Depth-3 scaled Knill
value -36. -/
def edgeReversal_tripleMerger_Sys : ExecSystem :=
  ⟨[edgeReversalRule, tripleMergerRule]⟩

/-! ## Depth-3 values -/

theorem edgeReversal_identity_knill_neg24 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = -24 := by
  native_decide

theorem edgeReversal_fork_knill_neg42 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = -42 := by
  native_decide

theorem edgeReversal_doubleCycle_knill_neg24 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_doubleCycle_Sys seedEdge12 3) = -24 := by
  native_decide

theorem fork_doubleCycle_knill_zero :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedEdge12 3) = 0 := by
  native_decide

theorem edgeReversal_tripleMerger_knill_neg36 :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 3) = -36 := by
  native_decide

/-! ## Conjunction of the five values -/

/-- The five depth-3 scaled Knill values of this module: -24, -42, -24,
0 and -36. -/
theorem multi_rule_discoveries :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys seedEdge12 3) = -24 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = -42 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_doubleCycle_Sys seedEdge12 3) = -24 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys seedEdge12 3) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 3) = -36 :=
  ⟨edgeReversal_identity_knill_neg24,
   edgeReversal_fork_knill_neg42,
   edgeReversal_doubleCycle_knill_neg24,
   fork_doubleCycle_knill_zero,
   edgeReversal_tripleMerger_knill_neg36⟩

/-! ## The value for `edgeReversal + forkRule_2`

Among the five systems of this module, `edgeReversal + forkRule_2` has
the lowest scaled Knill value at depth 3 (-42), so `1 - K/6 = 8`. The
module does not compare this value with systems outside the five. -/

/-- The scaled Knill value of the fire-all causal graph of
`edgeReversal + forkRule_2` on `seedEdge12` at depth 3 is -42, and the
integer `1 - (-42) / 6` equals 8. -/
theorem highest_merger_rate_multi_rule :
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys seedEdge12 3) = -42 ∧
    (1 - (-42 : Int) / 6) = 8 :=
  ⟨edgeReversal_fork_knill_neg42, by decide⟩

end MultiRuleDiscovered
end InfraFormalization
