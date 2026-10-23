/-
Equal contention Knill values for two rule pairs at depths 2 to 5.

B is `discreteBranchialDensity sys d`, the scaled Knill Euler
characteristic of `branchialDAGOfFireAll sys seedEdge12 d`. That graph
joins two events of the same step that consume a common edge. It is
not the Wolfram-model branchial graph. The evolution is `fireAllStep`,
which applies every match of every rule found in the state, including
matches that share edges. It is not a Wolfram model update when
matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE; depth 5 here, depths 2 to 4 in
earlier modules):

  | d | B(eR + tripleMerger) | B(fork + dCyc) |
  |---|----------------------|----------------|
  | 2 |          24          |       24       |
  | 3 |          78          |       78       |
  | 4 |         240          |      240       |
  | 5 |         726          |      726       |

R differs between the two pairs; at depth 4 it is -192 for
`eR + tripleMerger` and 0 for `fork + dCyc` (`MultiRuleRDivergence`).

OPEN: equality of B for the two pairs at every depth. No isomorphism
between the two contention graphs is stated or proved.
-/

import InfraFormalization.BEquivalenceRefinement

namespace InfraFormalization
namespace PersistentBEquivalence

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## Depth-5 B values -/

theorem B_d5_eR_tripleMerger :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 = 726 := by
  native_decide

theorem B_d5_fork_dCyc :
    discreteBranchialDensity fork_doubleCycle_Sys 5 = 726 := by
  native_decide

/-! ## Equal B at depths 2 to 5 -/

/-- `persistent_B_equivalence_4_depths`: `edgeReversal_tripleMerger_Sys`
and `fork_doubleCycle_Sys` have equal `discreteBranchialDensity` at
each of the depths 2, 3, 4, 5. -/
theorem persistent_B_equivalence_4_depths :
    -- d=2: 24
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 =
      discreteBranchialDensity fork_doubleCycle_Sys 2 ∧
    -- d=3: 78
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    -- d=4: 240
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 =
      discreteBranchialDensity fork_doubleCycle_Sys 4 ∧
    -- d=5: 726
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 =
      discreteBranchialDensity fork_doubleCycle_Sys 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## The recurrence at d = 2, 3, 4 -/

/-- `B_geometric_growth_pattern`: for `edgeReversal_tripleMerger_Sys`,
`B(d+1) = 3 · B(d) + 6` at d = 2, 3, 4 (78 = 3·24 + 6,
240 = 3·78 + 6, 726 = 3·240 + 6). -/
theorem B_geometric_growth_pattern :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      3 * discreteBranchialDensity edgeReversal_tripleMerger_Sys 2 + 6 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 =
      3 * discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 + 6 ∧
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 5 =
      3 * discreteBranchialDensity edgeReversal_tripleMerger_Sys 4 + 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Summary

  * `persistent_B_equivalence_4_depths`: equal B for the two rule pairs
    at depths 2, 3, 4, 5.
  * `B_geometric_growth_pattern`: `B(d+1) = 3·B(d) + 6` for
    `edgeReversal_tripleMerger_Sys` at d = 2, 3, 4.

OPEN: equal B at every depth, and the recurrence at every depth.
-/

end PersistentBEquivalence
end InfraFormalization
