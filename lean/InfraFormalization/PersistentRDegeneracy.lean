/-
Values of `discreteRicciScalar` (R) and `discreteBranchialDensity` (B)
for `forkRule_2 + doubleCycle_5` at depths 2, 3 and 4.

R is the scaled Knill value of `causalDAGOfFireAll sys seedEdge12 d`. B
is the scaled Knill value of `branchialDAGOfFireAll sys seedEdge12 d`,
the graph that links two events of the same step that consume a common
edge value. This relation is not the branchial graph of the Wolfram
model. Both graphs come from `tracedFireAllEvolve`, which applies every
match of every rule found in the state, including matches that share
edges. It is not a Wolfram model update when matches overlap. R is an
integer computed from a finite graph. It is not the Ricci scalar of a
metric, and R = 0 is not a vacuum condition.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  | depth | R | B   |
  |-------|---|-----|
  |   2   | 6 |  24 |
  |   3   | 0 |  78 |
  |   4   | 0 | 240 |
-/

import InfraFormalization.CorpusObservableTable

namespace InfraFormalization
namespace PersistentRDegeneracy

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## Values at depths 2 and 4 -/

theorem R_fork_dCyc_2 : discreteRicciScalar fork_doubleCycle_Sys 2 = 6 := by
  native_decide

theorem B_fork_dCyc_2 : discreteBranchialDensity fork_doubleCycle_Sys 2 = 24 := by
  native_decide

theorem R_fork_dCyc_4 : discreteRicciScalar fork_doubleCycle_Sys 4 = 0 := by
  native_decide

theorem B_fork_dCyc_4 : discreteBranchialDensity fork_doubleCycle_Sys 4 = 240 := by
  native_decide

/-! ## Values at depths 2, 3 and 4 -/

/-- For `forkRule_2 + doubleCycle_5` on `seedEdge12`:

  * d=2: R = 6, B = 24.
  * d=3: R = 0, B = 78.
  * d=4: R = 0, B = 240. -/
theorem persistent_R_degeneracy :
    discreteRicciScalar fork_doubleCycle_Sys 2 = 6 ∧
    discreteRicciScalar fork_doubleCycle_Sys 3 = 0 ∧
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 2 = 24 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 3 = 78 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 4 = 240 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## R = 0 at depths 3 and 4, B increases -/

/-- For `forkRule_2 + doubleCycle_5`: R = 0 at depths 3 and 4, and B at
depth 4 (240) is greater than B at depth 3 (78). -/
theorem B_grows_under_R_persistence :
    discreteRicciScalar fork_doubleCycle_Sys 3 = 0 ∧
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 ∧
    discreteBranchialDensity fork_doubleCycle_Sys 4 >
      discreteBranchialDensity fork_doubleCycle_Sys 3 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · rw [B_fork_dCyc_4, CorpusObservableTable.B_fork_dCyc_3]; decide

/-! ## Contents

  * `R_fork_dCyc_2`, `B_fork_dCyc_2`, `R_fork_dCyc_4`, `B_fork_dCyc_4`:
    four values.
  * `persistent_R_degeneracy`: R and B at depths 2, 3 and 4.
  * `B_grows_under_R_persistence`: R = 0 at depths 3 and 4, and B at
    depth 4 exceeds B at depth 3.

All statements concern `forkRule_2 + doubleCycle_5` on `seedEdge12` at
depths 2 to 4. The value of R at depths 5 and above is not computed
here.
-/

end PersistentRDegeneracy
end InfraFormalization
