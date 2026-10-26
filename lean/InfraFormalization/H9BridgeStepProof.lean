/-
`fireAllStep` with the empty rule system.

This module proves that `fireAllStep ⟨[]⟩ H = H` and that `distinctEdgeCount` is unchanged by
`fireAllStep ⟨[]⟩`.
`fireAllStep` applies every match of every rule, including overlapping matches, and is not a
Wolfram model update.
The statement `BridgeStepLemma` in `H9Bridge` is not proved here or elsewhere in the library.
-/

import InfraFormalization.H9Bridge

namespace InfraFormalization
namespace H9BridgeStepProof

open MultiwayExec
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DistinctEdgeIdentity
open H9Closure
open H9Bridge

/-! ## Section A: the empty rule system -/

/-- `fireAllStep ⟨[]⟩ H = H`. -/
theorem fireAllStep_empty_sys (H : ExecHG ℕ) :
    fireAllStep ⟨[]⟩ H = H := by
  unfold fireAllStep
  simp [List.foldl]

/-- `distinctEdgeCount (fireAllStep ⟨[]⟩ H) = distinctEdgeCount H`. The statement uses
`fireAllStep`, not `singleWayStep`. -/
theorem distinctEdgeCount_fireAllStep_empty (H : ExecHG ℕ) :
    distinctEdgeCount (fireAllStep ⟨[]⟩ H) = distinctEdgeCount H := by
  rw [fireAllStep_empty_sys]


end H9BridgeStepProof
end InfraFormalization
