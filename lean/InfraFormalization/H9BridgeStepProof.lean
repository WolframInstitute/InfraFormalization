/-
Two lemmas about `fireAllStep` with the empty rule system, and an
unproved outline for `BridgeStepLemma`.

`BridgeStepLemma` (in `H9Bridge`) is OPEN. It states that for
`edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`, and every
state `H` with `Psi H`, `fireAllStep` triples `distinctEdgeCount` and
preserves `Psi`. `fireAllStep` applies every match of every rule found
in the state, including matches that share edges. It is not a Wolfram
model update when matches overlap. In particular both rules of a pair
fire on the same edge in one step.

PROVED in this module (no `native_decide`):

  * `fireAllStep_empty_sys`: `fireAllStep ⟨[]⟩ H = H`.
  * `distinctEdgeCount_singleWayStep_empty`: `distinctEdgeCount` is
    unchanged by `fireAllStep ⟨[]⟩`.

Outline for `BridgeStepLemma` (none of these steps is stated or proved
in Lean). Let `n = distinctEdgeCount H`.

  1. For `edgeReversal_tripleMerger_Sys`, both rules have LHS
     `{0,1}`. `allMatches r H` would give one
     binding `(a, b)` per distinct edge, so `n` matches per rule.
  2. For a binding `(a, b)` with fresh vertex `f`, `edgeReversalRule`
     produces `[b, a]` and `tripleMergerRule` produces `[a, f]`,
     `[b, a]`, `[b, f]`. Both consume `[a, b]`.
  3. The fresh-vertex offsets in `fireAllStep` would make each `f`
     unique, and `Psi` (no self-loops, no symmetric pairs) would rule
     out collisions between new edges of different bindings.
  4. `Psi` bounds the multiplicity of each edge by 2, so the two
     consumptions would remove every old edge.
  5. Together these would give `3n` distinct edges after the step.
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

/-- For the empty rule system, `fireAllStep` is the identity.
The outer foldl over `[]` returns its initial accumulator. -/
theorem fireAllStep_empty_sys (H : ExecHG ℕ) :
    fireAllStep ⟨[]⟩ H = H := by
  unfold fireAllStep
  simp [List.foldl]

/-- `distinctEdgeCount (fireAllStep ⟨[]⟩ H) = distinctEdgeCount H`. -/
theorem distinctEdgeCount_singleWayStep_empty (H : ExecHG ℕ) :
    distinctEdgeCount (fireAllStep ⟨[]⟩ H) = distinctEdgeCount H := by
  rw [fireAllStep_empty_sys]

/-! ## Summary

PROVED (no `native_decide`):

  * `fireAllStep_empty_sys`: `fireAllStep ⟨[]⟩ H = H`.
  * `distinctEdgeCount_singleWayStep_empty`: `distinctEdgeCount` is
    unchanged by `fireAllStep ⟨[]⟩`. The name says `singleWayStep`;
    the statement is about `fireAllStep`.

OPEN: `BridgeStepLemma`. The sub-lemmas (1)-(5) in the module header
are not stated in Lean.
-/

end H9BridgeStepProof
end InfraFormalization
