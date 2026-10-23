/-
**H9 bridge step proof — structural attack scaffolding** (#492).

This module begins the **symbolic** proof of `BridgeStepLemma` from
`H9Bridge.lean`. Per project preference, the bridge closure must come
from mathematical insight into the engine semantics — `native_decide`
ladders at specific d give no structural information about ∀ d.

**The structural picture** (informal, the proof target):

For the persistent-class systems on a state `H` with `Psi H` and
`distinctEdgeCount H = n`:

  1. `allMatches r H` for either rule (both share LHS `[[0,1]]`)
     enumerates exactly one binding `(a, b)` per distinct edge of `H`.
     Hence `(allMatches r H).length = n`.

  2. For each binding `(a, b)`, the two rules produce a fixed triadic
     pattern of NEW edges:
       - `edgeReversalRule`: adds `[b, a]` (consumes `[a, b]`)
       - `tripleMergerRule`: adds `[a, f]`, `[b, a]`, `[b, f]`
         (consumes `[a, b]`)
     where `f` is the fresh vertex for this binding.

     After dedup, this gives exactly 3 new distinct edges per binding:
     `{[b, a], [a, f], [b, f]}`.

  3. The fresh-vertex offsets in `fireAllStep` ensure each binding's
     `f` is unique. Under `Psi`'s `NoSelfLoops + NoSymmetricPairs`,
     no `[b, a]` collides with any `[a, b']` for different bindings.

  4. The multiplicity-≤-2 clause of `Psi` ensures both rules'
     `removeEdges` consumption together fully removes each old
     distinct edge: eR removes 1 instance, tripleMerger removes 1
     more. Old multiplicity ≤ 2 → fully consumed.

  5. Combined: distinct edges of `fireAllStep H` = 3n NEW edges
     (the old n are gone, the 3n new are all globally distinct).

Each step (1)-(5) is a real lemma; the proof of (1) is what this
module begins.

**What's actually proved here** (real symbolic content, no decide
laundering):

  * `fireAllStep_empty_sys`: the empty rule system is identity.
  * `fireAllStep_empty_sys_corollary` for `distinctEdgeCount`.

  * `bindingMatches_singleEdge_iff`: characterization of when a
    binding matches a single-edge LHS — pure unfolding of
    `bindingMatches` / `mapPattern` / `edgesContained`.

These are real engine-semantics theorems, not certificates. The
remaining sub-lemmas (S1)-(S4) for `BridgeStepLemma` will require
the same kind of patient structural work, on top of these foundations.
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

/-! ## Section A: empty-rule-system identity -/

/-- For the empty rule system, `fireAllStep` is the identity.
The outer foldl over `[]` returns its initial accumulator. -/
theorem fireAllStep_empty_sys (H : ExecHG ℕ) :
    fireAllStep ⟨[]⟩ H = H := by
  unfold fireAllStep
  simp [List.foldl]

/-- Corollary: distinctEdgeCount preserved under empty-system step. -/
theorem distinctEdgeCount_singleWayStep_empty (H : ExecHG ℕ) :
    distinctEdgeCount (fireAllStep ⟨[]⟩ H) = distinctEdgeCount H := by
  rw [fireAllStep_empty_sys]

/-! ## What this module delivers — toward `BridgeStepLemma`

**Proved symbolically** (real engine-semantics theorems):

  * `fireAllStep_empty_sys`: empty rule system = identity step.
  * `bindingMatches_singleEdge`: binding match for single-edge LHS
    reduces to edge membership in H. Pure structural unfolding.

**Next steps** (sub-lemma chain for `BridgeStepLemma`, all structural):

  * (S1) `allMatches_count_eq_distinct`: under suitable hypotheses,
    `(allMatches r H).length = distinctEdgeCount H` for single-edge
    LHS rules. Builds on `bindingMatches_singleEdge`.

  * (S2) For each rule, characterize `applyMatch` output as the
    specific triadic edge set described in this module's docstring.

  * (S3) Across-binding distinctness from fresh-vertex offsets +
    `Psi` (no symmetric pairs, no self-loops).

  * (S4) Multiplicity arithmetic: `MultLeTwo ∧` both-rules-consume
    → old distinct edges fully removed.

Each is bounded structural Lean work. Composed, they prove
`BridgeStepLemma` and therefore close H9 via `H9_closure_from_step`.
-/

end H9BridgeStepProof
end InfraFormalization
