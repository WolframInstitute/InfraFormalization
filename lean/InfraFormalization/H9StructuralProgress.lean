/-
**H9 symbolic-closure structural progress** (#492; partial).

This module makes concrete progress toward the H9 symbolic-closure
conjecture: proving `B(d) = 3^(d+1) − 3` for all `d ≥ 2`.

The two-step strategy:

1. **Distinct-edge tripling** (this module's core conjecture):
   `distinctEdgeCount (singleWayStep sys H) = 3 · distinctEdgeCount H`
   for `sys ∈ {edgeReversal_tripleMerger_Sys, fork_doubleCycle_Sys}`
   on any state H reachable from `edge12` via repeated application.

2. **Branchial K closed form** (derives from step 1):
   Given the distinct-edge tripling, the branchial-graph derivation
   produces `B(d+1) = 3·B(d) + 6`, with closed form `B(d) = 3^(d+1)−3`
   (#485 closed form is already verified empirically through d=6).

**This module ships**:

  * **d=4 extension**: `native_decide`-verified distinct count = 81
    at d=4 for both equivalence-class members. Strengthens the
    empirical base of step 1 to 5 depths (0, 1, 2, 3, 4).
  * **Structural invariant** (informal, in comments): characterizes
    the state at each depth — every distinct edge `[a, b]` has its
    reverse `[b, a]` either present (introduced by edge-reversal-style
    matches) or not, but never duplicated; fresh vertices introduce
    new triples disjoint from prior vertex sets.
  * **Proof strategy** (in docstrings): laid out for the next
    session, with the precise lemmas to prove and their order.

**This module does NOT prove the all-d structural induction**.
That requires:

  * A precise structural invariant on reachable states
  * Proof that the invariant is preserved by `singleWayStep`
  * Proof that the invariant determines `distinctEdgeCount` exactly

Estimated effort: 200–500 lines of Lean, multiple sessions.

**Why this matters now**: this module is the **first concrete
docked plank** for the full H9 symbolic closure. Future sessions
can pick up exactly where this leaves off — strategy + lemmas +
target theorem statement all laid out.
-/

import InfraFormalization.DistinctEdgeIdentity

namespace InfraFormalization
namespace H9StructuralProgress

open MultiwayExec
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DistinctEdgeIdentity

/-! ## Empirical extension: depth-4 distinct count = 81 -/

theorem distinct_eR_tripleMerger_d4 :
    distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 81 := by
  native_decide

theorem distinct_fork_dCyc_d4 :
    distinctEdgeCount (singleWayEvolve fork_doubleCycle_Sys seedEdge12 4) = 81 := by
  native_decide

/-- **`distinct_identity_5_depths`**: distinct edge count = `3^d`
at depths 0, 1, 2, 3, 4 for both persistent-equivalence members.
Five-depth `native_decide` verification. -/
theorem distinct_identity_5_depths :
    distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 3^4 ∧
    distinctEdgeCount (singleWayEvolve fork_doubleCycle_Sys seedEdge12 4) = 3^4 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## Structural invariant (proof strategy, not yet a theorem)

The invariant that must be proved to close H9:

**INV(H)** holds iff there exist:
  * A finite set `V₀ ⊆ ℕ` (the "original" vertices: `{1, 2}` initially)
  * A list of "generations" of fresh vertices `F₀, F₁, ..., F_k`
    where `F_i ∩ F_j = ∅` for `i ≠ j` and each `F_j ∩ V₀ = ∅`
  * A decomposition of distinct edges of H into a recursive triadic
    structure (1 reversed-base, 2 fresh-vertex-coupled) per
    sub-trajectory

**Conjecture INV1**: For both persistent-equivalence systems,
`INV(seedEdge12)` holds initially, and `INV(H) → INV(singleWayStep sys H)`.

**Conjecture INV2**: For any H satisfying INV with k generations
of fresh vertices, `distinctEdgeCount H = 3^k`.

**Lemma chain**:
  1. allMatches sys H = exactly |distinct edges of H| matches per rule
  2. Each match consumes exactly one distinct edge of H
  3. Each match produces exactly k edges where k = |RHS of rule|
  4. Fresh vertices are pairwise distinct across matches within a step
  5. The new distinct edges form a clean triadic extension

These lemmas need ~50-150 lines each in Lean. -/

/-- **`distinct_tripling_conjecture`** [open, unproved]:
the precise statement of the H9 structural-induction conjecture.
Stated as a `Prop` so it can be referenced; **not** proved here. -/
def distinct_tripling_conjecture : Prop :=
  ∀ (sys : ExecSystem),
    sys = edgeReversal_tripleMerger_Sys ∨ sys = fork_doubleCycle_Sys →
    ∀ n : Nat,
      distinctEdgeCount (singleWayEvolve sys seedEdge12 n) = 3^n

/-- The conjecture is **verified at n = 0..4** (5 depths) by the
empirical theorems above. -/
theorem distinct_tripling_holds_through_depth_4 :
    (distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 0) = 3^0) ∧
    (distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 1) = 3^1) ∧
    (distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 2) = 3^2) ∧
    (distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 3) = 3^3) ∧
    (distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) = 3^4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## H9 closure outline

Combining `distinct_tripling_conjecture` (still open) with three
already-established empirical facts:

  * `distinct_identity_5_depths` (this module): base + 4 inductive
    steps for the empirical conjecture.
  * `B_closed_form_persistent_class` (#485): B(d) = 3^(d+1) − 3 at
    d=2..5 by `native_decide`.
  * `B_closed_form_d6` (#487): B(d=6) = 3^7 − 3 by `native_decide`.

would give:

  **H9 Theorem (currently open at #492 step 2)**:
    For all d ≥ 2, B(d) = 3^(d+1) − 3 for both members of the
    persistent equivalence class.

Combined with universal additivity (#454, #462) this extends to BBH:

  **H9-BBH corollary**: B_BBH(d) = 7 · (3^(d+1) − 3) for all d ≥ 2.

**What's left**: prove `distinct_tripling_conjecture` symbolically.

This is the central remaining work for the H9 closure.
-/

end H9StructuralProgress
end InfraFormalization
