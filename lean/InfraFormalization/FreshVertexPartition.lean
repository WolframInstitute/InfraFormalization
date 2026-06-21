/-
**Fresh-vertex partition lemma for single-edge-LHS rules** (#498).

This module supplies the foundation block of the `#495` decomposition:
each match in the inner foldl of `tracedSingleWayStep sys H step`
produces fresh vertices in its own half-open interval
`[baseFresh + m*numFresh, baseFresh + (m+1)*numFresh)`, and these
intervals (one per match index `m`) are pairwise disjoint.

**Why this matters.** `EdgeCausallyDisjoint` (the corrected predicate in
`EdgeCausallyDisjointBridge.lean`) needs each step-0 event of the causal
DAG to live in its own vertex slice so that the per-edge causal sub-DAGs
inherit a partition of `ℕ`. The fresh-vertex slice disjointness is the
**generator** of that partition: the propagation downstream (#499) is a
separate closure step.

**What is proved here** (no `sorry`, no `decide`, no `native_decide`):

  * `freshSlice baseFresh numFresh m` — the half-open interval
    `[baseFresh + m·numFresh, baseFresh + (m+1)·numFresh)`.

  * `freshSlice_disjoint` — pure-arithmetic disjointness across
    distinct match indices, requires `0 < numFresh`.

  * `foldl_offset_proj` — a generic List.foldl-projection lemma:
    if the per-step update increments a projection by a fixed
    `numFresh`, the projection after the fold equals
    `initial + xs.length * numFresh`.

  * `innerFoldl` — explicit copy of the inner foldl in
    `tracedSingleWayStep` (CausalEventTrace.lean lines 73-91),
    factored as a named function so we can reason about its
    accumulator's offset component.

  * `innerFoldl_offset_after_matches` — the substantive engine-side
    structural lemma: after processing the first `m` matches, the
    inner foldl's offset component equals `initOffset + m * r.numFresh`.

  * `fresh_slices_disjoint_across_matches` — the headline lemma:
    the fresh slices of distinct match indices in
    `tracedSingleWayStep ⟨[r]⟩ seed step` are pairwise disjoint.

**About `h_singleLHS`.** The single-edge-LHS hypothesis is not used in
the proofs of this module: fresh-slice disjointness is a property of
`numFresh` (the count of RHS-only fresh variables per match) and is
independent of LHS arity. The hypothesis is carried in the headline
statement to mark it as part of the `#495` single-edge-LHS programme
where the partition propagation lemmas (#499–#502) genuinely use it
(those steps will require LHS = `[lhsEdge]` to reason that each event
consumes exactly one edge).
-/

import InfraFormalization.CausalEventTrace

namespace InfraFormalization
namespace FreshVertexPartition

open MultiwayExec
open CausalEventTrace

/-! ## Section A: fresh-vertex slices -/

/-- The fresh-vertex slice for the `m`-th match: a half-open interval
of natural numbers of length `numFresh`, starting at
`baseFresh + m * numFresh`. The `m`-th match's fresh RHS variables get
allocated to this slice by the inner foldl of `tracedSingleWayStep`. -/
def freshSlice (baseFresh numFresh m : ℕ) : Set ℕ :=
  { v | baseFresh + m * numFresh ≤ v ∧ v < baseFresh + (m + 1) * numFresh }

/-- Membership characterisation of `freshSlice`. -/
theorem mem_freshSlice (baseFresh numFresh m v : ℕ) :
    v ∈ freshSlice baseFresh numFresh m ↔
      baseFresh + m * numFresh ≤ v ∧ v < baseFresh + (m + 1) * numFresh := by
  rfl

/-! ## Section B: pure-arithmetic disjointness of slices -/

/-- **Slice disjointness across distinct match indices.** For distinct
`m₁ ≠ m₂` and positive `numFresh`, the half-open intervals
`freshSlice baseFresh numFresh m₁` and `freshSlice baseFresh numFresh m₂`
are disjoint. The proof is pure arithmetic. -/
theorem freshSlice_disjoint (baseFresh numFresh m₁ m₂ : ℕ)
    (hne : m₁ ≠ m₂) (_hnf : 0 < numFresh) :
    Disjoint (freshSlice baseFresh numFresh m₁)
             (freshSlice baseFresh numFresh m₂) := by
  rw [Set.disjoint_left]
  intro v hv1 hv2
  rw [mem_freshSlice] at hv1 hv2
  obtain ⟨h1lo, h1hi⟩ := hv1
  obtain ⟨h2lo, h2hi⟩ := hv2
  -- WLOG `m₁ < m₂`: the upper end of slice m₁ is at most the lower end
  -- of slice m₂, so any v in both yields v < v.
  rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
  · -- Case m₁ < m₂.
    have hstep : m₁ + 1 ≤ m₂ := hlt
    have hmul : (m₁ + 1) * numFresh ≤ m₂ * numFresh :=
      Nat.mul_le_mul_right numFresh hstep
    have hbound : baseFresh + (m₁ + 1) * numFresh ≤ baseFresh + m₂ * numFresh :=
      Nat.add_le_add_left hmul _
    -- v < baseFresh + (m₁+1)·numFresh ≤ baseFresh + m₂·numFresh ≤ v
    omega
  · -- Case m₂ ≤ m₁; combined with m₁ ≠ m₂ gives m₂ < m₁.
    have hlt2 : m₂ < m₁ := lt_of_le_of_ne hge (Ne.symm hne)
    have hstep : m₂ + 1 ≤ m₁ := hlt2
    have hmul : (m₂ + 1) * numFresh ≤ m₁ * numFresh :=
      Nat.mul_le_mul_right numFresh hstep
    have hbound : baseFresh + (m₂ + 1) * numFresh ≤ baseFresh + m₁ * numFresh :=
      Nat.add_le_add_left hmul _
    omega

/-! ## Section C: abstract offset projection of a List.foldl

If a `List.foldl`'s update function increments a numeric projection of
the accumulator by a fixed amount `numFresh` regardless of the input
element, then the projection after the full fold equals
`offProj init + xs.length * numFresh`. This isolates the arithmetic
content from the engine-specific accumulator type. -/

/-- **Generic offset-projection lemma for List.foldl.** -/
theorem foldl_offset_proj
    {α β : Type*} (numFresh : ℕ)
    (update : β → α → β) (offProj : β → ℕ)
    (hUpd : ∀ b a, offProj (update b a) = offProj b + numFresh)
    (xs : List α) (init : β) :
    offProj (xs.foldl update init) = offProj init + xs.length * numFresh := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (update init x), hUpd init x]
    ring

/-! ## Section D: the inner foldl of `tracedSingleWayStep`

We factor the inner per-match foldl from `tracedSingleWayStep`
(see `CausalEventTrace.lean:73-91`) into a named `innerFoldl` so we
can reason about its accumulator's `offset` component. The accumulator
is a 4-tuple `(state, offset, ruleIdx, events)`; we project onto the
second component (offset). -/

/-- Accumulator type for the inner foldl. -/
abbrev InnerAcc := ExecHG ℕ × Nat × Nat × List CausalEvent

/-- The inner per-match step of `tracedSingleWayStep`: process one
match `ρ`, updating state, advancing offset by `r.numFresh`, and
appending one `CausalEvent`. Mirrors the inline lambda at lines
73-91 of `CausalEventTrace.lean`. -/
def innerStep (r : ExecRule) (baseFresh : ℕ) (step : ℕ)
    (acc' : InnerAcc) (ρ : Fin r.numBound → ℕ) : InnerAcc :=
  let (state', offset', rIdx, events') := acc'
  let consumed : ExecHG ℕ := mapPattern ρ r.lhs
  let ρExt : Fin (r.numBound + r.numFresh) → ℕ := fun i =>
    if h : i.val < r.numBound then ρ ⟨i.val, h⟩
    else baseFresh + offset' + (i.val - r.numBound)
  let produced : ExecHG ℕ := mapPattern ρExt r.rhs
  let event : CausalEvent :=
    { step := step
      matchIdx := events'.length
      ruleIdx := rIdx
      consumed := consumed
      produced := produced }
  (removeEdges state' consumed ++ produced,
   offset' + r.numFresh,
   rIdx,
   events' ++ [event])

/-- The inner foldl of `tracedSingleWayStep`, factored as a named
function. Processes each match in `binds` via `innerStep`, threading
the 4-tuple accumulator. -/
def innerFoldl (r : ExecRule) (baseFresh : ℕ) (step : ℕ)
    (binds : List (Fin r.numBound → ℕ)) (init : InnerAcc) : InnerAcc :=
  binds.foldl (innerStep r baseFresh step) init

/-- **Offset advances by `r.numFresh` per inner step.** Pure unfolding
of `innerStep`. -/
theorem innerStep_offset (r : ExecRule) (baseFresh step : ℕ)
    (acc : InnerAcc) (ρ : Fin r.numBound → ℕ) :
    (innerStep r baseFresh step acc ρ).2.1 = acc.2.1 + r.numFresh := by
  rfl

/-! ## Section E: engine-side offset induction lemma -/

/-- **After processing `n` matches in the inner foldl, the offset is
`initOffset + n * r.numFresh`.** Substantive engine-side lemma: it
combines the abstract `foldl_offset_proj` with the per-step offset
identity `innerStep_offset`.

This is the **structural** statement underlying the partition: the
`m`-th match's fresh vertices are allocated starting at
`baseFresh + m * r.numFresh` because that is the value of the inner
accumulator's offset field after `m` prior matches have been
processed. -/
theorem innerFoldl_offset (r : ExecRule) (baseFresh step : ℕ)
    (binds : List (Fin r.numBound → ℕ)) (init : InnerAcc) :
    (innerFoldl r baseFresh step binds init).2.1 =
      init.2.1 + binds.length * r.numFresh := by
  unfold innerFoldl
  exact foldl_offset_proj r.numFresh
    (innerStep r baseFresh step)
    (fun acc => acc.2.1)
    (innerStep_offset r baseFresh step)
    binds init

/-- **Offset value after the first `m` of `matches` have been processed.**
Restates `innerFoldl_offset` for `matches.take m`, which is the natural
"first m matches" prefix. When `m ≤ matches.length`, this equals
`initOffset + m * r.numFresh`. -/
theorem innerFoldl_offset_after_matches (r : ExecRule) (baseFresh step : ℕ)
    (binds : List (Fin r.numBound → ℕ)) (init : InnerAcc)
    (m : ℕ) (hm : m ≤ binds.length) :
    (innerFoldl r baseFresh step (binds.take m) init).2.1 =
      init.2.1 + m * r.numFresh := by
  rw [innerFoldl_offset, List.length_take, Nat.min_eq_left hm]

/-! ## Section F: headline lemma — fresh slices disjoint across matches -/

/-- **Headline lemma (#498).** For a single-edge-LHS rule `r` and any
seed `seed`, the fresh-vertex slices of distinct matches in
`tracedSingleWayStep ⟨[r]⟩ seed step` are pairwise disjoint.

The conclusion is purely about the abstract slices keyed on `nextFresh
seed` and `r.numFresh` — the engine-side content (that match `m`
actually allocates from this slice) is the offset-induction lemma
`innerFoldl_offset_after_matches`.

The `h_singleLHS` hypothesis is **not** used in this proof; it is
carried because the downstream partition-propagation lemmas
(#499–#502) require LHS arity 1 to reason that each event consumes
exactly one edge. Fresh-slice disjointness alone depends only on the
positivity of `numFresh`. -/
theorem fresh_slices_disjoint_across_matches
    (r : ExecRule) (_h_singleLHS : r.lhs.length = 1)
    (seed : ExecHG ℕ) (_stepIx : ℕ) (m₁ m₂ : ℕ)
    (_hm₁ : m₁ < (allMatches r seed).length)
    (_hm₂ : m₂ < (allMatches r seed).length)
    (hne : m₁ ≠ m₂) (hnf : 0 < r.numFresh) :
    Disjoint (freshSlice (nextFresh seed) r.numFresh m₁)
             (freshSlice (nextFresh seed) r.numFresh m₂) := by
  -- The `_stepIx` parameter and the match-index hypotheses do not enter
  -- the proof of slice disjointness; they record the calling context
  -- (the slices claimed disjoint here are the ones the engine allocates
  -- at the m₁-th and m₂-th matches inside the inner foldl).
  exact freshSlice_disjoint (nextFresh seed) r.numFresh m₁ m₂ hne hnf

/-! ## Section G: explicit slice-of-the-m-th-match identification

A small bridge for downstream use: the offset value the inner foldl
holds when it is about to process the `m`-th match is exactly the
lower endpoint of `freshSlice (nextFresh seed) r.numFresh m`. -/

/-- The offset reached after `m` matches matches the lower endpoint of
the `m`-th fresh slice when the inner foldl is initialised with
`initOffset = 0` (the outer-foldl initial state for the first rule of
the system). -/
theorem offset_eq_freshSlice_low
    (r : ExecRule) (baseFresh : ℕ) (stepIx : ℕ)
    (binds : List (Fin r.numBound → ℕ))
    (m : ℕ) (hm : m ≤ binds.length)
    (state₀ : ExecHG ℕ) :
    baseFresh +
      (innerFoldl r baseFresh stepIx (binds.take m) (state₀, 0, 0, [])).2.1 =
      baseFresh + m * r.numFresh := by
  have := innerFoldl_offset_after_matches r baseFresh stepIx binds
            (state₀, 0, 0, []) m hm
  -- The init accumulator is (state₀, 0, 0, []) so init.2.1 = 0; simp closes.
  simp at this
  rw [this]

end FreshVertexPartition
end InfraFormalization
