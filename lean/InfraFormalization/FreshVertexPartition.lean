/-
Disjoint fresh-vertex intervals for the matches of one rule.

This module defines `freshSlice baseFresh numFresh m`, the interval
`[baseFresh + m·numFresh, baseFresh + (m+1)·numFresh)`, and proves that the intervals for distinct
`m` are disjoint when `0 < numFresh`.
It defines `innerStep` and `innerFoldl`, a copy of the per-match fold written inline in
`tracedSingleWayStep` (`CausalEventTrace.lean`), and proves that after `m` matches the offset
component of the fold equals its initial value plus `m * r.numFresh`.
No theorem in this module proves that `innerFoldl` agrees with the fold inside
`tracedSingleWayStep`.
-/

import InfraFormalization.CausalEventTrace

namespace InfraFormalization
namespace FreshVertexPartition

open MultiwayExec
open CausalEventTrace

/-! ## Section A: fresh-vertex slices -/

/-- The set of natural numbers `v` with `baseFresh + m * numFresh ≤ v < baseFresh + (m + 1) * numFresh`. -/
def freshSlice (baseFresh numFresh m : ℕ) : Set ℕ :=
  { v | baseFresh + m * numFresh ≤ v ∧ v < baseFresh + (m + 1) * numFresh }

/-- `v ∈ freshSlice baseFresh numFresh m` if and only if
`baseFresh + m * numFresh ≤ v ∧ v < baseFresh + (m + 1) * numFresh`. -/
theorem mem_freshSlice (baseFresh numFresh m v : ℕ) :
    v ∈ freshSlice baseFresh numFresh m ↔
      baseFresh + m * numFresh ≤ v ∧ v < baseFresh + (m + 1) * numFresh := by
  rfl

/-! ## Section B: disjointness of slices -/

/-- For `m₁ ≠ m₂`, `freshSlice baseFresh numFresh m₁` and `freshSlice baseFresh numFresh m₂` are
disjoint. The hypothesis `0 < numFresh` is not used in the proof. -/
theorem freshSlice_disjoint (baseFresh numFresh m₁ m₂ : ℕ)
    (hne : m₁ ≠ m₂) (_hnf : 0 < numFresh) :
    Disjoint (freshSlice baseFresh numFresh m₁)
             (freshSlice baseFresh numFresh m₂) := by
  rw [Set.disjoint_left]
  intro v hv1 hv2
  rw [mem_freshSlice] at hv1 hv2
  obtain ⟨h1lo, h1hi⟩ := hv1
  obtain ⟨h2lo, h2hi⟩ := hv2
  -- Case split on `m₁ < m₂`; in each case the upper end of the lower slice is at most the
  -- lower end of the upper slice.
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

/-! ## Section C: a numeric projection of `List.foldl` -/

/-- If `offProj (update b a) = offProj b + numFresh` for all `b` and `a`, then
`offProj (xs.foldl update init) = offProj init + xs.length * numFresh`. -/
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

/-! ## Section D: the per-match fold

The accumulator is a 4-tuple `(state, offset, ruleIdx, events)`. -/

/-- The accumulator type `(state, offset, ruleIdx, events)`. -/
abbrev InnerAcc := ExecHG ℕ × Nat × Nat × List CausalEvent

/-- One step for the match `ρ`: remove the consumed edges, append the produced edges with fresh
vertices numbered from `baseFresh + offset`, add `r.numFresh` to the offset, and append one
`CausalEvent`. It is written to match the per-match lambda in `tracedSingleWayStep`. -/
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

/-- `binds.foldl (innerStep r baseFresh step) init`. -/
def innerFoldl (r : ExecRule) (baseFresh : ℕ) (step : ℕ)
    (binds : List (Fin r.numBound → ℕ)) (init : InnerAcc) : InnerAcc :=
  binds.foldl (innerStep r baseFresh step) init

/-- `innerStep` adds `r.numFresh` to the offset component. -/
theorem innerStep_offset (r : ExecRule) (baseFresh step : ℕ)
    (acc : InnerAcc) (ρ : Fin r.numBound → ℕ) :
    (innerStep r baseFresh step acc ρ).2.1 = acc.2.1 + r.numFresh := by
  rfl

/-! ## Section E: offset after the fold -/

/-- The offset component of `innerFoldl r baseFresh step binds init` equals
`init.2.1 + binds.length * r.numFresh`. -/
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

/-- For `m ≤ binds.length`, the offset component of `innerFoldl` over `binds.take m` equals
`init.2.1 + m * r.numFresh`. -/
theorem innerFoldl_offset_after_matches (r : ExecRule) (baseFresh step : ℕ)
    (binds : List (Fin r.numBound → ℕ)) (init : InnerAcc)
    (m : ℕ) (hm : m ≤ binds.length) :
    (innerFoldl r baseFresh step (binds.take m) init).2.1 =
      init.2.1 + m * r.numFresh := by
  rw [innerFoldl_offset, List.length_take, Nat.min_eq_left hm]

/-! ## Section F: slices for distinct match indices -/

/-- For `m₁ ≠ m₂`, `freshSlice (nextFresh seed) r.numFresh m₁` and
`freshSlice (nextFresh seed) r.numFresh m₂` are disjoint. The proof applies `freshSlice_disjoint`.
The hypotheses `r.lhs.length = 1` and `m₁, m₂ < (allMatches r seed).length` and the argument
`_stepIx` are not used. -/
theorem fresh_slices_disjoint_across_matches
    (r : ExecRule) (_h_singleLHS : r.lhs.length = 1)
    (seed : ExecHG ℕ) (_stepIx : ℕ) (m₁ m₂ : ℕ)
    (_hm₁ : m₁ < (allMatches r seed).length)
    (_hm₂ : m₂ < (allMatches r seed).length)
    (hne : m₁ ≠ m₂) (hnf : 0 < r.numFresh) :
    Disjoint (freshSlice (nextFresh seed) r.numFresh m₁)
             (freshSlice (nextFresh seed) r.numFresh m₂) := by
  exact freshSlice_disjoint (nextFresh seed) r.numFresh m₁ m₂ hne hnf

/-! ## Section G: offset and the lower end of a slice -/

/-- With initial accumulator `(state₀, 0, 0, [])` and `m ≤ binds.length`, `baseFresh` plus the
offset after `innerFoldl` over `binds.take m` equals `baseFresh + m * r.numFresh`, the lower end of
`freshSlice baseFresh r.numFresh m`. -/
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
  -- The initial offset is 0.
  simp at this
  rw [this]

end FreshVertexPartition
end InfraFormalization
