/-
Causal level of the events of a trajectory, and sums of consumed and produced edge counts.

For a trajectory of `M` applications of one rule `r`, the module proves that the consumed
edge counts sum to `M * r.lhsSize` and the produced edge counts to `M * r.rhsSize`, and that
the two sums are equal when `r` is conservative. It defines the Boolean causal-predecessor
test `isCausalPred` and the causal level `level`, proves `level τ j + 1 ≤ level τ i` when `j`
is a causal predecessor of `i` with `j < i`, and proves that `isCausalPred` agrees with
`causallyPrecedes` from `Causal.lean`.
-/

import InfraFormalization.ParallelSchedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- If every application of `τ` uses the rule `r`, the consumed-edge counts of the
applications sum to `τ.applications.length * r.lhsSize`. -/
theorem total_in_degree_eq {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (r : Rule P)
    (hall : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1 = r) :
    (Finset.univ.sum
      fun i : Fin τ.applications.length =>
        (τ.applications.get i).2.2.consumed.card)
      = τ.applications.length * r.lhsSize := by
  rw [Finset.sum_congr rfl (fun i _ =>
        show (τ.applications.get i).2.2.consumed.card = r.lhsSize from ?_)]
  · simp
  · rw [Application.consumed_card, hall i.val i.isLt]

/-- If every application of `τ` uses the rule `r`, the produced-edge counts of the
applications sum to `τ.applications.length * r.rhsSize`. -/
theorem total_out_degree_eq {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (r : Rule P)
    (hall : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1 = r) :
    (Finset.univ.sum
      fun i : Fin τ.applications.length =>
        (τ.applications.get i).2.2.produced.card)
      = τ.applications.length * r.rhsSize := by
  rw [Finset.sum_congr rfl (fun i _ =>
        show (τ.applications.get i).2.2.produced.card = r.rhsSize from ?_)]
  · simp
  · rw [Application.produced_card, hall i.val i.isLt]

/-- If every application of `τ` uses the conservative rule `r`, the consumed-edge counts and
the produced-edge counts have equal sums. -/
theorem total_in_eq_total_out {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (r : Rule P) (hcons : r.IsConservative)
    (hall : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1 = r) :
    (Finset.univ.sum
      fun i : Fin τ.applications.length => (τ.applications.get i).2.2.consumed.card) =
    (Finset.univ.sum
      fun i : Fin τ.applications.length => (τ.applications.get i).2.2.produced.card) := by
  rw [total_in_degree_eq τ r hall, total_out_degree_eq τ r hall]
  unfold Rule.IsConservative at hcons
  rw [hcons]

/-- `true` when both indices are in range and some hyperedge produced by application `j` is
consumed by application `i`. Decidability of the existential is classical. -/
noncomputable def isCausalPred {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) : Bool :=
  if h : j < τ.applications.length ∧ i < τ.applications.length then
    let _ : Decidable (∃ e : Hyperedge V,
      e ∈ (τ.applications.get ⟨j, h.1⟩).2.2.produced ∧
      e ∈ (τ.applications.get ⟨i, h.2⟩).2.2.consumed) := Classical.propDecidable _
    decide (∃ e : Hyperedge V,
      e ∈ (τ.applications.get ⟨j, h.1⟩).2.2.produced ∧
      e ∈ (τ.applications.get ⟨i, h.2⟩).2.2.consumed)
  else false

/-- The causal level of event `i`: the supremum of `1 + level τ j` over indices `j < i` with
`isCausalPred τ j i`, and 0 if there are none. Defined by well-founded recursion on `i`. -/
noncomputable def level {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) : Nat :=
  (Finset.range i).attach.sup fun ⟨j, hj⟩ =>
    if isCausalPred τ j i then
      1 + level τ j
    else 0
termination_by i
decreasing_by
  exact Finset.mem_range.mp hj

/-- The defining equation of `level`. -/
theorem level_eq {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) :
    level τ i = (Finset.range i).attach.sup fun ⟨j, hj⟩ =>
      if isCausalPred τ j i then 1 + level τ j else 0 := by
  rw [level]

/-- If `j < i` and `isCausalPred τ j i = true`, then `level τ j + 1 ≤ level τ i`. -/
theorem level_add_one_le_of_isCausalPred {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) (hlt : j < i)
    (hcp : isCausalPred τ j i = true) :
    level τ j + 1 ≤ level τ i := by
  -- The function whose supremum defines `level τ i`.
  set f : {x // x ∈ Finset.range i} → Nat :=
    fun ⟨j', _⟩ => if isCausalPred τ j' i then 1 + level τ j' else 0
  with hf
  -- Unfold `level` at `i` only.
  have heq : level τ i = (Finset.range i).attach.sup f := by
    rw [show level τ i = _ from level_eq τ i]
  rw [heq]
  have hjr : j ∈ Finset.range i := Finset.mem_range.mpr hlt
  have hstep : f ⟨j, hjr⟩ = 1 + level τ j := by
    simp [hf, hcp]
  -- level τ j + 1 = f ⟨j, hjr⟩ ≤ sup of f.
  calc level τ j + 1
      = 1 + level τ j := by omega
    _ = f ⟨j, hjr⟩ := hstep.symm
    _ ≤ (Finset.range i).attach.sup f :=
        Finset.le_sup (f := f) (Finset.mem_attach _ ⟨j, hjr⟩)

/-- If `j < i` and `level τ j = level τ i`, then `isCausalPred τ j i = false`. -/
theorem no_causal_edge_within_level {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) (hlt : j < i)
    (h_same_level : level τ j = level τ i) :
    isCausalPred τ j i = false := by
  by_contra h
  push_neg at h
  -- h : ¬ (isCausalPred τ j i = false), so isCausalPred τ j i = true.
  have hcp : isCausalPred τ j i = true := by
    cases hcp : isCausalPred τ j i with
    | false => exact absurd hcp h
    | true => rfl
  have h_mono : level τ j + 1 ≤ level τ i :=
    level_add_one_le_of_isCausalPred τ j i hlt hcp
  omega

/-- `causallyPrecedes τ i j` holds if and only if `i < j`, `j` is in range and
`isCausalPred τ i j = true`. -/
theorem causallyPrecedes_iff_isCausalPred
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i j : Nat) :
    causallyPrecedes τ i j ↔
      (i < j ∧ j < τ.applications.length ∧ isCausalPred τ i j = true) := by
  unfold causallyPrecedes isCausalPred
  constructor
  · rintro ⟨hlt, hj, e, hprod, hcons⟩
    refine ⟨hlt, hj, ?_⟩
    have hi : i < τ.applications.length := by omega
    have hband : i < τ.applications.length ∧ j < τ.applications.length :=
      ⟨hi, hj⟩
    rw [dif_pos hband]
    letI := Classical.propDecidable (∃ e : Hyperedge V,
      e ∈ (τ.applications.get ⟨i, hband.1⟩).2.2.produced ∧
      e ∈ (τ.applications.get ⟨j, hband.2⟩).2.2.consumed)
    exact decide_eq_true ⟨e, hprod, hcons⟩
  · rintro ⟨hlt, hj, hcp⟩
    have hi : i < τ.applications.length := by omega
    have hband : i < τ.applications.length ∧ j < τ.applications.length :=
      ⟨hi, hj⟩
    rw [dif_pos hband] at hcp
    letI := Classical.propDecidable (∃ e : Hyperedge V,
      e ∈ (τ.applications.get ⟨i, hband.1⟩).2.2.produced ∧
      e ∈ (τ.applications.get ⟨j, hband.2⟩).2.2.consumed)
    have := of_decide_eq_true hcp
    obtain ⟨e, hprod, hcons⟩ := this
    exact ⟨hlt, hj, e, hprod, hcons⟩

end InfraFormalization
