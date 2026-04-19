/-
Causal-DAG level function and basic degree-sum theorems.

This file takes the first steps toward the parallel-layer bound for
conservative rules (Theorem B). It:

1. Proves `total_in_degree_eq` and `total_out_degree_eq`: the total
   consumed / produced cardinalities sum to `M * r.(lhs|rhs)Size`.
2. Proves `total_in_eq_total_out` for conservative rules (the causal
   DAG is balanced).
3. Defines `level`: the causal-DAG level of an event, via classical
   well-founded recursion on the Nat index.

The full parallel-layer bound (each level has ≤ ⌊N/k⌋ events) requires
a state-at-each-level tracker and a monotonicity lemma
(`level τ j + 1 ≤ level τ i` whenever `j` causally precedes `i`).
The monotonicity lemma stumbled on `Nat.strongRecOn`'s unfolding
behaviour; a cleaner approach (building level into a list iteratively
so the equation is `List.get?`-based rather than strong-recursor-based)
is the planned next step.
-/

import InfraFormalization.ParallelSchedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **Total-in-degree theorem.** For a trajectory all of whose
applications use the same conservative rule `r`, the sum of the
consumed-edge cardinalities over all events is `M * r.lhsSize`. -/
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

/-- **Total-out-degree theorem.** Same for produced edges. -/
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

/-- **Balance theorem.** For a conservative rule, total in-degree and
total out-degree are equal (both `= M * r.lhsSize`). -/
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

/-- Causal-predecessor indicator (Bool), using classical decidability
for the hyperedge existential. -/
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

/-- **Causal level** of an event: length of the longest chain of
causal-predecessor edges ending at it. Defined via well-founded
recursion on Nat; equivalently, `level τ i` is `1 + sup over causal
predecessors of their level`, with the sup being 0 when there are no
predecessors. -/
noncomputable def level {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) : Nat :=
  (Finset.range i).attach.sup fun ⟨j, hj⟩ =>
    if isCausalPred τ j i then
      1 + level τ j
    else 0
termination_by i
decreasing_by
  exact Finset.mem_range.mp hj

/-- **Level unfolding equation.** -/
theorem level_eq {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) :
    level τ i = (Finset.range i).attach.sup fun ⟨j, hj⟩ =>
      if isCausalPred τ j i then 1 + level τ j else 0 := by
  rw [level]

/-- **Level monotonicity.** If `j` causally precedes `i`
(indicated by `isCausalPred τ j i = true` plus `j < i`), then
`level τ j + 1 ≤ level τ i`. -/
theorem level_add_one_le_of_isCausalPred {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) (hlt : j < i)
    (hcp : isCausalPred τ j i = true) :
    level τ j + 1 ≤ level τ i := by
  -- Name the sup-function to avoid naming issues in calc.
  set f : {x // x ∈ Finset.range i} → Nat :=
    fun ⟨j', _⟩ => if isCausalPred τ j' i then 1 + level τ j' else 0
  with hf
  -- Use the unfolding equation for `level τ i` (only at i).
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

/-- **Antichain property.** Events at the same causal level form an
antichain: no causal edge connects two events at the same level.

This is a direct consequence of monotonicity: a causal edge `j → i`
forces `level τ j + 1 ≤ level τ i`, so they cannot be equal. -/
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

/-- Symmetric form of `no_causal_edge_within_level`: for *ordered* pairs
`j < i`, same-level implies no forward causal edge. The fully symmetric
version (covering both `isCausalPred τ j i` and `isCausalPred τ i j` for
arbitrary `j ≠ i`) requires a trajectory-structure lemma stating that
events can only consume expressions produced earlier in the trajectory,
which we haven't yet formalised; deferred. -/
theorem same_level_ordered_antichain {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) (hlt : j < i)
    (h_same_level : level τ j = level τ i) :
    isCausalPred τ j i = false :=
  no_causal_edge_within_level τ j i hlt h_same_level

/-- **Bridge lemma.** The `Prop`-level `causallyPrecedes` from `Causal.lean`
agrees with the `Bool`-level `isCausalPred` from this file. Specifically,
for indices in range, `causallyPrecedes τ i j ↔ isCausalPred τ i j = true`.

The argument-order convention matches: in both, the first index is the
causal predecessor, the second is the successor. -/
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
