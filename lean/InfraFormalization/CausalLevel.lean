/-
Causal-DAG level function and related bounds.

This file defines the *causal level* of a trajectory event — the length
of the longest chain of causal-predecessor edges leading to it — and
proves basic structural theorems.

The long-term goal (parallel-layer bound: each level of a conservative
rule's trajectory contains at most `⌊N/k⌋` events) requires tracking
the state at each level, which is a substantial formalisation. This
file establishes what's directly provable without that: the total
in-degree, total out-degree, and the existence of the level function
via classical well-founded recursion.
-/

import InfraFormalization.ParallelSchedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **Total-in-degree theorem.** For a trajectory all of whose
applications use the same conservative rule `r`, the sum of the
consumed-edge cardinalities over all events is `M * r.lhsSize`, where
`M` is the number of events. -/
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

/-- **Total-out-degree theorem.** Same statement for produced edges:
sum of produced-cardinalities is `M * r.rhsSize`. -/
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

/-- **Balance (sum).** For a conservative rule, the total in-degree
and total out-degree of the causal DAG are equal. -/
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

/-- **Causal level** of an event. Defined by strong recursion on the
Nat index: the level of an event `i` is `1 + max over predecessors`,
or `0` if no predecessor exists. Predecessor relation uses `j < i`
and "causal edge j → i" (some expression produced by `j` is consumed
by `i`).

Uses `Classical.dec` at the outermost `Decidable` inference for the
existential quantifier over hyperedges. -/
noncomputable def level {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) : Nat → Nat := fun i =>
  Nat.strongRecOn (motive := fun _ => Nat) i fun n rec =>
    (Finset.range n).attach.sup fun ⟨j, hj⟩ =>
      if h : j < τ.applications.length ∧ n < τ.applications.length then
        let _ : Decidable (∃ e : Hyperedge V,
          e ∈ (τ.applications.get ⟨j, h.1⟩).2.2.produced ∧
          e ∈ (τ.applications.get ⟨n, h.2⟩).2.2.consumed) := Classical.propDecidable _
        if ∃ e : Hyperedge V,
             e ∈ (τ.applications.get ⟨j, h.1⟩).2.2.produced ∧
             e ∈ (τ.applications.get ⟨n, h.2⟩).2.2.consumed then
          1 + rec j (Finset.mem_range.mp hj)
        else 0
      else 0

/-! **Level monotonicity (deferred).** The natural next theorem is:
if `j` causally precedes `i` then `level τ j + 1 ≤ level τ i`. The
proof idea is that `j` appears in `(Finset.range i).attach` and the
step function evaluates at `⟨j, _⟩` to exactly `1 + level τ j`. The
full calc-step proof is brittle against `Nat.strongRecOn`'s
simp-unfolding behaviour; we defer it to a focused iteration where
we introduce an auxiliary `level_step` function with an explicit
simp lemma for its evaluation. -/

end InfraFormalization
