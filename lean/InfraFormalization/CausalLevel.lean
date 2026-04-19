/-
Total in-degree count for conservative-rule trajectories.

A step toward the parallel-layer bound (Theorem B). We prove that
summing the causal in-degree over all events equals `k * M` where
`k = |LHS|` and `M` is the total number of events — a direct
consequence of `in_degree_eq_lhsSize` (T5) but usefully packaged
as a summation lemma.

The full level / parallel-layer bound requires tracking the evolving
state, which is deferred.
-/

import InfraFormalization.ParallelSchedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **Total-in-degree theorem.** For a trajectory all of whose
applications use the same conservative rule `r`, the sum of the
consumed-edge cardinalities over all events is `M * r.lhsSize`,
where `M` is the number of events. Equivalently: the total causal
in-degree of the causal DAG (multi-count, excluding virtual seed) is
`k * M`. -/
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

end InfraFormalization
