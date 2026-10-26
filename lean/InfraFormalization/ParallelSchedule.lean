/-
Edge counts of events in a trajectory.

For a conservative rule (`|LHS| = |RHS| = k`) evolving from a state with `N` edges, the conjectured
bound is that every layer of the greedy parallel schedule of the causal graph contains at most
`⌊N/k⌋` events. This bound is not stated in Lean, because the causal relation of `Causal.lean`
compares hyperedge values and the bound requires hyperedge identities. The layer bound concerns
antichains given by the schedule level and does not bound the number of events within a given
causal distance of a source. This module proves that each event consumes `|LHS|` edges and produces
`|RHS|` edges, and that for a conservative rule the two numbers are equal. `INFRAGEOMETRY.md`,
Phase 1, describes the conjecture.
-/

import InfraFormalization.Causal

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- The `j`-th application of a trajectory consumes `lhsSize` edges of its rule. -/
theorem in_degree_eq_lhsSize {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j : Nat) (hj : j < τ.applications.length) :
    (τ.applications.get ⟨j, hj⟩).2.2.consumed.card =
      (τ.applications.get ⟨j, hj⟩).2.1.lhsSize :=
  Application.consumed_card _

/-- The `j`-th application of a trajectory produces `rhsSize` edges of its rule. -/
theorem out_degree_eq_rhsSize {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j : Nat) (hj : j < τ.applications.length) :
    (τ.applications.get ⟨j, hj⟩).2.2.produced.card =
      (τ.applications.get ⟨j, hj⟩).2.1.rhsSize :=
  Application.produced_card _

/-- If the rule of the `j`-th application is conservative, the application consumes and produces the
same number of edges. -/
theorem balanced_of_conservative {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j : Nat) (hj : j < τ.applications.length)
    (hcons : (τ.applications.get ⟨j, hj⟩).2.1.IsConservative) :
    (τ.applications.get ⟨j, hj⟩).2.2.consumed.card =
      (τ.applications.get ⟨j, hj⟩).2.2.produced.card := by
  rw [in_degree_eq_lhsSize τ j hj, out_degree_eq_rhsSize τ j hj]
  exact hcons

end InfraFormalization
