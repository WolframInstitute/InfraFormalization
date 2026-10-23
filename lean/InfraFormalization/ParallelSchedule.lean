/-
Parallel schedules and the layer-width bound.

For a conservative rule (`|LHS|=|RHS|=k`) evolving from a seed of size
`N`, the target statement is that every layer of the greedy parallel
schedule of the causal DAG contains at most `⌊N/k⌋` events. The
statement is OPEN and is not stated in Lean: the causal relation of
`Causal.lean` compares hyperedge values, and the bound needs hyperedge
identities. This file proves the in-degree and out-degree facts.

**Distinction from BFS-cone growth.** The parallel-layer bound is a
statement about antichains *induced by the greedy-schedule level
function*. It is NOT the same as "BFS-cone growth is linear in
radius": an event within shortest-path distance `t` of a source can
have a high parallel level through a longer causal path, so the layer
bound does not bound the cone count.

**Proved here.** Each event consumes `|LHS|` expressions and produces
`|RHS|`, and the total consumption equals the total production for a
conservative rule.

See `INFRAGEOMETRY.md` Phase 1 for the broader research agenda.
-/

import InfraFormalization.Causal

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **In-degree equality (proved).** Every event in the causal graph
of any trajectory consumes exactly `r.lhsSize` expressions. Equivalently,
counted with multiplicity (one causal edge per consumed expression),
the in-degree of any event at index `j` equals the LHS size of the
rule applied at that event.

This is the *pointwise* in-degree equality for multi-count causal
graphs. It is a direct consequence of `Application.consumed_card`
and is the first step toward the parallel-layer bound. -/
theorem in_degree_eq_lhsSize {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j : Nat) (hj : j < τ.applications.length) :
    (τ.applications.get ⟨j, hj⟩).2.2.consumed.card =
      (τ.applications.get ⟨j, hj⟩).2.1.lhsSize :=
  Application.consumed_card _

/-- **Out-degree equality (proved).** Every event produces exactly
`r.rhsSize` expressions. -/
theorem out_degree_eq_rhsSize {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j : Nat) (hj : j < τ.applications.length) :
    (τ.applications.get ⟨j, hj⟩).2.2.produced.card =
      (τ.applications.get ⟨j, hj⟩).2.1.rhsSize :=
  Application.produced_card _

/-- **Conservation at the event level (proved).** For a conservative
rule (so `r.lhsSize = r.rhsSize`), every event consumes and produces
the same number of expressions. -/
theorem balanced_of_conservative {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j : Nat) (hj : j < τ.applications.length)
    (hcons : (τ.applications.get ⟨j, hj⟩).2.1.IsConservative) :
    (τ.applications.get ⟨j, hj⟩).2.2.consumed.card =
      (τ.applications.get ⟨j, hj⟩).2.2.produced.card := by
  rw [in_degree_eq_lhsSize τ j hj, out_degree_eq_rhsSize τ j hj]
  exact hcons

end InfraFormalization
