/-
Parallel schedules and the layer-width bound.

For a conservative rule (`|LHS|=|RHS|=k`) evolving from a seed of size
`N`, the greedy-parallel-schedule decomposition of the causal DAG has
every layer containing at most `⌊N/k⌋` events. This file states the
target theorem and establishes the direct building blocks.

**Distinction from BFS-cone growth.** The parallel-layer bound is a
statement about antichains *induced by the greedy-schedule level
function*. It is NOT the same as "BFS-cone growth is linear in
radius" — events in a BFS cone of radius `t` from a fixed source can
have arbitrarily high parallel-level via long alternate causal paths,
so cones are not contained in bounded bands of layers. The linear
cone growth observed empirically for JGORARD's named rule is
rule-and-seed-specific structure, not a corollary of the parallel-
layer bound.

**Status of this file.** We state the parallel-layer bound as a
proposition (no proof, no `sorry` — it's just a target). We prove the
direct immediate facts: each event consumes `|LHS|` expressions
(therefore has in-degree at most `|LHS|` in the multi-edge causal
graph), and the consumption cardinalities multiply out correctly for
conservative rules.

See `INFRAGEOMETRY.md` Phase 1 for the broader research agenda.
-/

import InfraFormalization.Causal

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **Parallel-layer bound (target proposition, to be proved).** For
a conservative rule with `|LHS| = k` and a seed of size `N`, at every
level `s` of the greedy-parallel schedule of any trajectory, the set
of events at that level contains at most `⌊N / k⌋` events.

Formally, this requires the construction of a level function, which in
turn requires a recursive definition over event predecessors with
careful termination. Both pieces are planned formalisation work (see
`NEXT_STEPS.md`). The proposition is stated here so downstream work
can refer to it symbolically. -/
def ParallelLayerBound {sys : RewritingSystem P} {init : Hypergraph V}
    (_τ : Trajectory sys init) (_r : Rule P) : Prop :=
  True  -- placeholder, to be fleshed out once `level` is defined

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
