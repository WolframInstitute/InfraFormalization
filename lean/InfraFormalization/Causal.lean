/-
Causal graph construction.

Given a trajectory — a finite list of applications, each applied to the
previous state — the causal graph is defined as follows: an event is a
single application; there is a directed edge from event `i` to event
`j > i` iff some hyperedge produced by `i` is consumed by `j`.

This file sketches the construction at the type level; exact
extraction-of-structure work is deferred to when it's needed downstream
(e.g. for the proof of `Growth.bounded_cone_of_conservative_CLAIM`).
-/

import InfraFormalization.Multiway
import InfraFormalization.Application

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- A finite trajectory: a list of applications where each is applied
to the state produced by its predecessor. -/
structure Trajectory (sys : RewritingSystem P) (init : Hypergraph V) where
  states : List (Hypergraph V)
  applications : List (Σ s : Hypergraph V, Σ r : Rule P, Application r s)
  length_eq : applications.length + 1 = states.length
  first_state : states.head? = some init
  well_formed : ∀ i (hi : i + 1 < states.length),
    (applications.get ⟨i, by omega⟩).2.2.result =
      states.get ⟨i + 1, hi⟩

/-- The causal relation between two events in a trajectory: `i ≺ j` iff
`i < j` and some hyperedge output by application `i` is consumed by
application `j`. -/
def causallyPrecedes {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i j : Nat) : Prop :=
  ∃ _ : i < j, ∃ hj : j < τ.applications.length,
    have hi : i < τ.applications.length := by omega
    let ai := τ.applications.get ⟨i, hi⟩
    let aj := τ.applications.get ⟨j, hj⟩
    ∃ e, e ∈ ai.2.2.produced ∧ e ∈ aj.2.2.consumed

/- **TODO.** The causal graph can then be defined as a simple graph on
`Fin τ.applications.length` with edge relation `i → j ↔ causallyPrecedes τ i j`.
Skipping the `SimpleGraph` instance here to keep the file
Mathlib-version-agnostic. -/

end InfraFormalization
