/-
Trajectories and a value-based causal relation.

`causallyPrecedes τ i j` holds when `i < j` and some hyperedge value
produced by application `i` is consumed by application `j`. When a state
holds two equal hyperedges, this relation differs from the causal graph
of the evolution. `CausalHistory.lean` defines the causal graph on
hyperedge identities.
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

end InfraFormalization
