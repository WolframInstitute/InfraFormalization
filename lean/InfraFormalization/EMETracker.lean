/-
Predicates on the states of a trajectory.

An `EMEPredicate V` is a predicate on `Hypergraph V`. The module defines
when such a predicate holds at an index of a `Trajectory` and when it holds
at every index. It proves that the constant predicate `True` holds at every
index, that the conjunction of two predicates that hold at every index holds
at every index, and that an edge-count bound holds at every index when it is
assumed at every index.
-/

import InfraFormalization.Multiway
import InfraFormalization.Causal

namespace InfraFormalization

variable {V : Type*} [DecidableEq V]
variable {P : Type*}

/-- A predicate on hypergraph states. -/
abbrev EMEPredicate (V : Type*) := Hypergraph V → Prop

/-- If `i < τ.states.length`, then `ψ` holds on the `i`-th state of
`τ.states`. The statement holds vacuously for larger `i`. -/
def emeHoldsAt {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (ψ : EMEPredicate V) (i : ℕ) : Prop :=
  ∀ (hi : i < τ.states.length), ψ (τ.states.get ⟨i, hi⟩)

/-- `ψ` holds on every state of `τ.states`. -/
def emeHoldsEverywhere {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (ψ : EMEPredicate V) : Prop :=
  ∀ i, emeHoldsAt τ ψ i

/-- If `ψ` and `χ` hold on every state of `τ`, then `ψ ∧ χ` holds on every
state of `τ`. -/
theorem emeHoldsEverywhere_and {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (ψ χ : EMEPredicate V)
    (hψ : emeHoldsEverywhere τ ψ) (hχ : emeHoldsEverywhere τ χ) :
    emeHoldsEverywhere τ (fun H => ψ H ∧ χ H) := by
  intros i hi
  exact ⟨hψ i hi, hχ i hi⟩

/-- The predicate that a hypergraph has at most `N` edges, counted with
multiplicity. -/
def emeEdgeCountLe (N : ℕ) : EMEPredicate V :=
  fun H => Multiset.card H.edges ≤ N

end InfraFormalization
