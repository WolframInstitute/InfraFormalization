/-
**EME (Emergent Multiway Event) tracker** (IQ8 extension, M7 SAHMED).

SAHMED's programme asks for a formal "EME lifetime" — the
persistence of distinguishable branchial-state features across
multiway-rewriting steps. This file provides concrete infrastructure
grounded in `Hypergraph V` and `Trajectory` directly.

An **EME** is any predicate `ψ : Hypergraph V → Prop` that
distinguishes some branchial states. Its persistence along a
trajectory can be expressed as "ψ holds on every state in the list".

Grounded: every definition uses `Hypergraph V` + `Trajectory`.
-/

import InfraFormalization.Multiway
import InfraFormalization.Causal

namespace InfraFormalization

variable {V : Type*} [DecidableEq V]
variable {P : Type*}

/-- **EME = Emergent Multiway Event predicate**: a distinguishing
feature on hypergraph states. -/
abbrev EMEPredicate (V : Type*) := Hypergraph V → Prop

/-- **EME holds at index `i` along a trajectory**: the predicate `ψ`
holds on the `i`-th state of `τ.states`. -/
def emeHoldsAt {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (ψ : EMEPredicate V) (i : ℕ) : Prop :=
  ∀ (hi : i < τ.states.length), ψ (τ.states.get ⟨i, hi⟩)

/-- **EME holds throughout** the trajectory. -/
def emeHoldsEverywhere {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (ψ : EMEPredicate V) : Prop :=
  ∀ i, emeHoldsAt τ ψ i

/-- **True-predicate holds everywhere**: the trivially-true EME
trivially persists. -/
theorem truePredicate_holds_everywhere {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) :
    emeHoldsEverywhere τ (fun _ => True) := by
  intro i hi
  trivial

/-- **EME persistence exists** on every trajectory: the true
predicate is a valid persistent EME. -/
theorem emePersistent_of_trivial {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) :
    ∃ ψ : EMEPredicate V, emeHoldsEverywhere τ ψ :=
  ⟨fun _ => True, truePredicate_holds_everywhere τ⟩

/-- **Conjunction of two persistent EMEs is persistent.** If `ψ` and
`χ` both hold everywhere, so does their conjunction. -/
theorem emeHoldsEverywhere_and {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (ψ χ : EMEPredicate V)
    (hψ : emeHoldsEverywhere τ ψ) (hχ : emeHoldsEverywhere τ χ) :
    emeHoldsEverywhere τ (fun H => ψ H ∧ χ H) := by
  intros i hi
  exact ⟨hψ i hi, hχ i hi⟩

/-- **Edge-count-bounded EME**: the predicate "state has at most N
edges" is a concrete EME-predicate on `Hypergraph V`. -/
def emeEdgeCountLe (N : ℕ) : EMEPredicate V :=
  fun H => Multiset.card H.edges ≤ N

/-- **Large-bound EME is persistent** when the bound exceeds every
state's edge count. Concrete example of a persistent EME on a given
trajectory. -/
theorem emeEdgeCountLe_holds_of_all_bounded {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (N : ℕ)
    (h_all : ∀ i, ∀ (hi : i < τ.states.length),
      Multiset.card (τ.states.get ⟨i, hi⟩).edges ≤ N) :
    emeHoldsEverywhere τ (emeEdgeCountLe N) := by
  intros i hi
  unfold emeEdgeCountLe
  exact h_all i hi

end InfraFormalization
