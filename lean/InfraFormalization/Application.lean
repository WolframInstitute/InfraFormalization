/-
Application of a rewriting rule to a hypergraph.

An application of a rule `r : Rule P` to a hypergraph `H : Hypergraph V` is
a binding `ρ : P → V` such that the image of the left-hand side under `ρ` is
a sub-multiset of `H.edges`. The structure imposes no freshness condition on
the images of right-hand-side-only vertices. The result replaces the image of
the left-hand side with the image of the right-hand side. `NamedRule.lean`
gives a computable version on `V = Nat` with fresh-vertex allocation.
-/

import InfraFormalization.Rule

namespace InfraFormalization

open Hypergraph

/-- An application of rule `r` at hypergraph `H`: a binding `ρ` under which
the left-hand side is a sub-multiset of `H.edges`. -/
structure Application {P V : Type*} (r : Rule P) (H : Hypergraph V) where
  ρ : P → V
  lhs_embedded : (r.lhs.edges.map (Hyperedge.map ρ)) ≤ H.edges

namespace Application

variable {P V : Type*} {r : Rule P} {H : Hypergraph V}

/-- The hyperedges consumed by this application. -/
def consumed (a : Application r H) : Multiset (Hyperedge V) :=
  r.lhs.edges.map (Hyperedge.map a.ρ)

/-- The hyperedges produced by this application. -/
def produced (a : Application r H) : Multiset (Hyperedge V) :=
  r.rhs.edges.map (Hyperedge.map a.ρ)

/-- The result hypergraph `(H.edges - consumed) + produced`. -/
def result [DecidableEq V] (a : Application r H) : Hypergraph V :=
  ⟨(H.edges - a.consumed) + a.produced⟩

@[simp] theorem consumed_card (a : Application r H) :
    a.consumed.card = r.lhsSize := by
  simp [consumed, Rule.lhsSize, Hypergraph.size]

@[simp] theorem produced_card (a : Application r H) :
    a.produced.card = r.rhsSize := by
  simp [produced, Rule.rhsSize, Hypergraph.size]

end Application

end InfraFormalization
