/-
Application of a rewriting rule to a hypergraph.

A rule `r : Rule P` fires on a target hypergraph `H : Hypergraph V`
through an **application**, which consists of:

  * a binding `ρ : P → V` (pattern-to-target vertex map) such that the
    image `r.lhs.map ρ` is a sub-multiset of `H.edges`;
  * freshness of any `ρ p` for `p ∉ r.lhs.vertexFinset` (strictly
    speaking, for `p` in the *difference* between RHS and LHS vertex
    sets).

The result of firing: replace `r.lhs.map ρ` in `H` with `r.rhs.map ρ`.

We provide an abstract / non-computable version here. The computable
version (with explicit fresh-vertex allocation) is in
`NamedRule.lean` specialized to `V = Nat`.
-/

import InfraFormalization.Rule

namespace InfraFormalization

open Hypergraph

/-- An application of rule `r` at hypergraph `H` with binding `ρ`.

The key invariant is `lhs_embedded`: the LHS pattern, under the
binding, appears as a sub-multiset of `H.edges`. Mathlib's `Multiset.Le`
gives us submultiset membership. -/
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

/-- The result hypergraph. Needs `DecidableEq V` for multiset
subtraction. -/
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
