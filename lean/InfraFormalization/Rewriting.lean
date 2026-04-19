/-
Hypergraph pattern matching and rewriting rules.

Gorard's Def 3 (2004.14810) defines an update rule as `H₁ → H₂` replacing
a "subhypergraph" matching `H₁` with a copy of `H₂`, preserving (a) the
number of outgoing hyperedges and (b) the symmetries of `H₁`. Neither (a)
nor (b) is made precise in his prose.

We formalize rewriting via *matches* that are explicit injective maps from
pattern-edge indices into target edges, together with a vertex-binding
`ρ : P → V` from pattern-vertex type to target-vertex type. This replaces
"subhypergraph" (a vague notion) with a concrete morphism.

An update rule is a pair `(L, R)` of pattern hypergraphs over a shared
pattern-vertex type `P`, plus a designation of which `P`-vertices are
*bound* (must match to existing vertices of the target) versus *fresh*
(allocate new vertices in the target when the rule fires).
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Finset.Basic

namespace InfraFormalization

open Hypergraph

/-- A rewriting rule: pattern vertex type `P`, left and right pattern
hypergraphs, and a partition of `P` into bound vs. fresh vertices. -/
structure Rule (P : Type*) where
  lhs : Hypergraph P
  rhs : Hypergraph P
  /-- Pattern vertices that must match existing target vertices. Any
  `P`-vertex appearing in `lhs.vertexMultiset` is implicitly bound. -/
  boundVerts : Finset P
  /-- Compatibility: every vertex used by `lhs` is bound. -/
  bound_covers_lhs :
    ∀ p ∈ lhs.vertexMultiset, p ∈ boundVerts

/-- A match of a rule's LHS into a target hypergraph `H : Hypergraph V`:

* `ρ : P → V` — a binding of pattern vertices to target vertices. Must be
  injective on `boundVerts` (a matching move should not conflate two
  distinct pattern vertices into one target vertex — this is a precise
  replacement for the unspecified "preserve symmetries" clause in Def 3).
* `φ : Hyperedge P → Hyperedge V` — the induced map on hyperedges,
  determined by `ρ`.
* `witness` : every edge of `lhs` maps (under `φ`) to an actual edge of
  the target, with the chosen occurrences tracked via an explicit
  multiset-membership witness.
-/
structure Match {P V : Type*} (r : Rule P) (H : Hypergraph V) where
  ρ : P → V
  inj_on_bound : Set.InjOn ρ (r.boundVerts : Set P)
  witness : ∀ e ∈ r.lhs.edges,
    ⟨e.verts.map ρ, by
      intro h; cases e with
      | mk verts ne =>
        simp at h
        exact absurd (List.map_eq_nil.mp h) ne⟩ ∈ H.edges

/-- Apply a rule at a chosen match.

Fresh vertices (those in `rhs.vertexMultiset \ boundVerts`) need
allocation in `V`. We model this by abstracting the allocation as a
parameter `fresh : (P \ boundVerts) → V` with the requirement that its
image is disjoint from `ρ` on `boundVerts`. -/
structure Application {P V : Type*} (r : Rule P) (H : Hypergraph V) where
  m : Match r H
  freshBind : { p : P // p ∉ r.boundVerts } → V
  fresh_disjoint :
    ∀ (p : P) (hp : p ∉ r.boundVerts) (q : P) (hq : q ∈ r.boundVerts),
      freshBind ⟨p, hp⟩ ≠ m.ρ q

namespace Application

variable {P V : Type*} {r : Rule P} {H : Hypergraph V}

/-- The full binding `P → V` induced by a rule application. -/
def binding (a : Application r H) : P → V :=
  fun p =>
    if h : p ∈ r.boundVerts then a.m.ρ p
    else a.freshBind ⟨p, h⟩

/-- The result of firing `a`: remove the matched LHS edges and add the
image of RHS edges. -/
noncomputable def result [DecidableEq V] (a : Application r H) : Hypergraph V :=
  let removed : Multiset (Hyperedge V) :=
    r.lhs.edges.map (fun e =>
      { verts := e.verts.map a.binding,
        nonempty := by
          intro h
          rcases e with ⟨verts, ne⟩
          simp at h
          exact ne (List.map_eq_nil.mp h) })
  let added : Multiset (Hyperedge V) :=
    r.rhs.edges.map (fun e =>
      { verts := e.verts.map a.binding,
        nonempty := by
          intro h
          rcases e with ⟨verts, ne⟩
          simp at h
          exact ne (List.map_eq_nil.mp h) })
  ⟨(H.edges - removed) + added⟩

end Application

end InfraFormalization
