/-
Directed (multi-)hypergraphs as used in the Wolfram model.

A `Hypergraph V` is a finite multiset of directed hyperedges, where each
hyperedge is a nonempty ordered tuple of vertices from `V`. We use
ordered tuples (not unordered subsets) because:

  * Gorard's later machinery (the Ollivier-Ricci construction in §3.1 of
    arXiv:2004.14810 and in arXiv:2102.09363 §5) requires a notion of
    "tail" and "head" of an edge, i.e. direction;
  * "outgoing hyperedges" (Def 3, arXiv:2004.14810) is only well-defined
    when edges carry an order;
  * every rule actually written down in the Wolfram Physics Project
    corpus is expressed with ordered edges.

This file is intentionally light on Mathlib dependencies. We re-use
`List` and `Multiset` from core/Mathlib so that downstream modules can
compose these hypergraphs with Mathlib's metric / measure / topology
infrastructure.
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

namespace InfraFormalization

/-- A directed hyperedge on vertex type `V` is a nonempty ordered tuple. -/
structure Hyperedge (V : Type*) where
  verts : List V
  nonempty : verts ≠ []
deriving DecidableEq

namespace Hyperedge

variable {V : Type*}

/-- The arity (number of vertex slots, with multiplicity). -/
@[simp] def arity (e : Hyperedge V) : Nat := e.verts.length

/-- The multiset of vertices incident to this hyperedge. -/
def incident (e : Hyperedge V) : Multiset V := ↑e.verts

/-- The first vertex; always exists because `verts ≠ []`. -/
def head! (e : Hyperedge V) : V :=
  e.verts.head e.nonempty

/-- Apply a vertex relabeling to a hyperedge. -/
def map {W : Type*} (f : V → W) (e : Hyperedge V) : Hyperedge W where
  verts := e.verts.map f
  nonempty := by
    intro h
    have := List.map_eq_nil_iff.mp h
    exact e.nonempty this

@[simp] theorem arity_map {W : Type*} (f : V → W) (e : Hyperedge V) :
    (e.map f).arity = e.arity := by
  simp [map, arity]

end Hyperedge

/-- A (directed, multi-) hypergraph on `V`: a finite multiset of
directed hyperedges. -/
structure Hypergraph (V : Type*) where
  edges : Multiset (Hyperedge V)

namespace Hypergraph

variable {V : Type*}

/-- The empty hypergraph. -/
@[simp] def empty : Hypergraph V := ⟨0⟩

/-- Number of (multiset-counted) edges. -/
@[simp] def size (H : Hypergraph V) : Nat := H.edges.card

@[simp] theorem size_empty : (empty : Hypergraph V).size = 0 := rfl

/-- Insert a single edge. -/
def cons (e : Hyperedge V) (H : Hypergraph V) : Hypergraph V :=
  ⟨e ::ₘ H.edges⟩

@[simp] theorem size_cons (e : Hyperedge V) (H : Hypergraph V) :
    (H.cons e).size = H.size + 1 := by
  simp [cons, size]

/-- Union of two hypergraphs (additive on multisets). -/
def union (H₁ H₂ : Hypergraph V) : Hypergraph V :=
  ⟨H₁.edges + H₂.edges⟩

instance : Add (Hypergraph V) := ⟨union⟩

@[simp] theorem size_add (H₁ H₂ : Hypergraph V) :
    (H₁ + H₂).size = H₁.size + H₂.size := by
  show (H₁.edges + H₂.edges).card = _
  simp [size]

/-- Remove a submultiset of edges. Mathlib's `Multiset.sub` is
truncated subtraction; to get exact conservation laws we'll prove
lemmas that guarantee the submultiset assumption. Needs `DecidableEq`
on the edges (which follows from `DecidableEq V`). -/
def diff [DecidableEq V] (H : Hypergraph V) (E : Multiset (Hyperedge V)) : Hypergraph V :=
  ⟨H.edges - E⟩

/-- **Empty is a right unit for union.** -/
@[simp] theorem add_empty (H : Hypergraph V) : H + empty = H := by
  show ⟨H.edges + (0 : Multiset (Hyperedge V))⟩ = H
  simp

/-- **Empty is a left unit for union.** -/
@[simp] theorem empty_add (H : Hypergraph V) : empty + H = H := by
  show ⟨(0 : Multiset (Hyperedge V)) + H.edges⟩ = H
  simp

/-- **Union is commutative.** Inherited from multiset addition. -/
theorem add_comm' (H₁ H₂ : Hypergraph V) : H₁ + H₂ = H₂ + H₁ := by
  show (⟨H₁.edges + H₂.edges⟩ : Hypergraph V)
    = (⟨H₂.edges + H₁.edges⟩ : Hypergraph V)
  congr 1
  exact Multiset.add_comm _ _

/-- **Union is associative.** Inherited from multiset addition. -/
theorem add_assoc' (H₁ H₂ H₃ : Hypergraph V) :
    H₁ + H₂ + H₃ = H₁ + (H₂ + H₃) := by
  show (⟨H₁.edges + H₂.edges + H₃.edges⟩ : Hypergraph V)
    = (⟨H₁.edges + (H₂.edges + H₃.edges)⟩ : Hypergraph V)
  congr 1
  exact Multiset.add_assoc _ _ _

/-- **Diff reduces size**: removing edges can only decrease (or
preserve) the size. Mathlib's truncated `Multiset.sub` gives the
inequality unconditionally. -/
theorem size_diff_le [DecidableEq V] (H : Hypergraph V)
    (E : Multiset (Hyperedge V)) :
    (H.diff E).size ≤ H.size := by
  show (H.edges - E).card ≤ H.edges.card
  exact Multiset.card_le_card (Multiset.sub_le_self H.edges E)

/-- **Empty has size 0** — an alternate phrasing of `size_empty`. -/
theorem size_eq_zero_of_empty (H : Hypergraph V)
    (hH : H = (empty : Hypergraph V)) : H.size = 0 := by
  rw [hH]; exact size_empty

/-- **`H.size = 0 ↔ H = empty`.** A multiset has cardinality 0 iff it
is the zero multiset; lift this to hypergraphs via the edge-multiset
wrapping. -/
theorem size_eq_zero_iff_empty (H : Hypergraph V) :
    H.size = 0 ↔ H = (empty : Hypergraph V) := by
  constructor
  · intro hsize
    show (⟨H.edges⟩ : Hypergraph V) = ⟨0⟩
    congr 1
    exact Multiset.card_eq_zero.mp hsize
  · intro hempty
    rw [hempty]; exact size_empty

/-- **`cons` strictly increases size**, so never yields empty. -/
theorem cons_ne_empty (e : Hyperedge V) (H : Hypergraph V) :
    H.cons e ≠ empty := by
  intro h
  have : (H.cons e).size = 0 := by rw [h]; exact size_empty
  rw [size_cons] at this
  omega

end Hypergraph

end InfraFormalization
