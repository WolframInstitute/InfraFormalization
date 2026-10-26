/-
Directed multi-hypergraphs as used in the Wolfram model.

A `Hyperedge V` is a nonempty ordered list of vertices, and a `Hypergraph V` is a finite multiset of hyperedges. Hyperedges are ordered because the outgoing hyperedges of Def. 3 in G1 (arXiv:2004.14810) require an order on each edge, and the rules of the Wolfram Physics Project are written with ordered edges. The module defines size, insertion, union and multiset difference, and proves the basic identities and size bounds for them.
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

/-- The first vertex, which exists because `verts ≠ []`. -/
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

/-- A directed multi-hypergraph on `V`: a finite multiset of hyperedges. -/
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

/-- Remove the edges of `E` from `H` by `Multiset.sub`, which is truncated subtraction. Requires `DecidableEq V`. -/
def diff [DecidableEq V] (H : Hypergraph V) (E : Multiset (Hyperedge V)) : Hypergraph V :=
  ⟨H.edges - E⟩

/-- `H + empty = H`. -/
@[simp] theorem add_empty (H : Hypergraph V) : H + empty = H := by
  show ⟨H.edges + (0 : Multiset (Hyperedge V))⟩ = H
  simp

/-- `empty + H = H`. -/
@[simp] theorem empty_add (H : Hypergraph V) : empty + H = H := by
  show ⟨(0 : Multiset (Hyperedge V)) + H.edges⟩ = H
  simp

/-- Union is commutative. -/
theorem add_comm' (H₁ H₂ : Hypergraph V) : H₁ + H₂ = H₂ + H₁ := by
  show (⟨H₁.edges + H₂.edges⟩ : Hypergraph V)
    = (⟨H₂.edges + H₁.edges⟩ : Hypergraph V)
  congr 1
  exact Multiset.add_comm _ _

/-- Union is associative. -/
theorem add_assoc' (H₁ H₂ H₃ : Hypergraph V) :
    H₁ + H₂ + H₃ = H₁ + (H₂ + H₃) := by
  show (⟨H₁.edges + H₂.edges + H₃.edges⟩ : Hypergraph V)
    = (⟨H₁.edges + (H₂.edges + H₃.edges)⟩ : Hypergraph V)
  congr 1
  exact Multiset.add_assoc _ _ _

/-- `(H.diff E).size ≤ H.size` for every `E`. -/
theorem size_diff_le [DecidableEq V] (H : Hypergraph V)
    (E : Multiset (Hyperedge V)) :
    (H.diff E).size ≤ H.size := by
  show (H.edges - E).card ≤ H.edges.card
  exact Multiset.card_le_card (Multiset.sub_le_self H.edges E)

/-- If `H = empty` then `H.size = 0`. -/
theorem size_eq_zero_of_empty (H : Hypergraph V)
    (hH : H = (empty : Hypergraph V)) : H.size = 0 := by
  rw [hH]; exact size_empty

/-- `H.size = 0 ↔ H = empty`. -/
theorem size_eq_zero_iff_empty (H : Hypergraph V) :
    H.size = 0 ↔ H = (empty : Hypergraph V) := by
  constructor
  · intro hsize
    show (⟨H.edges⟩ : Hypergraph V) = ⟨0⟩
    congr 1
    exact Multiset.card_eq_zero.mp hsize
  · intro hempty
    rw [hempty]; exact size_empty

/-- `H.cons e ≠ empty`. -/
theorem cons_ne_empty (e : Hyperedge V) (H : Hypergraph V) :
    H.cons e ≠ empty := by
  intro h
  have : (H.cons e).size = 0 := by rw [h]; exact size_empty
  rw [size_cons] at this
  omega

/-- `(H₁ + H₂).cons e = H₁.cons e + H₂`. -/
theorem cons_add (e : Hyperedge V) (H₁ H₂ : Hypergraph V) :
    (H₁ + H₂).cons e = H₁.cons e + H₂ := by
  show (⟨e ::ₘ (H₁.edges + H₂.edges)⟩ : Hypergraph V)
    = ⟨(e ::ₘ H₁.edges) + H₂.edges⟩
  congr 1
  exact (Multiset.cons_add e H₁.edges H₂.edges).symm

/-- `H.size < (H.cons e).size`. -/
theorem size_lt_cons (e : Hyperedge V) (H : Hypergraph V) :
    H.size < (H.cons e).size := by
  rw [size_cons]; omega

/-- `H₁.size ≤ (H₁ + H₂).size`. -/
theorem size_le_add_right (H₁ H₂ : Hypergraph V) :
    H₁.size ≤ (H₁ + H₂).size := by
  rw [size_add]; omega

/-- `H₂.size ≤ (H₁ + H₂).size`. -/
theorem size_le_add_left (H₁ H₂ : Hypergraph V) :
    H₂.size ≤ (H₁ + H₂).size := by
  rw [size_add]; omega

/-- If `H ≠ empty` then `0 < H.size`. -/
theorem size_pos_of_ne_empty (H : Hypergraph V) (hne : H ≠ empty) :
    0 < H.size := by
  rcases Nat.eq_zero_or_pos H.size with hz | hpos
  · exact absurd ((size_eq_zero_iff_empty H).mp hz) hne
  · exact hpos

end Hypergraph

end InfraFormalization
