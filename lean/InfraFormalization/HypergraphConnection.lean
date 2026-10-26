import Mathlib.Combinatorics.SimpleGraph.Walk
import InfraFormalization.HypergraphDistance

/-!
Discrete connections on a hypergraph.

A `HypergraphConnection H G` assigns an element of `G` to each adjacency `u ~ w` of `H`. The module defines the connection with all values `1`, the symmetry condition `transport w u = (transport u w)⁻¹`, transport along a walk in `H.toSimpleGraph` as the ordered product of edge values, holonomy of a closed walk, and flatness. It proves that transport is multiplicative under walk concatenation and that the constant-`1` connection is symmetric and has holonomy `1` on every closed walk. No continuum limit is stated.
-/

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

open Hypergraph

/-- A function assigning an element of `G` to each proof of `H.Adj u w`. No symmetry or composition condition is imposed. -/
structure HypergraphConnection (H : Hypergraph V) (G : Type*) where
  transport : ∀ {u w : V}, H.Adj u w → G

namespace HypergraphConnection

/-- The connection that assigns `1 : G` to every adjacency. -/
def flat (H : Hypergraph V) (G : Type*) [One G] : HypergraphConnection H G :=
  { transport := fun _ => 1 }

@[simp] theorem flat_transport (H : Hypergraph V) {G : Type*} [One G]
    {u w : V} (h : H.Adj u w) :
    (flat H G).transport h = 1 := rfl

/-- For a group `G`, `IsSymmetric C` holds when the value on `w ~ u` is the inverse of the value on `u ~ w` for every adjacency. -/
def IsSymmetric {H : Hypergraph V} {G : Type*} [Group G]
    (C : HypergraphConnection H G) : Prop :=
  ∀ {u w : V} (h : H.Adj u w),
    C.transport (Hypergraph.Adj_symm h) = (C.transport h)⁻¹

/-- `flat H G` is symmetric. -/
theorem flat_isSymmetric (H : Hypergraph V) (G : Type*) [Group G] :
    (flat H G).IsSymmetric := by
  intro u w h
  simp [flat]

/-- For a monoid `G`, the ordered product of the connection values along a walk in `H.toSimpleGraph`. The empty walk gives `1`. -/
def transportWalk {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) :
    ∀ {u v : V}, H.toSimpleGraph.Walk u v → G
  | _, _, SimpleGraph.Walk.nil => 1
  | _, _, SimpleGraph.Walk.cons h p => C.transport h * C.transportWalk p

@[simp] theorem transportWalk_nil {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) (v : V) :
    C.transportWalk (SimpleGraph.Walk.nil : H.toSimpleGraph.Walk v v) = 1 := rfl

@[simp] theorem transportWalk_cons {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) {u w v : V} (h : H.Adj u w)
    (p : H.toSimpleGraph.Walk w v) :
    C.transportWalk (SimpleGraph.Walk.cons h p) = C.transport h * C.transportWalk p := rfl

/-- Transport of `flat H G` along any walk is `1`. -/
theorem flat_transportWalk_eq_one (H : Hypergraph V) (G : Type*) [Monoid G]
    {u v : V} (p : H.toSimpleGraph.Walk u v) :
    (flat H G).transportWalk p = 1 := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    rw [transportWalk_cons, flat_transport, one_mul]
    exact ih

/-- Transport along a closed walk from `v` to `v`. -/
def holonomy {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) {v : V}
    (p : H.toSimpleGraph.Walk v v) : G :=
  C.transportWalk p

/-- The holonomy of `flat H G` on every closed walk is `1`. -/
theorem flat_holonomy_eq_one (H : Hypergraph V) (G : Type*) [Monoid G]
    {v : V} (p : H.toSimpleGraph.Walk v v) :
    (flat H G).holonomy p = 1 :=
  flat_transportWalk_eq_one H G p

/-- `IsFlat C` holds when the holonomy of every closed walk is `1`. -/
def IsFlat {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) : Prop :=
  ∀ {v : V} (p : H.toSimpleGraph.Walk v v), C.holonomy p = 1

/-- `flat H G` satisfies `IsFlat`. -/
theorem flat_isFlat (H : Hypergraph V) (G : Type*) [Monoid G] :
    (flat H G).IsFlat := by
  intro v p
  exact flat_holonomy_eq_one H G p

/-- `transportWalk (p.append q) = transportWalk p * transportWalk q`. -/
theorem transportWalk_append {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) : ∀ {u v w : V}
    (p : H.toSimpleGraph.Walk u v) (q : H.toSimpleGraph.Walk v w),
    C.transportWalk (p.append q) = C.transportWalk p * C.transportWalk q := by
  intro u v w p q
  induction p with
  | nil => simp [transportWalk]
  | cons h p' ih =>
    rw [SimpleGraph.Walk.cons_append, transportWalk_cons, transportWalk_cons]
    rw [ih, mul_assoc]

end HypergraphConnection

end InfraFormalization
