import Mathlib.Combinatorics.SimpleGraph.Walk
import InfraFormalization.HypergraphDistance

/-!
**Discrete connection on a hypergraph** (C7 / #40).

For a hypergraph `H : Hypergraph V` and a fiber-group type `G`, a discrete
connection assigns to each adjacency in `H` an element of `G` representing
parallel transport. This is the direct hypergraph analog of
`FiberedGraph.Connection` — instead of lifting edges to a total space, we
attach transport group-elements to the adjacencies of `H` itself.

This module is deliberately minimal: just the definition, the trivial flat
connection (all identities), symmetry lifted from group inverses, and
transport along a walk in the underlying `SimpleGraph`. More refined
structures (curvature 2-form, holonomy-preserving maps) are separate tasks.

**Research role**: C7 is the discrete object that, when scaled, should
converge to a Levi-Civita connection on the continuum bridge (C8 / #41).
-/

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

open Hypergraph

/-- **Discrete connection on a hypergraph.** Assigns to every adjacent
pair `(u, w)` in `H` an element of the fiber-group `G` representing
parallel transport `u → w`. No symmetry or composition axiom is imposed
at this level — those come from assumptions on `G` (e.g. `Group`) and
are added separately below. -/
structure HypergraphConnection (H : Hypergraph V) (G : Type*) where
  transport : ∀ {u w : V}, H.Adj u w → G

namespace HypergraphConnection

/-- **Flat (trivial) connection**: assigns the identity element of `G`
to every adjacency. Corresponds to "parallel transport = no rotation",
the canonical flat-background choice. -/
def flat (H : Hypergraph V) (G : Type*) [One G] : HypergraphConnection H G :=
  { transport := fun _ => 1 }

@[simp] theorem flat_transport (H : Hypergraph V) {G : Type*} [One G]
    {u w : V} (h : H.Adj u w) :
    (flat H G).transport h = 1 := rfl

/-- **Group-valued symmetric connection**: `transport w u = (transport u w)⁻¹`.
This is the discrete analog of the antisymmetry of a Levi-Civita
connection in its matrix form (inverse parallel transport in the
opposite direction). -/
def IsSymmetric {H : Hypergraph V} {G : Type*} [Group G]
    (C : HypergraphConnection H G) : Prop :=
  ∀ {u w : V} (h : H.Adj u w),
    C.transport (Hypergraph.Adj_symm h) = (C.transport h)⁻¹

/-- The flat connection is symmetric (inverse of identity is identity). -/
theorem flat_isSymmetric (H : Hypergraph V) (G : Type*) [Group G] :
    (flat H G).IsSymmetric := by
  intro u w h
  simp [flat]

/-- **Transport along a walk** in the underlying simple graph of `H`.
For a connection with values in a monoid, transport along a walk is
the product of the edge transports in order. The base case (nil walk)
is the identity; the inductive case composes with the next edge. -/
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

/-- **Flat transport is trivial along any walk.** For the flat connection
all transports are `1`, so the product is `1` regardless of walk
structure. This is the prototypical discrete-analog of "zero curvature
⇒ parallel transport is path-independent (trivially the identity)". -/
theorem flat_transportWalk_eq_one (H : Hypergraph V) (G : Type*) [Monoid G]
    {u v : V} (p : H.toSimpleGraph.Walk u v) :
    (flat H G).transportWalk p = 1 := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    rw [transportWalk_cons, flat_transport, one_mul]
    exact ih

/-- **Holonomy of a loop**: transport along a closed walk. For the flat
connection this is trivially `1`; in general it lives in `G` and
encodes the curvature through the loop. -/
def holonomy {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) {v : V}
    (p : H.toSimpleGraph.Walk v v) : G :=
  C.transportWalk p

/-- **Flat connection has trivial holonomy on every loop.** -/
theorem flat_holonomy_eq_one (H : Hypergraph V) (G : Type*) [Monoid G]
    {v : V} (p : H.toSimpleGraph.Walk v v) :
    (flat H G).holonomy p = 1 :=
  flat_transportWalk_eq_one H G p

/-- **A connection is *flat* when the holonomy of every loop is the
identity.** Discrete analog of vanishing curvature: transport depends
only on endpoints, not on the chosen walk between them. -/
def IsFlat {H : Hypergraph V} {G : Type*} [Monoid G]
    (C : HypergraphConnection H G) : Prop :=
  ∀ {v : V} (p : H.toSimpleGraph.Walk v v), C.holonomy p = 1

/-- **The flat connection is flat** (naming sanity check). -/
theorem flat_isFlat (H : Hypergraph V) (G : Type*) [Monoid G] :
    (flat H G).IsFlat := by
  intro v p
  exact flat_holonomy_eq_one H G p

/-- **Transport along concatenated walks is the product of transports**:
`transportWalk (p.append q) = transportWalk p * transportWalk q`. This is
the semigroup homomorphism property of parallel transport, a prerequisite
for holonomy to make sense as a group homomorphism from the fundamental
groupoid. -/
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
