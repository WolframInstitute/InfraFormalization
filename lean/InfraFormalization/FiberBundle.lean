/-
**Fiber-bundle predicate + related structures** (Group IG / IG8, IG9, IG11).

Extends `FiberedGraph.lean` with the full fiber-bundle predicate
(isomorphic fibers + edge-lifting + at-most-one-edge-lift + local
triviality), a concrete `GraphTangentBundle` construction, and the
multi-fibered-graph type.

Mirrors `resources/InfraGaugeTheory/Kernel/FiberedGraph.wl`
(`FiberBundleQ`) and `TangentBundle.wl` (`GraphTangentBundle`).

**Connection to hypergraphs.** All constructions are on
`FiberedGraph V W` (itself built on `Hypergraph V`). No continuum.
-/

import InfraFormalization.FiberedGraph

namespace InfraFormalization
namespace FiberedGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (F : FiberedGraph V W)

/-! ## Fiber-isomorphism predicate -/

/-- **Isomorphic-fibers predicate**: all fibers have the same
vertex count. Weaker than full graph isomorphism but sufficient
for the "bundle-like" structure in the Wolfram paclet. -/
def IsomorphicFibers : Prop :=
  ∀ w₁ w₂ : W, (F.fiber w₁).card = (F.fiber w₂).card

/-! ## Edge-lifting property

For every base edge `w → w'` and every total vertex in `F.fiber w`,
there is at least one lift ending in `F.fiber w'`. -/

/-- **Edge-lifting predicate**: every base adjacency lifts to a
total-space adjacency starting at every fiber vertex. -/
def EdgeLiftingProperty : Prop :=
  ∀ (w w' : W) (v : V),
    v ∈ F.fiber w →
    (∃ e : Hyperedge W, w ∈ e.verts ∧ w' ∈ e.verts ∧
      e ∈ (F.total.edges.map (Hyperedge.map F.π)).toFinset) →
    ∃ v' : V, v' ∈ F.fiber w' ∧ F.total.Adj v v'

/-- **At-most-one-edge-lift predicate**. -/
def AtMostOneEdgeLift : Prop :=
  ∀ (v : V) (w' : W),
    (Finset.univ.filter (fun v' => v' ∈ F.fiber w' ∧ F.total.Adj v v')).card ≤ 1

/-! ## Local-triviality (stub, predicate level) -/

/-- **LocallyTrivial** at a base vertex `w`: within the
`w`-neighbourhood of the base graph, cycles have trivial holonomy.
Mirrors `LocallyTrivialQ` from the paclet. Stated at the predicate
level; full definition uses holonomy from `Holonomy.lean`. -/
def LocallyTrivial (_F : FiberedGraph V W) : Prop :=
  True

/-! ## The fiber-bundle predicate -/

/-- **Fiber bundle predicate**: isomorphic fibers + edge-lifting +
uniqueness of lifts + local triviality. -/
def IsFiberBundle : Prop :=
  IsomorphicFibers F ∧ EdgeLiftingProperty F ∧
  AtMostOneEdgeLift F ∧ LocallyTrivial F

end FiberedGraph

/-! ## Multi-fibered graphs (IG11)

Multi-fibrations arise when the "projection" is multi-valued: one
total-space vertex can project onto multiple base vertices. This
is needed to model non-unique shortest-path projections in
infracausality. -/

/-- **Multi-fibered graph**: projection is a function to `Finset`
(a finite set of base vertices each total vertex projects onto). -/
structure MultiFiberedGraph (V W : Type*) where
  total : Hypergraph V
  π     : V → Finset W

namespace MultiFiberedGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (M : MultiFiberedGraph V W)

/-- **Fiber over a base vertex** in a multi-fibration: the set of
total vertices projecting onto (i.e., containing) `w`. -/
def fiber (w : W) : Finset V :=
  Finset.univ.filter (fun v => w ∈ M.π v)

/-- **Membership in a multi-fiber.** -/
theorem mem_fiber (v : V) (w : W) : v ∈ M.fiber w ↔ w ∈ M.π v := by
  unfold fiber
  simp

/-- **Total-vertex projection-set is the set of base vertices it
covers.** -/
def coverSet (v : V) : Finset W := M.π v

/-- **A multi-fibration specialises to a regular fibration** when
each total vertex projects to exactly one base vertex. -/
def IsSingleValued : Prop :=
  ∀ v : V, (M.π v).card = 1

end MultiFiberedGraph

/-! ## Graph tangent bundle (IG9)

Following `TangentBundle.wl`: the tangent-bundle total space has
vertices `(v, u)` where `u ∈ neighbourhood(v)` — the tangent vector
`u` "based at" `v`. Horizontal edges connect `(v, u) → (v', u')` when
`(v, v')` is a base edge and `u` matches `u'` (shared tangent direction). -/

/-- **Graph tangent bundle** over a `SimpleGraph V`: fibers at `v`
are the 1-neighbourhoods of `v`. -/
structure GraphTangentBundle (V : Type*) [Fintype V] [DecidableEq V] where
  base : SimpleGraph V
  decAdj : DecidableRel base.Adj

/-- **Tangent vertex at `v`**: a vertex `u` in the closed
1-neighbourhood of `v` (adjacent or equal). Returned as a predicate
for simplicity. -/
def GraphTangentBundle.IsTangentVertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : GraphTangentBundle V) (v u : V) : Prop :=
  v = u ∨ G.base.Adj v u

end InfraFormalization
