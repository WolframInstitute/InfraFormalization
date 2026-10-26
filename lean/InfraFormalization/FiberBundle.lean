/-
Fiber-bundle predicates on fibered graphs.

This module defines, for a `FiberedGraph V W`, the predicates `IsomorphicFibers`,
`EdgeLiftingProperty`, `AtMostOneEdgeLift` and their
conjunction `IsFiberBundle`.
It also defines `MultiFiberedGraph`, whose projection sends each total vertex to a finite set of
base vertices, and `GraphTangentBundle`, a simple graph with decidable adjacency.
The definitions follow `FiberBundleQ` in `resources/InfraGaugeTheory/Kernel/FiberedGraph.wl` and
`GraphTangentBundle` in `TangentBundle.wl`.
-/

import InfraFormalization.FiberedGraph

namespace InfraFormalization
namespace FiberedGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (F : FiberedGraph V W)

/-! ## Fiber-isomorphism predicate -/

/-- All fibers have the same number of vertices. This is a cardinality condition, not a graph
isomorphism. -/
def IsomorphicFibers : Prop :=
  ∀ w₁ w₂ : W, (F.fiber w₁).card = (F.fiber w₂).card

/-! ## Edge-lifting property -/

/-- For all `w`, `w'` that lie in a common projected edge of the total space, every vertex `v` in
the fiber over `w` is adjacent in the total space to some vertex in the fiber over `w'`. -/
def EdgeLiftingProperty : Prop :=
  ∀ (w w' : W) (v : V),
    v ∈ F.fiber w →
    (∃ e : Hyperedge W, w ∈ e.verts ∧ w' ∈ e.verts ∧
      e ∈ (F.total.edges.map (Hyperedge.map F.π)).toFinset) →
    ∃ v' : V, v' ∈ F.fiber w' ∧ F.total.Adj v v'

/-- Every total vertex `v` is adjacent to at most one vertex in each fiber. -/
def AtMostOneEdgeLift : Prop :=
  ∀ (v : V) (w' : W),
    (Finset.univ.filter (fun v' => v' ∈ F.fiber w' ∧ F.total.Adj v v')).card ≤ 1


/-! ## The fiber-bundle predicate -/

/-- The conjunction of `IsomorphicFibers`, `EdgeLiftingProperty`, `AtMostOneEdgeLift` and
-/
def IsFiberBundle : Prop :=
  IsomorphicFibers F ∧ EdgeLiftingProperty F ∧
  AtMostOneEdgeLift F

end FiberedGraph

/-! ## Multi-fibered graphs -/

/-- A hypergraph `total` on `V` with a projection `π : V → Finset W` that assigns each total vertex
a finite set of base vertices. -/
structure MultiFiberedGraph (V W : Type*) where
  total : Hypergraph V
  π     : V → Finset W

namespace MultiFiberedGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (M : MultiFiberedGraph V W)

/-- The fiber over `w`: the total vertices `v` with `w ∈ M.π v`. -/
def fiber (w : W) : Finset V :=
  Finset.univ.filter (fun v => w ∈ M.π v)

/-- `v ∈ M.fiber w` if and only if `w ∈ M.π v`. -/
theorem mem_fiber (v : V) (w : W) : v ∈ M.fiber w ↔ w ∈ M.π v := by
  unfold fiber
  simp

/-- The set `M.π v` of base vertices assigned to `v`. -/
def coverSet (v : V) : Finset W := M.π v

/-- Every total vertex is assigned exactly one base vertex. -/
def IsSingleValued : Prop :=
  ∀ v : V, (M.π v).card = 1

end MultiFiberedGraph

/-! ## Graph tangent bundle -/

/-- A simple graph `base` on `V` together with a decidability instance for its adjacency
relation. -/
structure GraphTangentBundle (V : Type*) [Fintype V] [DecidableEq V] where
  base : SimpleGraph V
  decAdj : DecidableRel base.Adj

/-- `u` lies in the closed neighbourhood of `v`: `v = u` or `v` is adjacent to `u`. -/
def GraphTangentBundle.IsTangentVertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : GraphTangentBundle V) (v u : V) : Prop :=
  v = u ∨ G.base.Adj v u

end InfraFormalization
