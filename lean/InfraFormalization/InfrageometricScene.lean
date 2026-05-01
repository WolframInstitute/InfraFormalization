/-
**Multi-construction scenes on hypergraphs** (Group IS / #157).

From PHAJEK's Srní/Madrid talks: an *infrageometric scene* is
an ensemble of synthetic geometric constructions over a common
base hypergraph, with the Hausdorff distance between construction
instances defining a branchial structure on scenes.

  * A scene is a finset of `Finset V` (the set of constructed
    objects, each a subset of vertices).
  * The Hausdorff distance between two such subsets gives a metric
    on the scene set.
  * Ensembles of scenes form a branchial graph — one scene per
    multiway branch of the underlying construction process.

This file gives the basic type + Hausdorff-distance predicate. The
branchial structure and hypergraph-rewriting coupling are IS3 and
follow-up.

**Connection to hypergraphs.** Native: a scene is literally a
`Finset (Finset V)`.
-/

import InfraFormalization.SyntheticGeometry
import InfraFormalization.HypergraphDistance

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Infrageometric scene** over a hypergraph: a finset of
constructed objects (each a subset of vertices). -/
structure InfrageometricScene (V : Type*) [Fintype V] [DecidableEq V] where
  objects : Finset (Finset V)

namespace InfrageometricScene

variable (S : InfrageometricScene V)

/-- **Empty scene.** -/
def empty : InfrageometricScene V := ⟨∅⟩

/-- **Add an object to a scene.** -/
def addObject (obj : Finset V) : InfrageometricScene V :=
  ⟨insert obj S.objects⟩

@[simp] theorem empty_objects : (empty : InfrageometricScene V).objects = ∅ := rfl

@[simp] theorem addObject_objects (obj : Finset V) :
    (S.addObject obj).objects = insert obj S.objects := rfl

/-- **Scene cardinality**: the number of distinct constructed objects. -/
def card : Nat := S.objects.card

@[simp] theorem empty_card : (empty : InfrageometricScene V).card = 0 := by
  simp [card, empty]

end InfrageometricScene

/-! ## Hausdorff distance (stub) between two scene-objects. -/

/-- **Directed Hausdorff "distance"** between two vertex-subsets under
the hypergraph distance: `sup_{u ∈ A} inf_{v ∈ B} dist H u v`.
Implemented as a `Nat` for the discrete-distance setting; returns
`0` when either set is empty. -/
noncomputable def directedHausdorff (H : Hypergraph V) (A B : Finset V) : Nat :=
  A.sup (fun u =>
    (B.image (fun v => H.dist u v)).min.getD 0)

/-- **Symmetric Hausdorff distance**: max of the two directed
directions. Metric on scene-objects under `Hypergraph.dist`. -/
noncomputable def sceneHausdorff (H : Hypergraph V) (A B : Finset V) : Nat :=
  max (directedHausdorff H A B) (directedHausdorff H B A)

end Hypergraph
end InfraFormalization
