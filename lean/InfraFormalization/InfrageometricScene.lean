/-
Infrageometric scenes.

Following P. Hajek's Srní and Madrid talks, a scene is a finite set of constructed objects over a
base hypergraph, each object a set of vertices. This module defines the scene type, the empty scene,
insertion of an object, the number of objects, and the directed and symmetric Hausdorff distances
between two vertex sets under `Hypergraph.dist`.
-/

import InfraFormalization.SyntheticGeometry
import InfraFormalization.HypergraphDistance

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite set of constructed objects, each a finite set of vertices. -/
structure InfrageometricScene (V : Type*) [Fintype V] [DecidableEq V] where
  objects : Finset (Finset V)

namespace InfrageometricScene

variable (S : InfrageometricScene V)

/-- The scene with no objects. -/
def empty : InfrageometricScene V := ⟨∅⟩

/-- The scene with `obj` inserted into its set of objects. -/
def addObject (obj : Finset V) : InfrageometricScene V :=
  ⟨insert obj S.objects⟩

@[simp] theorem empty_objects : (empty : InfrageometricScene V).objects = ∅ := rfl

@[simp] theorem addObject_objects (obj : Finset V) :
    (S.addObject obj).objects = insert obj S.objects := rfl

/-- The number of distinct objects in the scene. -/
def card : Nat := S.objects.card

@[simp] theorem empty_card : (empty : InfrageometricScene V).card = 0 := by
  simp [card, empty]

end InfrageometricScene

/-! ## Hausdorff distance between two vertex sets -/

/-- The directed Hausdorff distance `max_{u ∈ A} min_{v ∈ B} dist H u v` as a natural number. It
is 0 when `A` or `B` is empty. -/
noncomputable def directedHausdorff (H : Hypergraph V) (A B : Finset V) : Nat :=
  A.sup (fun u =>
    (B.image (fun v => H.dist u v)).min.getD 0)

/-- The maximum of `directedHausdorff H A B` and `directedHausdorff H B A`. -/
noncomputable def sceneHausdorff (H : Hypergraph V) (A B : Finset V) : Nat :=
  max (directedHausdorff H A B) (directedHausdorff H B A)

end Hypergraph
end InfraFormalization
