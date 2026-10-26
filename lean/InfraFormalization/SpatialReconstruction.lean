/-
Spatial adjacency from a causal graph.

Two events are adjacent in a slice if both lie in the slice, are distinct,
and have a common immediate causal predecessor. This module defines the
common-predecessor relation, proves that it is symmetric, defines the
adjacency predicate on a slice `Finset V`, and defines the two-vertex
hyperedge `[u, v]`. It does not construct the hypergraph of a slice.
-/

import InfraFormalization.CausalGraphType
import InfraFormalization.CausalFoliation

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-- `a` is an immediate common ancestor of `u` and `v`:
`G.causalEdge a u` and `G.causalEdge a v`. -/
def ImmediateCommonAncestor (u v : V) (a : V) : Prop :=
  G.causalEdge a u ∧ G.causalEdge a v

/-- Some event is an immediate common ancestor of `u` and `v`. -/
def ShareImmediateAncestor (u v : V) : Prop :=
  ∃ a : V, G.ImmediateCommonAncestor u v a

/-- `ShareImmediateAncestor` is symmetric. -/
theorem ShareImmediateAncestor.symm {u v : V}
    (h : G.ShareImmediateAncestor u v) : G.ShareImmediateAncestor v u := by
  obtain ⟨a, hau, hav⟩ := h
  exact ⟨a, hav, hau⟩

/-- `u ≠ v` and `u`, `v` have an immediate common ancestor. -/
def ShareImmediateAncestorNontrivial (u v : V) : Prop :=
  u ≠ v ∧ G.ShareImmediateAncestor u v

/-- `u` and `v` lie in `slice`, are distinct, and have an immediate common
ancestor. -/
def spatialReconstructionAdj (slice : Finset V) (u v : V) : Prop :=
  u ∈ slice ∧ v ∈ slice ∧ G.ShareImmediateAncestorNontrivial u v

/-- The hyperedge with vertex list `[u, v]`. It is defined for every pair
and does not depend on `G`. -/
def spatialHyperedgeOfPair (u v : V) : Hyperedge V :=
  { verts := [u, v], nonempty := by simp }

end CausalGraph
end InfraFormalization
