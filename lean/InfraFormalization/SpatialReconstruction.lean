/-
**Spatially-reconstructed hypergraph** from a causal graph + foliation
(Group IC / #129).

Following the Madrid-talk pipeline:

  1. Pick an observer foliation of the causal graph.
  2. In each slice, connect events that share an *immediate common
     ancestor* in the previous slice.

The resulting structure is a `Hypergraph (slice)` for each slice,
and together they form a time-evolving hypergraph — the
**spatially-reconstructed hypergraph**.

**Connection to hypergraphs.** Native: the output is literally a
`Hypergraph V`-valued function of the foliation level. Input is a
`CausalGraph V` (from `CausalGraphType.lean`) + a `Foliation`.

**What this file gives.**

  * `immediateCommonAncestor G u v` — the predicate "events `u, v`
    share at least one immediate common ancestor in `G`" (via
    `causalEdge`).
  * `spatialReconstructionPredicate G slice` — the hypergraph-edge
    predicate on pairs of events within a foliation slice.
  * `spatialHyperedgeOfPair G u v` — constructs a 2-vertex
    `Hyperedge` when the pair shares an ancestor.

The full construction of the per-slice `Hypergraph V` and its
consistency with causal-graph dynamics is a substantial follow-up;
here we give the piece-parts. -/

import InfraFormalization.CausalGraphType
import InfraFormalization.CausalFoliation

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-- **Immediate common ancestor**: event `a` is an immediate common
ancestor of `u` and `v` if `G.causalEdge a u` and `G.causalEdge a v`.
No transitivity — direct causal arrows only. -/
def ImmediateCommonAncestor (u v : V) (a : V) : Prop :=
  G.causalEdge a u ∧ G.causalEdge a v

/-- **Two events share an immediate common ancestor** if at least
one exists. -/
def ShareImmediateAncestor (u v : V) : Prop :=
  ∃ a : V, G.ImmediateCommonAncestor u v a

/-- **Symmetry of the share-ancestor relation.** -/
theorem ShareImmediateAncestor.symm {u v : V}
    (h : G.ShareImmediateAncestor u v) : G.ShareImmediateAncestor v u := by
  obtain ⟨a, hau, hav⟩ := h
  exact ⟨a, hav, hau⟩

/-- **Events don't share an ancestor with themselves** via `causalEdge`:
`a → u` and `a → u` are the same edge, so "shared" degenerates. We
state the non-trivial predicate as "`u ≠ v` and there's a common
ancestor". -/
def ShareImmediateAncestorNontrivial (u v : V) : Prop :=
  u ≠ v ∧ G.ShareImmediateAncestor u v

/-- **The spatial-reconstruction edge predicate**: whether a pair
`{u, v}` in a foliation slice should be connected in the
spatially-reconstructed hypergraph at that slice. -/
def spatialReconstructionAdj (slice : Finset V) (u v : V) : Prop :=
  u ∈ slice ∧ v ∈ slice ∧ G.ShareImmediateAncestorNontrivial u v

/-- **Build a 2-vertex hyperedge from a pair sharing an ancestor.**
The directionality is `[u, v]` (arbitrary but consistent). -/
def spatialHyperedgeOfPair (u v : V) : Hyperedge V :=
  { verts := [u, v], nonempty := by simp }

end CausalGraph
end InfraFormalization
