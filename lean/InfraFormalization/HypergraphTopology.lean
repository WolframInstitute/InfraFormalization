/-
**Pre-metric topological invariants of a hypergraph** (#323 TOP1, #326 TOP4).

The two most elementary topological invariants on a hypergraph, requiring
neither metric nor measure structure:
- `b_0` = number of connected components — Stephen's "is every point
  reachable from every other" — the partition every other invariant sits
  inside.
- `b_1` = first Betti number / cycle rank — `#hyperedges − #vertices +
  #components` — the most elementary non-trivial invariant after `b_0`.

**Connection to hypergraphs.** Native. Both are functions of the
underlying combinatorial structure; no metric tensor, no continuum.

**Connection to the Hodge-Laplacian spectrum** (IT3): on the constant
sheaf, `b_k = dim ker(Hodge Laplacian on k-forms)`. So `b_0` = nullity of
graph Laplacian, `b_1` = nullity of 1-form Hodge Laplacian. The
combinatorial definitions here agree with the spectral definitions
(bridge theorem to follow).

**Spatial flavour** is what we surface here. Causal / branchial /
rewriting-reachable flavours (the four-flavour structure documented in
`INFRAGEOMETRY.md` §5b Layer −1) live in their respective files
(`Causal.lean`, `Branchial.lean`, `Multiway.lean`).
-/

import InfraFormalization.HypergraphDistance
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## b_0 — connected components (TOP4 spatial flavour)

Spatial connectedness via the clique-expansion `H.toSimpleGraph`.
Mathlib's `SimpleGraph.ConnectedComponent` plus the `Fintype` instance
from `Connectivity/Finite.lean` make this directly computable. -/

/-- **Connected components** of the spatial graph — quotient of `V` by
`Reachable`. The partition. -/
noncomputable abbrev SpatialConnectedComponent (H : Hypergraph V) : Type _ :=
  H.toSimpleGraph.ConnectedComponent

/-- **`b_0` (spatial flavour)** — number of connected components in the
clique-expansion graph. The most elementary topological invariant.
Stephen's "is every point reachable from every other" reduces to
`b_0 = 1`. -/
noncomputable def spatialB0 (H : Hypergraph V) : ℕ :=
  Fintype.card H.SpatialConnectedComponent

/-- **Spatial connectedness predicate**: every vertex reachable from every
other (in the clique-expansion). Equivalently `spatialB0 = 1` (when `V`
is non-empty). -/
def IsSpatiallyConnected (H : Hypergraph V) : Prop :=
  H.toSimpleGraph.Connected

/-- **`spatialB0` is bounded above by `Fintype.card V`** — at most one
component per vertex. The map `V → ConnectedComponent` (taking each vertex
to its component-quotient class) is surjective; hence card-of-image ≤
card-of-source. -/
theorem spatialB0_le_card (H : Hypergraph V) :
    H.spatialB0 ≤ Fintype.card V := by
  unfold spatialB0 SpatialConnectedComponent
  exact Fintype.card_le_of_surjective
    (fun v => H.toSimpleGraph.connectedComponentMk v)
    (fun c => Quot.exists_rep c)

/-! ## b_1 — first Betti / cycle rank (TOP1)

For a finite graph: `b_1 = #edges − #vertices + #components`. For a
hypergraph, the analogous formula uses *hyperedges* rather than
clique-expanded edges:

  `b_1(H) := H.size − Fintype.card V + spatialB0(H)`

(at the integer-arithmetic level; we use ℤ to avoid `ℕ`-underflow on
disconnected examples).

This corresponds to the **simplicial-style b_1** treating each hyperedge
as a single 1-cell. The clique-expansion variant
`H.toSimpleGraph.edgeFinset.card − Fintype.card V + spatialB0` is a
distinct invariant (lives on the graph CLOSURE1 #362 chooses).
-/

/-- **First Betti number / cycle rank (hyperedge-counted, integer
arithmetic)** — `#hyperedges − #vertices + #components`. Stephen's most
elementary non-trivial invariant after `b_0`. -/
noncomputable def firstBettiZ (H : Hypergraph V) : ℤ :=
  (H.size : ℤ) - (Fintype.card V : ℤ) + (H.spatialB0 : ℤ)

/-- **`b_1` lower bound** on a finite hypergraph: `b_1 ≥ #hyperedges −
#vertices` (since `spatialB0 ≥ 0`). When the graph is connected
(`spatialB0 = 1`), `b_1 = #hyperedges − #vertices + 1` exactly. -/
theorem firstBettiZ_lower_bound (H : Hypergraph V) :
    (H.size : ℤ) - (Fintype.card V : ℤ) ≤ H.firstBettiZ := by
  unfold firstBettiZ
  have : (0 : ℤ) ≤ (H.spatialB0 : ℤ) := Int.natCast_nonneg _
  linarith

/-! ## Higher Betti placeholder (TOP2 #324)

`b_k` for `k ≥ 2` requires a chosen cellular structure (the closure
problem CLOSURE1 #362). The `Hodge Laplacian on k-forms` from KnillCore
gives one route once we surface the kernel-dimension API. Placeholder
predicate left here as a target. -/

/-- **k-th Betti number obligation**: for a chosen cellular extension of
`H`, the `k`-th Hodge-Laplacian kernel has dimension `n`. Placeholder
until KnillCore exposes the kernel-dimension extractor (TOP2 #324). -/
def HasBetti (H : Hypergraph V) (k : ℕ) (_n : ℕ) : Prop :=
  -- Will be: `Fintype.card (Module.End.eigenspace (hodgeLaplacian k) 0) = n`.
  -- Currently a Prop placeholder; the spectral apparatus exists in IT3
  -- but has not been packaged as a `bettiNumber` extractor yet.
  H.size ≥ 0  -- trivially true; placeholder content

/-! ## Connection to MILESTONE / topology-before-metric layering -/

/-- **`spatiallyConnected_implies_b0_pos`** — if Stephen's "every point
reachable from every other" holds, there is at least one connected
component. (The converse direction needs the unique-class characterisation
which lives in Mathlib follow-up; we surface the forward implication
which is the structurally important one.) -/
theorem spatialB0_pos_of_nonempty [Nonempty V] (H : Hypergraph V) :
    0 < H.spatialB0 := by
  unfold spatialB0 SpatialConnectedComponent
  -- nonempty quotient when source is nonempty
  exact Fintype.card_pos

end Hypergraph
end InfraFormalization
