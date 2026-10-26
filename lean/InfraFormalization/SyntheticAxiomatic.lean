/-
Axiom-style predicates on hypergraph distance.

This module defines predicates on a hypergraph `H` stated with
`SyntheticLineSegment`, `SyntheticCircle` and `Hypergraph.dist`: nonempty
segments, the betweenness property of segment vertices, and equal
cardinality of circles of equal radius. It proves that segment membership
is betweenness and that betweenness is symmetric in the endpoints.
-/

import InfraFormalization.SyntheticGeometry

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Segments -/

/-! ## Circles -/

/-- Any two circles of the same radius have the same cardinality. -/
def CircleCongruence (H : Hypergraph V) : Prop :=
  ∀ (c₁ c₂ : V) (r : Nat),
    (H.SyntheticCircle c₁ r).card = (H.SyntheticCircle c₂ r).card

/-! ## Betweenness -/

/-- `w` is between `u` and `v`: `dist u w + dist w v = dist u v`. -/
def Between (H : Hypergraph V) (u v w : V) : Prop :=
  H.dist u w + H.dist w v = H.dist u v

/-- `w` lies on the segment from `u` to `v` if and only if `w` is between
`u` and `v`. -/
theorem segment_is_between (H : Hypergraph V) (u v w : V) :
    w ∈ H.SyntheticLineSegment u v ↔ H.Between u v w := by
  rw [Hypergraph.mem_syntheticLineSegment]
  rfl

/-- `w` is between `u` and `v` if and only if `w` is between `v` and
`u`. -/
theorem between_symm (H : Hypergraph V) (u v w : V) :
    H.Between u v w ↔ H.Between v u w := by
  unfold Between
  rw [H.dist_comm v w, H.dist_comm v u, H.dist_comm u w]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## Conjunction -/

end Hypergraph
end InfraFormalization
