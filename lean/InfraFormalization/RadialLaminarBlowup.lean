/-
Radial and laminar blowups.

P. Hajek's Infrageometry paclet provides radial and laminar blowups as refinement operations. This
module defines two predicates on a vertex map `ψ : V → W` between hypergraphs `H` and `K`:
`IsRadialBlowup`, about distances from a basepoint, and `IsLaminarBlowup`, about distances to a
reference set.
-/

import InfraFormalization.HypergraphDistance
import InfraFormalization.BlowupOperations

namespace InfraFormalization

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- `ψ` sends `basepoint_V` to `basepoint_W`, and for every vertex `v` the distance from
`basepoint_W`
to `ψ v` in `K` is a natural-number multiple of the distance from `basepoint_V` to `v` in `H`. The
multiple may depend on `v`. -/
def IsRadialBlowup (ψ : V → W) (basepoint_V : V) (basepoint_W : W)
    (H : Hypergraph V) (K : Hypergraph W) : Prop :=
  ψ basepoint_V = basepoint_W ∧
  ∀ v : V,
    -- Distance in K is a multiple of distance in H; the multiple depends on v.
    ∃ s : ℕ, K.dist basepoint_W (ψ v) = s * H.dist basepoint_V v

/-- `ψ` maps `chain_V` into `chain_W`, and whenever `v₁, v₂` are equidistant from some vertex of
`chain_V` in `H`, their images are equidistant from some vertex of `chain_W` in `K`. -/
def IsLaminarBlowup (ψ : V → W) (chain_V : Finset V) (chain_W : Finset W)
    (H : Hypergraph V) (K : Hypergraph W) : Prop :=
  -- Every vertex of the chain_V maps into chain_W.
  (∀ u ∈ chain_V, ψ u ∈ chain_W) ∧
  -- Layer structure is preserved.
  ∀ v₁ v₂ : V,
    (∃ u ∈ chain_V, H.dist u v₁ = H.dist u v₂) →
    (∃ w ∈ chain_W, K.dist w (ψ v₁) = K.dist w (ψ v₂))

end InfraFormalization
