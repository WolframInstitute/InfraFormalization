/-
**Radial and laminar blowup operations** (Group IB / #151 IB6).

PHAJEK's Infrageometry paclet provides "radial" and "laminar"
blowups as canonical refinement operators for illustrating
scaling/renormalisation. We formalise the predicate-level notions:

  * `IsRadialBlowup ψ` — blowup preserves radial structure (distances
    from a basepoint).
  * `IsLaminarBlowup ψ` — blowup preserves a laminar ("layered")
    structure.

**Connection to hypergraphs.** Native. Blowups are `Hypergraph V →
Hypergraph W` maps; radial and laminar are structural predicates.
-/

import InfraFormalization.HypergraphDistance
import InfraFormalization.BlowupOperations

namespace InfraFormalization

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- **Radial blowup predicate**: there is a basepoint preservation —
the blowup `ψ : V → W` sends basepoint to basepoint and preserves
the distance-rank of each vertex (up to the blowup scale). -/
def IsRadialBlowup (ψ : V → W) (basepoint_V : V) (basepoint_W : W)
    (H : Hypergraph V) (K : Hypergraph W) : Prop :=
  ψ basepoint_V = basepoint_W ∧
  ∀ v : V,
    -- Distance in K is a multiple of distance in H (the scale factor).
    ∃ s : ℕ, K.dist basepoint_W (ψ v) = s * H.dist basepoint_V v

/-- **Laminar blowup predicate**: blowup preserves a foliation
structure — vertices on the same "layer" in `H` map to vertices on
the same "layer" in `K`. Here the layers are defined by distance to
a reference chain. -/
def IsLaminarBlowup (ψ : V → W) (chain_V : Finset V) (chain_W : Finset W)
    (H : Hypergraph V) (K : Hypergraph W) : Prop :=
  -- Every vertex of the chain_V maps into chain_W.
  (∀ u ∈ chain_V, ψ u ∈ chain_W) ∧
  -- Layer structure is preserved.
  ∀ v₁ v₂ : V,
    (∃ u ∈ chain_V, H.dist u v₁ = H.dist u v₂) →
    (∃ w ∈ chain_W, K.dist w (ψ v₁) = K.dist w (ψ v₂))

end InfraFormalization
