/-
Light-ray and worldline structures on a causal graph.

The module defines `LightStyle G`, a relation on vertices whose pairs are
causally ordered and span a degenerate interval, and `ParticleStyle G`, a
predicate on vertex sequences whose consecutive entries are causal edges.
`EPSAxioms G` bundles one of each with the condition that consecutive
worldline vertices are not light-related. Of the Ehlers-Pirani-Schild (1972)
axioms, only this compatibility condition is stated. The theorem
`eps_worldline_not_light` combines the two fields for one worldline step.
-/

import InfraFormalization.CausalGraphType

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A relation `isLight` on vertices such that every related pair `(u, v)`
satisfies `G.causallyPrecedes u v` and `G.DegenerateInterval u v`. -/
structure LightStyle (G : CausalGraph V) where
  isLight   : V → V → Prop
  -- Related pairs are causally ordered.
  forward   : ∀ u v, isLight u v → G.causallyPrecedes u v
  -- Related pairs span a degenerate interval.
  degenerate : ∀ u v, isLight u v → G.DegenerateInterval u v

/-- A predicate `isWorldline` on partial vertex sequences `ℕ → Option V` such
that consecutive defined entries of a worldline are joined by a causal edge. -/
structure ParticleStyle (G : CausalGraph V) where
  isWorldline : (Nat → Option V) → Prop
  -- Consecutive defined entries are joined by a causal edge.
  chain_like : ∀ (p : Nat → Option V) (hw : isWorldline p),
    ∀ (n : Nat) (u v : V), p n = some u → p (n+1) = some v →
    G.causalEdge u v

/-- A `LightStyle G`, a `ParticleStyle G`, and the condition that no two
consecutive defined entries of a worldline are related by `isLight`. No other
Ehlers-Pirani-Schild axiom is included. -/
structure EPSAxioms (G : CausalGraph V) where
  lightStyle    : LightStyle G
  particleStyle : ParticleStyle G
  /-- Consecutive defined entries of a worldline are not related by
  `isLight`. -/
  compatibility : ∀ (p : Nat → Option V), particleStyle.isWorldline p →
    ∀ (n : Nat) (u v : V), p n = some u → p (n + 1) = some v →
      ¬ lightStyle.isLight u v

/-- Consecutive defined entries `u, v` of a worldline satisfy
`G.causalEdge u v` and `¬ isLight u v`. The proof pairs the fields
`chain_like` and `compatibility`. -/
theorem eps_worldline_not_light {G : CausalGraph V}
    (eps : EPSAxioms G) (p : Nat → Option V)
    (hw : eps.particleStyle.isWorldline p)
    (n : Nat) (u v : V) (hu : p n = some u) (hv : p (n + 1) = some v) :
    G.causalEdge u v ∧ ¬ eps.lightStyle.isLight u v :=
  ⟨eps.particleStyle.chain_like p hw n u v hu hv,
   eps.compatibility p hw n u v hu hv⟩

end CausalGraph
end InfraFormalization
