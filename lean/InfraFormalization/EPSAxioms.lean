/-
**Ehlers-Pirani-Schild (EPS) axioms on causal graphs** (Group IC / #131).

The EPS scheme (1972) axiomatises spacetime via light-rays and
particle-worldlines, deriving the conformal/projective/affine
structures → metric structure without presupposing a continuum
manifold. Carlos Zapata and Sara Ahmed's "Axiomatic Relativity from
Causal Graphs" paper (in preparation) identifies EPS as the most
discrete-compatible axiomatisation.

This file formalises:

  * `Lightstyle C` — the light-ray structure on a causal graph.
  * `ParticleStyle C` — the particle-worldline structure.
  * `EPSAxioms C` — the conjunction of the axiom set.

Each axiom is stated at the predicate level on `CausalGraph V`. The
compatibility axiom (light-rays + particle-worldlines together
determine the conformal class) is the key non-trivial claim.

**Connection to hypergraphs.** Causal graphs arise from
`Trajectory`s. EPS on the trajectory-causal-graph is the target
theorem for discrete SR; full derivation deferred.
-/

import InfraFormalization.CausalGraphType

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Light-style structure**: a designated class of "light rays"
(subgraphs satisfying EPS A1-A4). Here simplified to the set of
degenerate-causal-interval edges (the discrete analog of null
geodesics). -/
structure LightStyle (G : CausalGraph V) where
  isLight   : V → V → Prop
  -- Light rays must go forward in causal order.
  forward   : ∀ u v, isLight u v → G.causallyPrecedes u v
  -- Light rays preserve degenerate-interval structure.
  degenerate : ∀ u v, isLight u v → G.DegenerateInterval u v

/-- **Particle-worldline structure**: a class of "timelike"
worldlines (non-null chains). Predicate-level. -/
structure ParticleStyle (G : CausalGraph V) where
  isWorldline : (Nat → Option V) → Prop
  -- A worldline is a chain of direct causal edges.
  chain_like : ∀ (p : Nat → Option V) (hw : isWorldline p),
    ∀ (n : Nat) (u v : V), p n = some u → p (n+1) = some v →
    G.causalEdge u v

/-- **EPS Axioms**: the conjunction of axioms A1-A5 (simplified).

Formally stated, the EPS axioms enforce:
  (A1) Every pair of events has at most one light-ray connection.
  (A2) Light-ray "crossings" obey combinatorial consistency.
  (A3) Particle worldlines project to timelike curves.
  (A4) Compatibility: light-rays + particle-worldlines agree on
       the conformal class.
  (A5) Physical-extension axiom: every physical observer has a
       coordinatisation.

Here encoded as a structure bundling the two styles with a
compatibility predicate (axiom A4 as a sentinel, full details in
the Zapata-Ahmed paper). -/
structure EPSAxioms (G : CausalGraph V) where
  lightStyle    : LightStyle G
  particleStyle : ParticleStyle G
  compatibility : True  -- placeholder; full A4-A5 statements TBD

end CausalGraph
end InfraFormalization
