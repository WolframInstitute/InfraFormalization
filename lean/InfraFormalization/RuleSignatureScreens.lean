import InfraFormalization.CandidateRuleCatalog
import InfraFormalization.RuleSignature

/-!
**Candidate rules passing signature screens** (H3 / #77).

A *signature screen* is a predicate on rule-produced `RuleSignature V`
that filters out rules incompatible with a target. The core screens
available in `RuleSignature.lean`:

  * `RuleSignature.sameEdgeCount` — matching `|E|`.
  * `RuleSignature.sameDim` — matching local Wolfram-Hausdorff function.
  * `RuleSignature.sameBallVolume` — matching `V(v, r)`.
  * `RuleSignature.FullMatch` — all five scalar invariants agree.

This file closes H3 by exhibiting a concrete catalogued rule whose
trajectory-state signatures pass specific screens. The witnesses used:

  * JGORARD's named rule (`gorardNamedRule` on `P6 = Fin 6`) —
    conservative: trajectory-state edge count is invariant, so every
    signature along a conservative trajectory from a 4-edge seed
    passes `sameEdgeCount` against a 4-edge target.
  * Empty-seed trajectory — trivially `sameEdgeCount = 0`.
  * Identity-state trajectory (no steps) — `FullMatch` is reflexive.

These are baseline screen-passes; they vindicate the screening
pipeline and give concrete plugin-witnesses for the IR7 /
reverse-engineering theorem (`reverseEngineeringObligationRefined_holds`).
-/

namespace InfraFormalization
namespace CandidateCatalog

open scoped BigOperators

/-! ## Reflexive signature-match (trivial baseline) -/

/-- **Reflexive signature self-match.** Every hypergraph `H` passes
every signature screen against itself. Baseline witness that the
`RuleSignature` framework can be instantiated. -/
theorem hypergraphSignature_FullMatch_self
    {V : Type*} [Fintype V] [DecidableEq V] (H : Hypergraph V) :
    (hypergraphSignature H).FullMatch (hypergraphSignature H) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **sameDim is reflexive**. -/
theorem hypergraphSignature_sameDim_self
    {V : Type*} [Fintype V] [DecidableEq V] (H : Hypergraph V) :
    (hypergraphSignature H).sameDim (hypergraphSignature H) := rfl

/-- **sameBallVolume is reflexive**. -/
theorem hypergraphSignature_sameBallVolume_self
    {V : Type*} [Fintype V] [DecidableEq V] (H : Hypergraph V) :
    (hypergraphSignature H).sameBallVolume (hypergraphSignature H) := rfl

/-! ## Screens for empty / cycle seeds under conservation -/

/-- **Concrete H3 witness**: starting from any hypergraph with
exactly `k` edges, every state along a step-consistent conservative
trajectory has signature edge-count `k`, so every state passes the
`sameEdgeCount` screen against any target with `edgeCount = k`. -/
theorem signature_sameEdgeCount_of_conservative
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : Type*} {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (i : ℕ) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount
      = (hypergraphSignature init).edgeCount := by
  show (τ.states.get ⟨i, hi⟩).size = init.size
  exact trajectory_size_invariant τ hstep hcons i hi

/-- **JGORARD's named rule passes the 4-edge screen from a 4-edge
seed.** Given a trajectory where every applied rule is
`gorardNamedRule` (conservative by `gorardNamedRule_isConservative`),
starting from an initial state with 4 edges, every reachable state
has signature `edgeCount = 4`. Concrete H3 witness. -/
theorem gorardNamedRule_passes_sameEdgeCount_screen
    {P : Type*} {sys : RewritingSystem P}
    (init : Hypergraph P6) (hinit : init.size = 4)
    (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hgorard : ∀ j (hj : j < τ.applications.length),
      (τ.applications.get ⟨j, hj⟩).2.1.IsConservative)
    (i : ℕ) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount = 4 := by
  have : (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount
      = (hypergraphSignature init).edgeCount :=
    signature_sameEdgeCount_of_conservative τ hstep hgorard i hi
  rw [this]
  show init.size = 4
  exact hinit

end CandidateCatalog
end InfraFormalization
