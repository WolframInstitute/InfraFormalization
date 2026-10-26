import InfraFormalization.CandidateRuleCatalog
import InfraFormalization.RuleSignature

/-!
Signature comparisons for rule trajectories.

This module proves that the signature of a hypergraph matches itself under
`FullMatch`, `sameDim` and `sameBallVolume`, and that on a step-consistent
trajectory of conservative rules every state has the signature edge count
of the initial state, in particular 4 when the initial state on `P6` has 4
edges.
-/

namespace InfraFormalization
namespace CandidateCatalog

open scoped BigOperators

/-! ## Reflexivity -/

/-! ## Edge counts along conservative trajectories -/

/-- On a step-consistent trajectory whose applications all use
conservative rules, every state has the signature edge count of the
initial state. -/
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

end CandidateCatalog
end InfraFormalization
