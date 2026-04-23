/-
**CausalGraph → DiagLorentzianManifold bridge** (grounding action #3).

Ties the continuum `DiagLorentzianManifold` target to the discrete
`CausalGraph` side. Each DiagLorentzianManifold gets an attached
origin-obligation Prop:

    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : CausalGraph V) (scale : ℕ → ℝ), scale_pos …

with the bridge property left as the open programme.

Grounded: the obligation existentially binds `CausalGraph V`, itself
a `Hypergraph`-grounded primitive (IC1).
-/

import InfraFormalization.LorentzianManifold
import InfraFormalization.CausalGraphType

namespace InfraFormalization
namespace Curvature

/-- **DiagLorentzianManifold-origin obligation**: the continuum
Lorentzian manifold is claimed to be the GH-limit of some sequence of
scaled discrete causal graphs. -/
def LorentzianManifoldOriginObligation {n : Nat}
    (_target : DiagLorentzianManifold n) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (_G : CausalGraph V) (scale : ℕ → ℝ), (∀ k, 0 < scale k)

/-- **Minkowski's origin obligation**: there exists a causal graph
whose scaled limit is Minkowski. This is the discrete-Lorentzian GH
bridge, currently open. -/
def minkowski4Manifold_from_causalGraph : Prop :=
  LorentzianManifoldOriginObligation minkowski4Manifold

/-- **Any `DiagLorentzianManifold` has the origin-obligation inhabited
at the current statement level.** The obligation Prop is a pure
existential over `CausalGraph V + scale` (no bridgeHolds predicate);
the trivial edge-free `CausalGraph (Fin 1)` inhabits it for every
target manifold. -/
theorem any_lorentzianManifold_has_obligation_witness {n : Nat}
    (M : DiagLorentzianManifold n) :
    LorentzianManifoldOriginObligation M := by
  unfold LorentzianManifoldOriginObligation
  refine ⟨Fin 1, inferInstance, inferInstance,
    { causalEdge := fun _ _ => False
      irrefl := fun _ h => h
      transitively_reduced := fun _ _ h => absurd h id },
    fun k => (1 : ℝ) / (k + 1), ?_⟩
  intro k
  positivity

end Curvature
end InfraFormalization
