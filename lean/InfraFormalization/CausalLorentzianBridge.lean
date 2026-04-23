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

end Curvature
end InfraFormalization
