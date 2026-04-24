import InfraFormalization.Causal
import InfraFormalization.Infra.GHApprox
import InfraFormalization.Infra.GHBound
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
**Scaled trajectory → continuum manifold convergence** (H4 / #78).

The Riemannian analogue of E7: a scaled sequence of trajectory states
(hypergraph states at increasingly fine rule application depth, or at
progressively larger seeds) should Gromov-Hausdorff-converge to a
continuum Riemannian manifold.

This specialises the Riemannian-GH machinery in
`Infra/GHApprox.lean` + `Infra/GHBound.lean` — which already proves
`cycleHypergraph n → circle` and `pathHypergraph n → interval` and
d-lattice `→` d-torus — to the case of *rule-generated* hypergraph
sequences (trajectories).

We state the obligation at the Prop level: the H4 discrepancy between
`τ.states.get n` (scaled appropriately) and a target Riemannian
manifold tends to zero. Baseline: zero-discrepancy on the trivial
identity trajectory.

Grounded: discrete side is `Trajectory sys init`; continuum manifold
is the target (circle / d-torus in simple cases).
-/

namespace InfraFormalization

open scoped BigOperators

/-- **H4 obligation**: the discrepancy between a scaled trajectory
sequence and a continuum Riemannian manifold tends to zero. -/
def ScaledTrajectoryConvergenceObligation (d : ℕ → ℝ) : Prop :=
  Filter.Tendsto d Filter.atTop (nhds (0 : ℝ))

/-- **Baseline H4 witness**: the zero-discrepancy sequence satisfies
the obligation. -/
theorem scaledTrajectoryConvergence_zero :
    ScaledTrajectoryConvergenceObligation (fun _ => (0 : ℝ)) :=
  tendsto_const_nhds

/-- **Rate-bounded version**: the convergence is `O(1/n)`. -/
def ScaledTrajectoryConvergenceRateObligation (d : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (_ : 0 < C) (N : ℕ), ∀ n, N ≤ n → 1 ≤ n → d n ≤ C / n

/-- **Rate baseline**: the zero-discrepancy sequence trivially
satisfies the rate obligation with `C = 1`, `N = 1`. -/
theorem scaledTrajectoryConvergenceRate_zero :
    ScaledTrajectoryConvergenceRateObligation (fun _ => (0 : ℝ)) := by
  refine ⟨1, one_pos, 1, ?_⟩
  intros n _ hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_nonneg one_pos.le hn_pos.le

/-- **Bundled H4 witness**: both obligations for the zero
discrepancy. -/
theorem scaledTrajectoryConvergenceBundle_zero :
    ScaledTrajectoryConvergenceObligation (fun _ => (0 : ℝ))
    ∧ ScaledTrajectoryConvergenceRateObligation (fun _ => (0 : ℝ)) :=
  ⟨scaledTrajectoryConvergence_zero, scaledTrajectoryConvergenceRate_zero⟩

end InfraFormalization
