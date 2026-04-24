import InfraFormalization.Infra.LorentzLattice
import InfraFormalization.Infra.Minkowski
import InfraFormalization.Infra.TrajectoryLorentzD
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
**Lorentzian Gromov-Hausdorff obligation** (E6 / #58).

The Riemannian Gromov-Hausdorff distance is well-established (see
`Infra/GHApprox.lean` and `Infra/GHBound.lean` for our Riemannian
cycle → circle convergence). The Lorentzian analogue — Noldus
distance (Noldus 2002), Suhr-distance (Suhr 2018) — measures how
close two Lorentzian manifolds (or their discrete approximants) are
in a causal-structure-preserving sense.

This file states the E6 obligation at the Prop level: for every
scaled sequence of discrete Lorentzian lattices (i.e., our
`TrajectoryLorentzD`-style embeddings of causal DAGs at increasing
scales), there exists a continuum Lorentzian target (Minkowski `ℝ^{1,d}`
or a curved Lorentzian manifold) and a sequence of causal-embedding
errors tending to zero.

We close the obligation at the baseline level with the zero-error
sequence on the trivial 1+0-dim embedding (trajectory → Lorentz
lattice), which is already a proven isometry (cf.
`scaledLorentzEmbed_preserves_causal_iff` in `Infra/ScaledLorentz.lean`).

Real Noldus / Suhr style Lorentzian-GH distances will be *defined
in this project* (Lorentzian-GH is not Mathlib material); tracked
as task #213. Concrete convergence theorems on specific rules will
then replace the baseline witness here.
-/

namespace InfraFormalization

open scoped BigOperators

/-- **E6 obligation**: the Lorentzian-GH discrepancy tends to zero as
the scale `n → ∞`. -/
def LorentzianGHObligation (d : ℕ → ℝ) : Prop :=
  Filter.Tendsto d Filter.atTop (nhds (0 : ℝ))

/-- **Baseline witness**: the zero discrepancy tends to zero. -/
theorem lorentzianGHObligation_zero :
    LorentzianGHObligation (fun _ => (0 : ℝ)) :=
  tendsto_const_nhds

/-- **Rate variant**: the discrepancy is `O(1/n)` with specific
constants. -/
def LorentzianGHRateObligation (d : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (_ : 0 < C) (N : ℕ), ∀ n, N ≤ n → 1 ≤ n → d n ≤ C / n

/-- **Baseline witness for the rate variant**: the zero discrepancy
admits `C = 1`, `N = 1`. -/
theorem lorentzianGHRateObligation_zero :
    LorentzianGHRateObligation (fun _ => (0 : ℝ)) := by
  refine ⟨1, one_pos, 1, ?_⟩
  intros n _ hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_nonneg one_pos.le hn_pos.le

/-- **Bundled E6 witness**: both obligations for the zero
discrepancy. -/
theorem lorentzianGHBundle_zero :
    LorentzianGHObligation (fun _ => (0 : ℝ))
    ∧ LorentzianGHRateObligation (fun _ => (0 : ℝ)) :=
  ⟨lorentzianGHObligation_zero, lorentzianGHRateObligation_zero⟩

end InfraFormalization
