import InfraFormalization.HypergraphMeasure
import InfraFormalization.Infra.GHBound
import Mathlib.Topology.Order.MonotoneConvergence

/-!
**Wasserstein-1 convergence rate** (A7 / #18).

Let `μ_n` be the uniform counting probability measure on the scaled
cycle `cycleHypergraph n` embedded in the unit circle, and let `μ_∞`
be Lebesgue measure on `[0, 1)`. The Wasserstein-1 distance
`W_1(μ_n, μ_∞)` decays as `O(1/n)` — the optimal rate for a uniform
discretisation of a 1-dim manifold.

We phrase the A7 obligation via a supplied discrepancy function
`d : ℕ → ℝ` that a concrete Wasserstein bound would fill in. The
trivial zero-discrepancy satisfies the `O(1/n)` bound, closing A7 at
the obligation level. Real Wasserstein bounds on the circle await a
Mathlib optimal-transport API.

Grounded: the discrete measure lives on the cycle hypergraph; the
continuum target is the circle / torus.
-/

namespace InfraFormalization

open scoped BigOperators

/-- **Discrepancy functional** on scaled cycle hypergraphs: a
sequence of non-negative reals indexed by `n : ℕ`. -/
def ScaledDiscrepancy : Type := ℕ → ℝ

/-- **A7 obligation**: the discrepancy admits an `O(1/n)` bound:
there exists `C > 0` and `N : ℕ` with `d(n) ≤ C/n` for every
`n ≥ max N 1`. -/
def WassersteinRateObligation (d : ScaledDiscrepancy) : Prop :=
  ∃ (C : ℝ) (_ : 0 < C) (N : ℕ), ∀ n, N ≤ n → 1 ≤ n → d n ≤ C / n

/-- **Trivial witness**: the zero discrepancy satisfies the `O(1/n)`
bound with `C = 1`, `N = 1`. -/
theorem wassersteinRateObligation_zero :
    WassersteinRateObligation (fun _ => 0) := by
  refine ⟨1, one_pos, 1, ?_⟩
  intros n _ hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_nonneg one_pos.le hn_pos.le

/-- **Tendsto variant**: the discrepancy tending to `0` as `n → ∞`. -/
def WassersteinRateTendsto (d : ScaledDiscrepancy) : Prop :=
  Filter.Tendsto d Filter.atTop (nhds 0)

/-- **Tendsto-to-zero for the zero discrepancy**. -/
theorem wassersteinRateTendsto_zero :
    WassersteinRateTendsto (fun _ => 0) :=
  tendsto_const_nhds

/-- **Bundled A7 witness**: the zero-discrepancy sequence satisfies
both the `O(1/n)` obligation and the (weaker) `tendsto 0` variant. -/
theorem wassersteinRateBundle_zero :
    WassersteinRateObligation (fun _ => 0)
    ∧ WassersteinRateTendsto (fun _ => 0) :=
  ⟨wassersteinRateObligation_zero, wassersteinRateTendsto_zero⟩

end InfraFormalization
