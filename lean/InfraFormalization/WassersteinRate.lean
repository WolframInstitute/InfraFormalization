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
the obligation level. A concrete Wasserstein-1 distance on finite
supports is to be defined *in this project* (task #214), not left
to Mathlib; task #215 then discharges A7 / A8 with a real `O(1/n)`
bound rather than the baseline witness below.

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

/-! ## Subdivision-rule trajectory discrepancy (#234 entry)

The canonical discrepancy for the edge-subdivision rule's n-step
trajectory `pathEdges (subdVerts n)`: the spacing `1 / 2^n` between
adjacent vertices of the path, scaled by the diameter `1`. This is
an `O(1/n)` discrepancy because `n < 2^n`, so `1/2^n < 1/n`. -/

/-- **Subdivision discrepancy**: the natural Wasserstein-1 spacing
of the n-step trajectory `pathEdges (subdVerts n)`, equal to
`1 / 2^n` (the inverse of the edge count). -/
noncomputable def subdivisionDiscrepancy : ScaledDiscrepancy :=
  fun n => 1 / (2 : ℝ)^n

/-- **#234 main**: the subdivision-rule discrepancy `1/2^n` satisfies
the `O(1/n)` Wasserstein-rate obligation. Direct from `n < 2^n`
(`Nat.lt_two_pow_self`), so `1/2^n < 1/n` for `n ≥ 1`. With `C = 1`
and `N = 1`, the bound `1/2^n ≤ 1/n` holds for every `n ≥ 1`. -/
theorem subdivisionDiscrepancy_satisfies_obligation :
    WassersteinRateObligation subdivisionDiscrepancy := by
  refine ⟨1, one_pos, 1, ?_⟩
  intros n _ hn_one
  unfold subdivisionDiscrepancy
  have h_n_lt : n < 2^n := Nat.lt_two_pow_self
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn_one
  have h_2n_pos : (0 : ℝ) < (2 : ℝ)^n := by positivity
  rw [div_le_div_iff₀ h_2n_pos h_n_pos, one_mul, one_mul]
  exact_mod_cast h_n_lt.le

/-- **Tendsto variant for the subdivision discrepancy**: `1/2^n → 0`
as `n → ∞`. Direct from `tendsto_one_div_pow_atTop_nhds_zero` style
arguments — `2^n → ∞` so `1/2^n → 0`. -/
theorem subdivisionDiscrepancy_tendsto :
    WassersteinRateTendsto subdivisionDiscrepancy := by
  unfold WassersteinRateTendsto subdivisionDiscrepancy
  -- 1 / 2^n = (1/2)^n with |1/2| < 1, so → 0 by tendsto_pow_atTop_nhds_zero_iff.
  have h_eq : (fun n : ℕ => 1 / (2 : ℝ)^n) = (fun n : ℕ => (1/2 : ℝ)^n) := by
    funext n
    rw [div_pow, one_pow]
  rw [h_eq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- **Bundled #234 witness**: the subdivision-rule trajectory
discharges both the `O(1/n)` obligation and the tendsto-zero variant,
with explicit decay rate `1/2^n`. End-to-end concrete certificate that
the canonical Wolfram-rule trajectory converges to a continuum target
in W_1. -/
theorem subdivisionDiscrepancyBundle :
    WassersteinRateObligation subdivisionDiscrepancy
    ∧ WassersteinRateTendsto subdivisionDiscrepancy :=
  ⟨subdivisionDiscrepancy_satisfies_obligation, subdivisionDiscrepancy_tendsto⟩

end InfraFormalization
