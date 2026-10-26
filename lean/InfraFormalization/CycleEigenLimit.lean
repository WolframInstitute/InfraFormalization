/-
Limit of the scaled cycle eigenvalue.

This module proves that for each `k : ℕ`,
`n² · cycleEigenvalue n k = n² · (−4 sin²(π k / n)) → −(2 π k)²` as `n → ∞`.
The limit `−(2 π k)²` is the `k`-th eigenvalue of the Laplacian on the circle
of length 1. The proof writes `n · sin(π k / n) = (π k) · sinc(π k / n)` and
uses continuity of `sinc` at 0.
-/

import InfraFormalization.CycleSpectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

namespace InfraFormalization

open Filter Topology Real

/-- `n · sin(π k / n) → π k` as `n → ∞`. -/
lemma n_sin_pi_k_div_n_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * sin (π * k / n)) atTop (𝓝 (π * k)) := by
  -- Case k = 0: both sides are 0.
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.sin_zero]
    simpa using tendsto_const_nhds
  -- Case k ≥ 1: use sinc continuity.
  have hπk : (π * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk0)
    exact mul_ne_zero (ne_of_gt Real.pi_pos) this
  have h0 : Tendsto (fun n : ℕ => (π * k : ℝ) / n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsinc : Tendsto (fun n : ℕ => sinc (π * k / n)) atTop (𝓝 1) := by
    have := (continuous_sinc.tendsto 0).comp h0
    simpa [sinc_zero] using this
  have h_eq : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * sin (π * k / n) = π * k * sinc (π * k / n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    have hdiv : (π * k / n : ℝ) ≠ 0 := div_ne_zero hπk hn_ne
    rw [sinc_of_ne_zero hdiv]
    field_simp
  have hπk_sinc_tendsto :
      Tendsto (fun n : ℕ => π * k * sinc (π * k / n)) atTop (𝓝 (π * k * 1)) :=
    tendsto_const_nhds.mul hsinc
  rw [mul_one] at hπk_sinc_tendsto
  exact hπk_sinc_tendsto.congr' (h_eq.mono (fun _ h => h.symm))

/-- `n² · cycleEigenvalue n k = n² · (−4 sin²(π k / n)) → −(2 π k)²`
as `n → ∞`. -/
theorem cycleEigenvalue_scaled_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 * cycleEigenvalue n k) atTop
      (𝓝 (-(2 * π * k)^2)) := by
  have hrw : ∀ n : ℕ, (n : ℝ)^2 * cycleEigenvalue n k
      = -4 * ((n : ℝ) * sin (π * k / n))^2 := by
    intro n
    unfold cycleEigenvalue
    ring
  have h1 := n_sin_pi_k_div_n_tendsto k
  have hsq : Tendsto (fun n : ℕ => ((n : ℝ) * sin (π * k / n))^2) atTop
      (𝓝 ((π * k)^2)) := by
    simpa using h1.pow 2
  have hfinal : Tendsto (fun n : ℕ => -4 * ((n : ℝ) * sin (π * k / n))^2) atTop
      (𝓝 (-4 * (π * k)^2)) :=
    tendsto_const_nhds.mul hsq
  have h_target : (-4 : ℝ) * (π * k)^2 = -(2 * π * k)^2 := by ring
  rw [← h_target]
  exact hfinal.congr (fun n => (hrw n).symm)

end InfraFormalization
