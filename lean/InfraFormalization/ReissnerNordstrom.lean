/-
The Reissner-Nordström metric in coordinates.

This module defines the metric
`ds² = −f dt² + f⁻¹ dr² + r² dθ² + r² sin²θ dφ²` with
`f(r) = 1 − 2M/r + Q²/r²`, its inverse and first partial derivatives, and
packages them as a `PartialMetricData 4` valid where `r > 0`, `f(r) > 0`
and `sin θ ≠ 0`. It proves that at `Q = 0` the lapse is `1 − 2M/r` and is
positive for `r > 2M`.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- The lapse function `f(r) = 1 − 2M/r + Q²/r²`. -/
noncomputable def rnLapse (M Q : ℝ) (r : ℝ) : ℝ :=
  1 - 2 * M / r + Q^2 / r^2

/-- Metric components in coordinates `(t, r, θ, φ)`: `g_{00} = −f(r)`,
`g_{11} = 1/f(r)`, `g_{22} = r²`, `g_{33} = r² sin²θ`, off-diagonal 0. -/
noncomputable def rnG (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -rnLapse M Q r
    else if μ.val = 1 then 1 / rnLapse M Q r
    else if μ.val = 2 then r^2
    else r^2 * (Real.sin θ)^2

/-- Inverse metric components: the reciprocals of the diagonal metric
components, off-diagonal 0. -/
noncomputable def rnGinv (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -1 / rnLapse M Q r
    else if μ.val = 1 then rnLapse M Q r
    else if μ.val = 2 then 1 / r^2
    else 1 / (r^2 * (Real.sin θ)^2)

/-- The domain of validity: `r > 0`, `f(r) > 0` and `sin θ ≠ 0`. For
`M² > Q²`, `f(r) > 0` holds outside the outer horizon and inside the inner
horizon. -/
def RNValid (M Q : ℝ) (x : Fin 4 → ℝ) : Prop :=
  x 1 > 0 ∧ rnLapse M Q (x 1) > 0 ∧ Real.sin (x 2) ≠ 0

/-- At `Q = 0` and `r > 0`, the lapse is `1 − 2M/r`. -/
theorem rnLapse_schwarzschild (M r : ℝ) (hr : r > 0) :
    rnLapse M 0 r = 1 - 2 * M / r := by
  unfold rnLapse
  simp

/-- At `Q = 0`, if `r > 0` and `r > 2M`, the lapse is positive. -/
theorem rnLapse_pos_of_large_r_Q_zero (M r : ℝ) (h2M : r > 2 * M) (hr : r > 0) :
    rnLapse M 0 r > 0 := by
  rw [rnLapse_schwarzschild M r hr]
  have hr_ne : r ≠ 0 := ne_of_gt hr
  rw [show (1 : ℝ) - 2 * M / r = (r - 2 * M) / r from by field_simp]
  exact div_pos (by linarith) hr

/-- `rnG` is symmetric. -/
theorem rnG_symm (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    rnG M Q x μ ν = rnG M Q x ν μ := by
  unfold rnG
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- `rnGinv` is symmetric. -/
theorem rnGinv_symm (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    rnGinv M Q x μ ν = rnGinv M Q x ν μ := by
  unfold rnGinv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- First partial derivatives `∂_l g_{μν}`. The nonzero components are:
  * `∂_r g_{00} = −f'(r)` where `f'(r) = 2M/r² − 2Q²/r³`
  * `∂_r g_{11} = −f'(r)/f(r)²`
  * `∂_r g_{22} = 2 r`
  * `∂_r g_{33} = 2 r sin²θ`
  * `∂_θ g_{33} = 2 r² sinθ cosθ`
Off-diagonal entries and other partials vanish. -/
noncomputable def rnDg (M Q : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    let fp := 2 * M / r^2 - 2 * Q^2 / r^3
    if l.val = 1 then
      if μ.val = 0 then -fp
      else if μ.val = 1 then -fp / (rnLapse M Q r)^2
      else if μ.val = 2 then 2 * r
      else 2 * r * (Real.sin θ)^2
    else if l.val = 2 then
      if μ.val = 3 then 2 * r^2 * Real.sin θ * Real.cos θ
      else 0
    else 0

/-- `rnDg l x μ ν = rnDg l x ν μ`. -/
theorem rnDg_symm (M Q : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    rnDg M Q l x μ ν = rnDg M Q l x ν μ := by
  unfold rnDg
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- The Reissner-Nordström metric as a `PartialMetricData 4` on
`RNValid M Q`. -/
noncomputable def rnPartial (M Q : ℝ) : PartialMetricData 4 where
  g := rnG M Q
  ginv := rnGinv M Q
  dg := rnDg M Q
  valid := RNValid M Q
  g_symm := fun x _ μ ν => rnG_symm M Q x μ ν
  ginv_symm := fun x _ μ ν => rnGinv_symm M Q x μ ν
  ginv_mul := by
    intros x hx μ ν
    obtain ⟨hr, hf, hsinθ⟩ := hx
    have hr_ne : x 1 ≠ 0 := ne_of_gt hr
    have hr_sq_ne : (x 1)^2 ≠ 0 := pow_ne_zero 2 hr_ne
    have hf_ne : rnLapse M Q (x 1) ≠ 0 := ne_of_gt hf
    have hsinθ_sq_ne : (Real.sin (x 2))^2 ≠ 0 := pow_ne_zero 2 hsinθ
    by_cases hμν : μ = ν
    · subst hμν
      rw [Finset.sum_eq_single μ]
      · rw [if_pos rfl]
        unfold rnGinv rnG
        simp only [ne_eq, not_true_eq_false, if_false]
        by_cases h0 : μ.val = 0
        · simp [h0]; field_simp
        by_cases h1 : μ.val = 1
        · simp [h0, h1]; field_simp
        by_cases h2 : μ.val = 2
        · simp [h0, h1, h2]; field_simp
        · simp [h0, h1, h2]; field_simp
      · intros α _ hα
        unfold rnGinv
        simp [Ne.symm hα]
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · rw [if_neg hμν]
      apply Finset.sum_eq_zero
      intros α _
      by_cases hαμ : α = μ
      · subst hαμ
        unfold rnG
        have hne : α ≠ ν := hμν
        simp [hne]
      · unfold rnGinv
        have hne : μ ≠ α := fun heq => hαμ heq.symm
        simp [hne]
  dg_symm := fun l x _ μ ν => rnDg_symm M Q l x μ ν

/-- The statement of `rnLapse_schwarzschild`: at `Q = 0` and `r > 0`, the
lapse is `1 − 2M/r`. -/
theorem rnPartial_lapse_schwarzschild (M r : ℝ) (hr : r > 0) :
    rnLapse M 0 r = 1 - 2 * M / r :=
  rnLapse_schwarzschild M r hr

end Curvature
end InfraFormalization
