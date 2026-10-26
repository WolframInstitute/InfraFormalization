/-
The de Sitter metric in static coordinates.

The module defines the components of
`ds² = -(1 - Λr²/3) dt² + (1 - Λr²/3)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`, their inverse,
a table of first partial derivatives, and the static-patch validity domain, and packages
them as `PartialMetricData 4`. It proves symmetry of each component table, that the inverse
is the matrix inverse on the validity domain, that the lapse equals 1 at `Λ = 0`, and that
for `Λ > 0` the lapse is positive exactly when `r² < 3/Λ`. The Einstein equations are not
checked in this module.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- The de Sitter lapse function `f(r) = 1 - Λr²/3`. -/
noncomputable def dsLapse (Λ r : ℝ) : ℝ :=
  1 - Λ * r^2 / 3

/-- The de Sitter metric components in static spherical coordinates `(t, r, θ, φ)`. -/
noncomputable def dsG (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -dsLapse Λ r
    else if μ.val = 1 then 1 / dsLapse Λ r
    else if μ.val = 2 then r^2
    else r^2 * (Real.sin θ)^2

/-- The diagonal reciprocal of `dsG`. -/
noncomputable def dsGinv (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -1 / dsLapse Λ r
    else if μ.val = 1 then dsLapse Λ r
    else if μ.val = 2 then 1 / r^2
    else 1 / (r^2 * (Real.sin θ)^2)

/-- The static-patch validity domain: `r > 0`, `dsLapse Λ r > 0` and `sin θ ≠ 0`. -/
def DSValid (Λ : ℝ) (x : Fin 4 → ℝ) : Prop :=
  x 1 > 0 ∧ dsLapse Λ (x 1) > 0 ∧ Real.sin (x 2) ≠ 0

/-- `dsLapse 0 r = 1`. -/
theorem dsLapse_minkowski (r : ℝ) :
    dsLapse 0 r = 1 := by
  unfold dsLapse
  ring

/-- `dsG` is symmetric. -/
theorem dsG_symm (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    dsG Λ x μ ν = dsG Λ x ν μ := by
  unfold dsG
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- `dsGinv` is symmetric. -/
theorem dsGinv_symm (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    dsGinv Λ x μ ν = dsGinv Λ x ν μ := by
  unfold dsGinv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- For `Λ > 0`, `dsLapse Λ r > 0` if and only if `r² < 3/Λ`. -/
theorem dsLapse_pos_iff (Λ : ℝ) (hΛ : Λ > 0) (r : ℝ) :
    dsLapse Λ r > 0 ↔ r^2 < 3 / Λ := by
  unfold dsLapse
  constructor
  · intro h
    have h1 : Λ * r^2 / 3 < 1 := by linarith
    have h2 : Λ * r^2 < 3 := by linarith
    rw [lt_div_iff₀ hΛ]
    linarith
  · intro h
    have h1 : Λ * r^2 < 3 := by
      rw [lt_div_iff₀ hΛ] at h
      linarith
    linarith

/-- A table of first partial derivatives `∂_l g_{μν}` of `dsG`, entered by hand; this
module does not prove that the entries are the derivatives of `dsG`. The non-zero entries:
  * `∂_r g_{00} = −f'(r)` where `f'(r) = −2Λr/3`
  * `∂_r g_{11} = −f'(r)/f(r)²`
  * `∂_r g_{22} = 2 r`
  * `∂_r g_{33} = 2 r sin²θ`
  * `∂_θ g_{33} = 2 r² sinθ cosθ`
-/
noncomputable def dsDg (Λ : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    let fp := -(2 * Λ * r / 3)
    if l.val = 1 then
      if μ.val = 0 then -fp
      else if μ.val = 1 then -fp / (dsLapse Λ r)^2
      else if μ.val = 2 then 2 * r
      else 2 * r * (Real.sin θ)^2
    else if l.val = 2 then
      if μ.val = 3 then 2 * r^2 * Real.sin θ * Real.cos θ
      else 0
    else 0

/-- `dsDg Λ l x μ ν = dsDg Λ l x ν μ`. -/
theorem dsDg_symm (Λ : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    dsDg Λ l x μ ν = dsDg Λ l x ν μ := by
  unfold dsDg
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- The de Sitter metric as `PartialMetricData 4` on the validity domain `DSValid Λ`. -/
noncomputable def dsPartial (Λ : ℝ) : PartialMetricData 4 where
  g := dsG Λ
  ginv := dsGinv Λ
  dg := dsDg Λ
  valid := DSValid Λ
  g_symm := fun x _ μ ν => dsG_symm Λ x μ ν
  ginv_symm := fun x _ μ ν => dsGinv_symm Λ x μ ν
  ginv_mul := by
    intros x hx μ ν
    obtain ⟨hr, hf, hsinθ⟩ := hx
    have hr_ne : x 1 ≠ 0 := ne_of_gt hr
    have hr_sq_ne : (x 1)^2 ≠ 0 := pow_ne_zero 2 hr_ne
    have hf_ne : dsLapse Λ (x 1) ≠ 0 := ne_of_gt hf
    have hsinθ_sq_ne : (Real.sin (x 2))^2 ≠ 0 := pow_ne_zero 2 hsinθ
    by_cases hμν : μ = ν
    · subst hμν
      rw [Finset.sum_eq_single μ]
      · rw [if_pos rfl]
        unfold dsGinv dsG
        simp only [ne_eq, not_true_eq_false, if_false]
        by_cases h0 : μ.val = 0
        · simp [h0]; field_simp
        by_cases h1 : μ.val = 1
        · simp [h0, h1]; field_simp
        by_cases h2 : μ.val = 2
        · simp [h0, h1, h2]; field_simp
        · simp [h0, h1, h2]; field_simp
      · intros α _ hα
        unfold dsGinv
        simp [Ne.symm hα]
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · rw [if_neg hμν]
      apply Finset.sum_eq_zero
      intros α _
      by_cases hαμ : α = μ
      · subst hαμ
        unfold dsG
        have hne : α ≠ ν := hμν
        simp [hne]
      · unfold dsGinv
        have hne : μ ≠ α := fun heq => hαμ heq.symm
        simp [hne]
  dg_symm := fun l x _ μ ν => dsDg_symm Λ l x μ ν

end Curvature
end InfraFormalization
