/-
The Schwarzschild metric in coordinates.

This module defines the components `sgg`, `sginv` and `sdg` of the
Schwarzschild metric, its inverse and its first partial derivatives in
coordinates `(t, r, θ, φ)`, and the region `SchwarzschildValid M`
(`r > 2M`, `r > 0`, `sin θ ≠ 0`). It proves `g^{μα} g_{αν} = δ^μ_ν` on
that region, computes the nine nonzero Christoffel symbols up to
lower-index symmetry, packages the metric as a `PartialMetricData 4`, and
proves that the metric is diagonal with signature (−, +, +, +) on the
region. No definition in this module involves a hypergraph.
-/

import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann
import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- Metric components in coordinates `(t, r, θ, φ)`: `g_{00} = −(1 − 2M/r)`,
`g_{11} = 1/(1 − 2M/r)`, `g_{22} = r²`, `g_{33} = r² sin²θ`, off-diagonal 0. -/
noncomputable def sgg (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -(1 - 2 * M / r)
    else if μ.val = 1 then 1 / (1 - 2 * M / r)
    else if μ.val = 2 then r^2
    else r^2 * (Real.sin θ)^2

/-- Inverse metric components: the reciprocals of the diagonal components
of `sgg`, off-diagonal 0. -/
noncomputable def sginv (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -1 / (1 - 2 * M / r)
    else if μ.val = 1 then 1 - 2 * M / r
    else if μ.val = 2 then 1 / r^2
    else 1 / (r^2 * (Real.sin θ)^2)

/-- First partial derivatives `∂_l g_{μν}`. They are nonzero only for
`l = 1` on diagonal components and for `l = 2` on `g_{33}`. -/
noncomputable def sdg (M : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if l.val = 1 then
      if μ.val = 0 then -(2 * M / r^2)
      else if μ.val = 1 then -(2 * M / r^2) / (1 - 2 * M / r)^2
      else if μ.val = 2 then 2 * r
      else 2 * r * (Real.sin θ)^2
    else if l.val = 2 then
      if μ.val = 3 then 2 * r^2 * Real.sin θ * Real.cos θ
      else 0
    else 0

/-- `r > 2M`, `r > 0` and `sin θ ≠ 0`. -/
def SchwarzschildValid (M : ℝ) (x : Fin 4 → ℝ) : Prop :=
  x 1 > 2 * M ∧ x 1 > 0 ∧ Real.sin (x 2) ≠ 0

/-- `sgg` is symmetric. -/
theorem sgg_symm (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    sgg M x μ ν = sgg M x ν μ := by
  unfold sgg
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- `sginv` is symmetric. -/
theorem sginv_symm (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    sginv M x μ ν = sginv M x ν μ := by
  unfold sginv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- `sdg l x μ ν = sdg l x ν μ`. -/
theorem sdg_symm (M : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    sdg M l x μ ν = sdg M l x ν μ := by
  unfold sdg
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- On `SchwarzschildValid M`, `g^{μμ} g_{μμ} = 1` for every `μ`. -/
theorem sginv_mul_sgg_diagonal {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) (μ : Fin 4) :
    sginv M x μ μ * sgg M x μ μ = 1 := by
  unfold sginv sgg
  simp only [ne_eq, not_true_eq_false, if_false]
  obtain ⟨hr_gt_2M, hr_pos, hsinθ⟩ := hx
  have hr_ne_zero : x 1 ≠ 0 := ne_of_gt hr_pos
  have h_one_minus : (1 - 2 * M / x 1) ≠ 0 := by
    intro heq
    have : 1 = 2 * M / x 1 := by linarith
    have : x 1 = 2 * M := by
      rw [eq_comm, div_eq_iff hr_ne_zero] at this
      linarith
    linarith
  have h_r_minus_2M_ne : x 1 - 2 * M ≠ 0 := by
    intro heq
    have : x 1 = 2 * M := by linarith
    linarith
  fin_cases μ
  · -- μ = 0: (-1/(1 - 2M/r)) · (-(1 - 2M/r)) = 1.
    simp only [Fin.val_zero, if_true, if_false]
    field_simp
  · -- μ = 1: (1 - 2M/r) · (1/(1 - 2M/r)) = 1.
    simp only [Fin.val_one, if_true, if_false, reduceCtorEq]
    field_simp
  · -- μ = 2: (1/r²) · r² = 1.
    have hne1 : (2 : ℕ) ≠ 1 := by decide
    simp only [if_true, if_false, reduceCtorEq, hne1, if_neg hne1]
    have hr_sq : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne_zero
    field_simp
  · -- μ = 3: (1/(r² sin²θ)) · (r² sin²θ) = 1.
    have hne1 : (3 : ℕ) ≠ 1 := by decide
    have hne2 : (3 : ℕ) ≠ 2 := by decide
    simp only [if_true, if_false, reduceCtorEq, if_neg hne1, if_neg hne2]
    have hr_sq : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne_zero
    have hsin_sq : (Real.sin (x 2))^2 ≠ 0 := pow_ne_zero _ hsinθ
    field_simp

/-- On `SchwarzschildValid M`, `∑_α g^{μα} g_{αν} = δ^μ_ν`. -/
theorem sginv_mul_sgg {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) (μ ν : Fin 4) :
    (∑ α : Fin 4, sginv M x μ α * sgg M x α ν)
    = if μ = ν then 1 else 0 := by
  by_cases h : μ = ν
  · subst h
    -- Diagonal: sum collapses at α = μ, value = 1.
    rw [Finset.sum_eq_single μ]
    · rw [if_pos rfl]
      exact sginv_mul_sgg_diagonal hx μ
    · intros α _ hα
      -- ginv μ α = 0 for α ≠ μ.
      unfold sginv
      simp [Ne.symm hα]
    · intro hne
      exact absurd (Finset.mem_univ μ) hne
  · -- Off-diagonal: all summands zero.
    rw [if_neg h]
    apply Finset.sum_eq_zero
    intros α _
    by_cases hαμ : α = μ
    · subst hαμ
      unfold sgg
      have hne : α ≠ ν := h
      simp [hne]
    · unfold sginv
      have hne : μ ≠ α := fun heq => hαμ heq.symm
      simp [hne]

/-! ## Christoffel symbols

The nonzero Christoffel symbols, up to lower-index symmetry, are

  Γ^0_{01} = M / (r(r−2M))
  Γ^1_{00} = M (r − 2M) / r³
  Γ^1_{11} = −M / (r(r−2M))
  Γ^1_{22} = −(r − 2M)
  Γ^1_{33} = −(r − 2M) sin²θ
  Γ^2_{12} = 1/r
  Γ^2_{33} = −sin θ cos θ
  Γ^3_{13} = 1/r
  Γ^3_{23} = cos θ / sin θ

Each is proved below on `SchwarzschildValid M`.
-/

/-- `Γ^ρ_{μν} = (1/2) ∑_σ g^{ρσ} (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})`. -/
noncomputable def schwarzschildChristoffel (M : ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) : ℝ :=
  (1 / 2) * ∑ σ : Fin 4,
    sginv M x ρ σ *
      (sdg M μ x σ ν + sdg M ν x σ μ - sdg M σ x μ ν)

/-- `Γ^ρ_{μν} = Γ^ρ_{νμ}`. -/
theorem schwarzschildChristoffel_symm (M : ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) :
    schwarzschildChristoffel M x ρ μ ν = schwarzschildChristoffel M x ρ ν μ := by
  unfold schwarzschildChristoffel
  congr 1
  apply Finset.sum_congr rfl
  intros σ _
  have h1 : sdg M μ x σ ν + sdg M ν x σ μ - sdg M σ x μ ν
          = sdg M ν x σ μ + sdg M μ x σ ν - sdg M σ x ν μ := by
    rw [sdg_symm M σ x μ ν]
    ring
  rw [h1]

/-- On `SchwarzschildValid M`, `Γ^1_{00} = M (r − 2M) / r³`. -/
theorem schwarzschildChristoffel_1_00 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨1, by decide⟩ : Fin 4)
                                 (⟨0, by decide⟩ : Fin 4)
                                 (⟨0, by decide⟩ : Fin 4)
    = M * (x 1 - 2 * M) / (x 1)^3 := by
  unfold schwarzschildChristoffel
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have hr_cube_ne : x 1 ^ 3 ≠ 0 := pow_ne_zero _ hr_ne
  -- Compute the three specific entries needed.
  have h_sginv_11 : sginv M x (⟨1, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4)
                  = 1 - 2 * M / x 1 := by
    unfold sginv
    simp
  have h_sdg_0_10 : sdg M (⟨0, by decide⟩ : Fin 4) x
                         (⟨1, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4) = 0 := by
    unfold sdg
    have h10ne : (⟨1, by decide⟩ : Fin 4) ≠ (⟨0, by decide⟩ : Fin 4) := by decide
    simp [h10ne]
  have h_sdg_1_00 : sdg M (⟨1, by decide⟩ : Fin 4) x
                         (⟨0, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4)
                  = -(2 * M / x 1^2) := by
    unfold sdg
    simp
  -- The sum over σ collapses to σ = 1.
  rw [Finset.sum_eq_single (⟨1, by decide⟩ : Fin 4)]
  · -- Only the σ = 1 summand. Compute directly.
    rw [h_sginv_11, h_sdg_0_10, h_sdg_1_00]
    field_simp
    ring
  · -- For α ≠ 1, sginv M x 1 α = 0.
    intros α _ hα
    have hne : (⟨1, by decide⟩ : Fin 4) ≠ α := fun heq => hα heq.symm
    have h_sginv_1α : sginv M x (⟨1, by decide⟩ : Fin 4) α = 0 := by
      unfold sginv
      rw [if_pos hne]
    rw [h_sginv_1α]
    ring
  · intro hne
    exact absurd (Finset.mem_univ _) hne

/-! ### Off-diagonal components of `sginv` vanish -/

theorem sginv_off_diag {M : ℝ} {x : Fin 4 → ℝ} {ρ σ : Fin 4} (h : ρ ≠ σ) :
    sginv M x ρ σ = 0 := by
  unfold sginv
  rw [if_pos h]

/-! ### Off-diagonal components of `sdg` vanish -/

theorem sdg_off_diag {M : ℝ} {l : Fin 4} {x : Fin 4 → ℝ} {μ ν : Fin 4}
    (h : μ ≠ ν) : sdg M l x μ ν = 0 := by
  unfold sdg
  rw [if_pos h]

/-! ### Values of `sdg` -/

/-- `∂_l g_{00}` is zero for `l ≠ 1`. -/
theorem sdg_l_00_eq_zero {M : ℝ} {x : Fin 4 → ℝ} {l : Fin 4} (hl : l.val ≠ 1) :
    sdg M l x (⟨0, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4) = 0 := by
  unfold sdg
  by_cases hl2 : l.val = 2
  · simp [hl, hl2]
  · simp [hl, hl2]

/-- `∂_1 g_{00} = -(2M/r²)`. -/
theorem sdg_1_00 {M : ℝ} (x : Fin 4 → ℝ) :
    sdg M (⟨1, by decide⟩ : Fin 4)
         x (⟨0, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4)
    = -(2 * M / x 1^2) := by
  unfold sdg
  simp

/-- `∂_1 g_{11} = -(2M/r²) / (1 - 2M/r)²`. -/
theorem sdg_1_11 {M : ℝ} (x : Fin 4 → ℝ) :
    sdg M (⟨1, by decide⟩ : Fin 4)
         x (⟨1, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4)
    = -(2 * M / x 1^2) / (1 - 2 * M / x 1)^2 := by
  unfold sdg
  simp

/-- `∂_1 g_{22} = 2r`. -/
theorem sdg_1_22 {M : ℝ} (x : Fin 4 → ℝ) :
    sdg M (⟨1, by decide⟩ : Fin 4)
         x (⟨2, by decide⟩ : Fin 4) (⟨2, by decide⟩ : Fin 4)
    = 2 * x 1 := by
  unfold sdg
  simp

/-- `∂_1 g_{33} = 2r sin²θ`. -/
theorem sdg_1_33 {M : ℝ} (x : Fin 4 → ℝ) :
    sdg M (⟨1, by decide⟩ : Fin 4)
         x (⟨3, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4)
    = 2 * x 1 * (Real.sin (x 2))^2 := by
  unfold sdg
  simp

/-- `∂_2 g_{33} = 2 r² sin θ cos θ`. -/
theorem sdg_2_33 {M : ℝ} (x : Fin 4 → ℝ) :
    sdg M (⟨2, by decide⟩ : Fin 4)
         x (⟨3, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4)
    = 2 * x 1^2 * Real.sin (x 2) * Real.cos (x 2) := by
  unfold sdg
  simp

/-! ### Values of `sginv` -/

theorem sginv_00 {M : ℝ} (x : Fin 4 → ℝ) :
    sginv M x (⟨0, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4)
    = -1 / (1 - 2 * M / x 1) := by
  unfold sginv
  simp

theorem sginv_11 {M : ℝ} (x : Fin 4 → ℝ) :
    sginv M x (⟨1, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4)
    = 1 - 2 * M / x 1 := by
  unfold sginv
  simp

theorem sginv_22 {M : ℝ} (x : Fin 4 → ℝ) :
    sginv M x (⟨2, by decide⟩ : Fin 4) (⟨2, by decide⟩ : Fin 4)
    = 1 / x 1^2 := by
  unfold sginv
  simp

theorem sginv_33 {M : ℝ} (x : Fin 4 → ℝ) :
    sginv M x (⟨3, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4)
    = 1 / (x 1^2 * (Real.sin (x 2))^2) := by
  unfold sginv
  simp

/-! ### Reduction of the Christoffel sum

Since `sginv` is diagonal, the sum over `σ` reduces to the term `σ = ρ`. -/

theorem schwarzschild_christoffel_collapse (M : ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) :
    schwarzschildChristoffel M x ρ μ ν
    = (1 / 2) * sginv M x ρ ρ *
      (sdg M μ x ρ ν + sdg M ν x ρ μ - sdg M ρ x μ ν) := by
  unfold schwarzschildChristoffel
  rw [Finset.sum_eq_single ρ]
  · ring
  · intros σ _ hσ
    rw [sginv_off_diag (Ne.symm hσ), zero_mul]
  · intro hne
    exact absurd (Finset.mem_univ _) hne

/-! ### The remaining Christoffel symbols

Each proof reduces the sum with `schwarzschild_christoffel_collapse`,
evaluates the partial derivatives, and finishes with `field_simp; ring`. -/

theorem schwarzschildChristoffel_0_01 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨0, by decide⟩ : Fin 4)
                                 (⟨0, by decide⟩ : Fin 4)
                                 (⟨1, by decide⟩ : Fin 4)
    = M / (x 1 * (x 1 - 2 * M)) := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have hrm2M_ne : x 1 - 2 * M ≠ 0 := by intro h; linarith
  have h_one_minus : (1 - 2 * M / x 1) ≠ 0 := by
    intro heq
    have h1 : 1 = 2 * M / x 1 := by linarith
    rw [eq_comm, div_eq_iff hr_ne] at h1
    linarith
  -- Three partials: sdg_0_01 = 0, sdg_1_00 = -(2M/r²), sdg_0_01 = 0.
  have h_sdg_0_01 :
      sdg M (⟨0, by decide⟩ : Fin 4) x
        (⟨0, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  rw [h_sdg_0_01, sdg_1_00, sginv_00]
  field_simp
  ring

theorem schwarzschildChristoffel_1_11 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨1, by decide⟩ : Fin 4)
                                 (⟨1, by decide⟩ : Fin 4)
                                 (⟨1, by decide⟩ : Fin 4)
    = - M / (x 1 * (x 1 - 2 * M)) := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have hrm2M_ne : x 1 - 2 * M ≠ 0 := by intro h; linarith
  have h_one_minus : (1 - 2 * M / x 1) ≠ 0 := by
    intro heq
    have h1 : 1 = 2 * M / x 1 := by linarith
    rw [eq_comm, div_eq_iff hr_ne] at h1
    linarith
  have h_one_sq : (1 - 2 * M / x 1)^2 ≠ 0 := pow_ne_zero _ h_one_minus
  rw [sdg_1_11, sginv_11]
  field_simp
  ring

theorem schwarzschildChristoffel_1_22 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨1, by decide⟩ : Fin 4)
                                 (⟨2, by decide⟩ : Fin 4)
                                 (⟨2, by decide⟩ : Fin 4)
    = - (x 1 - 2 * M) := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  -- sdg_2_12 = 0 (off-diag), sdg_2_12 = 0 (off-diag), sdg_1_22 = 2r.
  have h_sdg_2_12 :
      sdg M (⟨2, by decide⟩ : Fin 4) x
        (⟨1, by decide⟩ : Fin 4) (⟨2, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  rw [h_sdg_2_12, sdg_1_22, sginv_11]
  field_simp
  ring

theorem schwarzschildChristoffel_1_33 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨1, by decide⟩ : Fin 4)
                                 (⟨3, by decide⟩ : Fin 4)
                                 (⟨3, by decide⟩ : Fin 4)
    = - (x 1 - 2 * M) * (Real.sin (x 2))^2 := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have h_sdg_3_13 :
      sdg M (⟨3, by decide⟩ : Fin 4) x
        (⟨1, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  rw [h_sdg_3_13, sdg_1_33, sginv_11]
  field_simp
  ring

theorem schwarzschildChristoffel_2_12 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨2, by decide⟩ : Fin 4)
                                 (⟨1, by decide⟩ : Fin 4)
                                 (⟨2, by decide⟩ : Fin 4)
    = 1 / x 1 := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have h_sdg_2_22 :
      sdg M (⟨2, by decide⟩ : Fin 4) x
        (⟨2, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  have h_sdg_2_12 :
      sdg M (⟨2, by decide⟩ : Fin 4) x
        (⟨1, by decide⟩ : Fin 4) (⟨2, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  rw [h_sdg_2_22, h_sdg_2_12, sdg_1_22, sginv_22]
  field_simp
  ring

theorem schwarzschildChristoffel_2_33 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨2, by decide⟩ : Fin 4)
                                 (⟨3, by decide⟩ : Fin 4)
                                 (⟨3, by decide⟩ : Fin 4)
    = - Real.sin (x 2) * Real.cos (x 2) := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have h_sdg_3_23 :
      sdg M (⟨3, by decide⟩ : Fin 4) x
        (⟨2, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  rw [h_sdg_3_23, sdg_2_33, sginv_22]
  field_simp
  ring

theorem schwarzschildChristoffel_3_13 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨3, by decide⟩ : Fin 4)
                                 (⟨1, by decide⟩ : Fin 4)
                                 (⟨3, by decide⟩ : Fin 4)
    = 1 / x 1 := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, hsinθ⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have hsin_sq : (Real.sin (x 2))^2 ≠ 0 := pow_ne_zero _ hsinθ
  have h_sdg_3_33_13 :
      sdg M (⟨3, by decide⟩ : Fin 4) x
        (⟨3, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  have h_sdg_3_13 :
      sdg M (⟨3, by decide⟩ : Fin 4) x
        (⟨1, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  rw [h_sdg_3_33_13, h_sdg_3_13, sdg_1_33, sginv_33]
  field_simp
  ring

theorem schwarzschildChristoffel_3_23 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨3, by decide⟩ : Fin 4)
                                 (⟨2, by decide⟩ : Fin 4)
                                 (⟨3, by decide⟩ : Fin 4)
    = Real.cos (x 2) / Real.sin (x 2) := by
  rw [schwarzschild_christoffel_collapse]
  obtain ⟨hr_gt_2M, hr_pos, hsinθ⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have hsin_sq : (Real.sin (x 2))^2 ≠ 0 := pow_ne_zero _ hsinθ
  have h_sdg_3_33_23 :
      sdg M (⟨3, by decide⟩ : Fin 4) x
        (⟨3, by decide⟩ : Fin 4) (⟨2, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  have h_sdg_3_23 :
      sdg M (⟨3, by decide⟩ : Fin 4) x
        (⟨2, by decide⟩ : Fin 4) (⟨3, by decide⟩ : Fin 4) = 0 :=
    sdg_off_diag (by decide)
  rw [h_sdg_3_33_23, h_sdg_3_23, sdg_2_33, sginv_33]
  field_simp
  ring

/-! ## `PartialMetricData` -/

/-- The Schwarzschild metric as a `PartialMetricData 4` with domain
`SchwarzschildValid M`. -/
noncomputable def schwarzschildPartial (M : ℝ) : PartialMetricData 4 where
  g := sgg M
  ginv := sginv M
  dg := sdg M
  valid := SchwarzschildValid M
  g_symm := fun x _ μ ν => sgg_symm M x μ ν
  ginv_symm := fun x _ μ ν => sginv_symm M x μ ν
  ginv_mul := fun x hx μ ν => sginv_mul_sgg hx μ ν
  dg_symm := fun l x _ μ ν => sdg_symm M l x μ ν

/-- The Christoffel symbols of `schwarzschildPartial M` are
`schwarzschildChristoffel M`, by `rfl`. -/
theorem schwarzschildPartial_christoffel (M : ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) :
    (schwarzschildPartial M).christoffel x ρ μ ν
      = schwarzschildChristoffel M x ρ μ ν := by
  unfold PartialMetricData.christoffel schwarzschildChristoffel schwarzschildPartial
  rfl

/-- On `SchwarzschildValid M`, `g_{00} < 0`, `g_{ii} > 0` for `i ≥ 1`, and
the off-diagonal components are 0. -/
theorem sgg_lorentzian_pointwise (M : ℝ) (x : Fin 4 → ℝ)
    (hv : SchwarzschildValid M x) :
    sgg M x 0 0 < 0
    ∧ (∀ i : Fin 4, 0 < i.val → 0 < sgg M x i i)
    ∧ (∀ μ ν : Fin 4, μ ≠ ν → sgg M x μ ν = 0) := by
  obtain ⟨hr_gt_2M, hr_pos, hsinθ⟩ := hv
  have hr_ne_zero : x 1 ≠ 0 := ne_of_gt hr_pos
  have h_factor_pos : 0 < 1 - 2 * M / (x 1) := by
    have : 1 - 2 * M / (x 1) = (x 1 - 2 * M) / (x 1) := by field_simp
    rw [this]
    exact div_pos (by linarith) hr_pos
  have h_factor_ne : (1 : ℝ) - 2 * M / x 1 ≠ 0 := ne_of_gt h_factor_pos
  refine ⟨?_, ?_, ?_⟩
  · -- g_00 = -(1 - 2M/r) < 0.
    unfold sgg
    simp
    linarith
  · -- g_ii > 0 for i ≥ 1.
    intro i hi
    unfold sgg
    have hi_ne_zero : i.val ≠ 0 := Nat.pos_iff_ne_zero.mp hi
    simp [hi_ne_zero]
    fin_cases i
    · exact absurd rfl hi_ne_zero
    · simp
      -- Need 2M/r < 1, equivalent to r > 2M.
      rw [div_lt_one hr_pos]
      linarith
    · simp; positivity
    · simp
      have h_sq_sin_pos : 0 < (Real.sin (x 2))^2 := by positivity
      positivity
  · -- off-diagonal zero.
    intros μ ν h
    unfold sgg
    simp [h]

end Curvature
end InfraFormalization
