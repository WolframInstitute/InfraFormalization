/-
The spatially flat FLRW metric.

The module defines the metric `ds² = -dt² + a(t)² (dx² + dy² + dz²)` on ℝ⁴ as a
`PartialMetricData 4` valid where `a(t) ≠ 0`. The function `da` supplied for
the derivative data is arbitrary and is not required to be the derivative of
`a`. The module proves the Lorentzian sign pattern where `a(t) ≠ 0` and computes
the Christoffel symbols `Γ⁰₀₀ = 0`, `Γ⁰ᵢᵢ = a · da` and `Γⁱ₀ᵢ = da / a` for
`i = 1, 2, 3`, and `Γ¹₁₁ = 0`. No hypergraph appears in this module.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- The diagonal metric with `g₀₀ = -1`, `gᵢᵢ = a(x 0)²` for `i = 1, 2, 3`, and
zero off-diagonal entries. -/
noncomputable def flrwG (a : ℝ → ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then -1
  else (a (x 0))^2

/-- The diagonal array with `g^{00} = -1` and `g^{ii} = 1/a(x 0)²`. -/
noncomputable def flrwGinv (a : ℝ → ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then -1
  else 1 / (a (x 0))^2

/-- The derivative data `∂_l g_{μν}`: the entry `∂₀ gᵢᵢ` for `i ≥ 1` is
`2 · a(x 0) · da(x 0)` and every other entry is 0. The function `da` is a
parameter. -/
noncomputable def flrwDg (a da : ℝ → ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else if l.val = 0 ∧ μ.val ≠ 0 then 2 * a (x 0) * da (x 0)
  else 0

/-- `a(x 0) ≠ 0`. -/
def FLRWValid (a : ℝ → ℝ) (x : Fin 4 → ℝ) : Prop :=
  a (x 0) ≠ 0

/-- `flrwG`, `flrwGinv` and `flrwDg` as a `PartialMetricData 4` with validity
predicate `FLRWValid a`. -/
noncomputable def flrwPartial (a da : ℝ → ℝ) : PartialMetricData 4 where
  g := flrwG a
  ginv := flrwGinv a
  dg := flrwDg a da
  valid := FLRWValid a
  g_symm := by
    intros x _ μ ν
    unfold flrwG
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]
  ginv_symm := by
    intros x _ μ ν
    unfold flrwGinv
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]
  ginv_mul := by
    intros x hx μ ν
    by_cases h : μ = ν
    · subst h
      rw [Finset.sum_eq_single μ]
      · rw [if_pos rfl]
        unfold flrwGinv flrwG
        simp only [ne_eq, not_true_eq_false, if_false]
        by_cases h0 : μ.val = 0
        · simp [h0]
        · have ha_ne : a (x 0) ≠ 0 := hx
          have hsq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero 2 ha_ne
          simp [h0]
          field_simp
      · intros α _ hα
        unfold flrwGinv
        simp [Ne.symm hα]
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intros α _
      by_cases hαμ : α = μ
      · subst hαμ
        unfold flrwG
        have hne : α ≠ ν := h
        simp [hne]
      · unfold flrwGinv
        have hne : μ ≠ α := fun heq => hαμ heq.symm
        simp [hne]
  dg_symm := by
    intros l x _ μ ν
    unfold flrwDg
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]

/-- `Γ⁰₀₀ = 0` at every point. Every derivative entry `∂_l g_{μ0}` is 0. -/
theorem flrwChristoffel_0_00 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwPartial a da).christoffel x 0 0 0 = 0 := by
  unfold PartialMetricData.christoffel
  simp only [flrwPartial]
  -- Every flrwDg term with ν = 0 vanishes.
  have h_dg_μ0 : ∀ l μ : Fin 4,
      flrwDg a da l x μ 0 = 0 := by
    intro l μ
    unfold flrwDg
    by_cases hμ : μ = 0
    · subst hμ; simp
    · simp [hμ]
  have h_sum : (∑ σ : Fin 4, flrwGinv a x 0 σ
      * (flrwDg a da 0 x σ 0 + flrwDg a da 0 x σ 0 - flrwDg a da σ x 0 0)) = 0 := by
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    rw [h_dg_μ0 0 σ, h_dg_μ0 σ 0]
    ring
  rw [h_sum]; ring

/-- If `a(x 0) ≠ 0`, then `g₀₀ < 0`, `gᵢᵢ > 0` for `i ≥ 1`, and the
off-diagonal entries are 0 at `x`. -/
theorem flrwG_lorentzian_pointwise (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    flrwG a x 0 0 < 0
    ∧ (∀ i : Fin 4, 0 < i.val → 0 < flrwG a x i i)
    ∧ (∀ μ ν : Fin 4, μ ≠ ν → flrwG a x μ ν = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- g_00 = -1 < 0.
    unfold flrwG
    simp
  · -- g_ii = a(t)^2 > 0.
    intro i hi
    unfold flrwG
    have hi_ne_zero : i.val ≠ 0 := Nat.pos_iff_ne_zero.mp hi
    simp [hi_ne_zero]
    have ha : a (x 0) ≠ 0 := hv
    have h_sq_pos : 0 < (a (x 0))^2 := by positivity
    exact h_sq_pos
  · -- off-diagonal zero.
    intros μ ν h
    unfold flrwG
    simp [h]

/-- `Γ^ρ_{μν} = ½ · g^{ρρ} · (∂_μ g_{ρν} + ∂_ν g_{ρμ} − ∂_ρ g_{μν})`. The sum
over `σ` reduces to `σ = ρ` because `flrwGinv` is diagonal. -/
theorem flrwChristoffel_collapse (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) :
    (flrwPartial a da).christoffel x ρ μ ν
      = (1 / 2) * flrwGinv a x ρ ρ *
          (flrwDg a da μ x ρ ν + flrwDg a da ν x ρ μ - flrwDg a da ρ x μ ν) := by
  unfold PartialMetricData.christoffel
  simp only [flrwPartial]
  rw [Finset.sum_eq_single ρ]
  · ring
  · intros σ _ hσ
    have : flrwGinv a x ρ σ = 0 := by
      unfold flrwGinv
      simp [Ne.symm hσ]
    rw [this, zero_mul]
  · intro hne
    exact absurd (Finset.mem_univ _) hne

/-- `Γ⁰₁₁ = a(x 0) · da(x 0)`. -/
theorem flrwChristoffel_0_11 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwPartial a da).christoffel x 0 1 1 = a (x 0) * da (x 0) := by
  rw [flrwChristoffel_collapse]
  -- ginv_00 = -1; dg terms: ∂_1 g_{01} + ∂_1 g_{01} - ∂_0 g_{11}
  -- = 0 + 0 - 2 a da
  unfold flrwGinv flrwDg
  simp
  ring

/-- If `a(x 0) ≠ 0`, then `Γ¹₀₁ = da(x 0) / a(x 0)`. When `da` is the
derivative of `a`, this is the Hubble rate. -/
theorem flrwChristoffel_1_01 (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwPartial a da).christoffel x 1 0 1 = da (x 0) / a (x 0) := by
  rw [flrwChristoffel_collapse]
  unfold flrwGinv flrwDg
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero 2 ha_ne
  simp
  field_simp

/-- `Γ¹₁₁ = 0`. -/
theorem flrwChristoffel_1_11 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwPartial a da).christoffel x 1 1 1 = 0 := by
  rw [flrwChristoffel_collapse]
  unfold flrwGinv flrwDg
  simp

/-- `Γ⁰₂₂ = a(x 0) · da(x 0)`. -/
theorem flrwChristoffel_0_22 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwPartial a da).christoffel x 0 2 2 = a (x 0) * da (x 0) := by
  rw [flrwChristoffel_collapse]
  unfold flrwGinv flrwDg
  simp
  ring

/-- `Γ⁰₃₃ = a(x 0) · da(x 0)`. -/
theorem flrwChristoffel_0_33 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwPartial a da).christoffel x 0 3 3 = a (x 0) * da (x 0) := by
  rw [flrwChristoffel_collapse]
  unfold flrwGinv flrwDg
  simp
  ring

/-- If `a(x 0) ≠ 0`, then `Γ²₀₂ = da(x 0) / a(x 0)`. -/
theorem flrwChristoffel_2_02 (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwPartial a da).christoffel x 2 0 2 = da (x 0) / a (x 0) := by
  rw [flrwChristoffel_collapse]
  unfold flrwGinv flrwDg
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero 2 ha_ne
  simp
  field_simp

/-- If `a(x 0) ≠ 0`, then `Γ³₀₃ = da(x 0) / a(x 0)`. -/
theorem flrwChristoffel_3_03 (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwPartial a da).christoffel x 3 0 3 = da (x 0) / a (x 0) := by
  rw [flrwChristoffel_collapse]
  unfold flrwGinv flrwDg
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero 2 ha_ne
  simp
  field_simp

end Curvature
end InfraFormalization
