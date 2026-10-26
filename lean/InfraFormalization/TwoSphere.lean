/-
The round 2-sphere metric in polar coordinates.

This module defines the metric `ds² = dθ² + sin²θ dφ²` (with `x 0 = θ`),
its inverse and first partial derivatives, and packages them as a
`PartialMetricData 2` valid where `sin θ ≠ 0`. It computes the Christoffel
symbols `Γ⁰_{11} = −sin θ cos θ` and `Γ¹_{01} = cos θ / sin θ`, and proves
that `Γ¹_{01} ≠ 0` where `sin θ ≠ 0` and `cos θ ≠ 0`. No curvature tensor is
computed in this module.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- Metric components `g_{00} = 1`, `g_{11} = sin²θ`, off-diagonal 0, with
`x 0 = θ`. -/
noncomputable def sphereG (x : Fin 2 → ℝ) (μ ν : Fin 2) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then 1
  else (Real.sin (x 0))^2

/-- Inverse metric components `g^{00} = 1`, `g^{11} = 1/sin²θ`,
off-diagonal 0. -/
noncomputable def sphereGinv (x : Fin 2 → ℝ) (μ ν : Fin 2) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then 1
  else 1 / (Real.sin (x 0))^2

/-- First partial derivatives of the metric: `∂_0 g_{11} = 2 sin θ cos θ`
and all other components 0. -/
noncomputable def sphereDg (l : Fin 2) (x : Fin 2 → ℝ) (μ ν : Fin 2) : ℝ :=
  if μ ≠ ν then 0
  else if l.val = 0 ∧ μ.val = 1 then
    2 * Real.sin (x 0) * Real.cos (x 0)
  else 0

/-- The domain of validity: `sin θ ≠ 0`. -/
def SphereValid (x : Fin 2 → ℝ) : Prop :=
  Real.sin (x 0) ≠ 0

/-- `sphereG` is symmetric. -/
theorem sphereG_symm (x : Fin 2 → ℝ) (μ ν : Fin 2) :
    sphereG x μ ν = sphereG x ν μ := by
  unfold sphereG
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- `sphereGinv` is symmetric. -/
theorem sphereGinv_symm (x : Fin 2 → ℝ) (μ ν : Fin 2) :
    sphereGinv x μ ν = sphereGinv x ν μ := by
  unfold sphereGinv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- The 2-sphere metric as a `PartialMetricData 2` on `SphereValid`. -/
noncomputable def spherePartial : PartialMetricData 2 where
  g := sphereG
  ginv := sphereGinv
  dg := sphereDg
  valid := SphereValid
  g_symm := fun x _ μ ν => sphereG_symm x μ ν
  ginv_symm := fun x _ μ ν => sphereGinv_symm x μ ν
  ginv_mul := by
    intros x hx μ ν
    by_cases h : μ = ν
    · subst h
      rw [Finset.sum_eq_single μ]
      · rw [if_pos rfl]
        unfold sphereGinv sphereG
        simp only [ne_eq, not_true_eq_false, if_false]
        by_cases h0 : μ.val = 0
        · simp [h0]
        · have hs_ne : Real.sin (x 0) ≠ 0 := hx
          have hsq_ne : (Real.sin (x 0))^2 ≠ 0 := pow_ne_zero 2 hs_ne
          simp [h0]
          field_simp
      · intros α _ hα
        unfold sphereGinv
        simp [Ne.symm hα]
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intros α _
      by_cases hαμ : α = μ
      · subst hαμ
        unfold sphereG
        have hne : α ≠ ν := h
        simp [hne]
      · unfold sphereGinv
        have hne : μ ≠ α := fun heq => hαμ heq.symm
        simp [hne]
  dg_symm := by
    intros l x _ μ ν
    unfold sphereDg
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]

/-- `Γ⁰_{11}(x) = −sin θ cos θ`. -/
theorem sphereChristoffel_0_1_1 (x : Fin 2 → ℝ) :
    spherePartial.christoffel x 0 1 1 = -(Real.sin (x 0) * Real.cos (x 0)) := by
  unfold PartialMetricData.christoffel
  simp only [spherePartial, sphereGinv, sphereDg, sphereG]
  simp
  ring

/-- Where `sin θ ≠ 0`, `Γ¹_{01}(x) = cos θ / sin θ`. -/
theorem sphereChristoffel_1_0_1 (x : Fin 2 → ℝ) (hv : SphereValid x) :
    spherePartial.christoffel x 1 0 1 = Real.cos (x 0) / Real.sin (x 0) := by
  unfold PartialMetricData.christoffel
  simp only [spherePartial, sphereGinv, sphereDg, sphereG]
  have hs : Real.sin (x 0) ≠ 0 := hv
  have hsq : (Real.sin (x 0))^2 ≠ 0 := pow_ne_zero 2 hs
  simp
  field_simp

/-- Where `sin θ ≠ 0` and `cos θ ≠ 0`, `Γ¹_{01}(x) ≠ 0`. Nonzero Christoffel
symbols do not by themselves imply nonzero curvature. -/
theorem sphereChristoffel_nonzero (x : Fin 2 → ℝ) (hv : SphereValid x)
    (hc : Real.cos (x 0) ≠ 0) :
    spherePartial.christoffel x 1 0 1 ≠ 0 := by
  rw [sphereChristoffel_1_0_1 x hv]
  have hs : Real.sin (x 0) ≠ 0 := hv
  exact div_ne_zero hc hs

end Curvature
end InfraFormalization
