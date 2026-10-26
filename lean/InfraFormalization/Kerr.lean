/-
Kerr metric in Boyer–Lindquist coordinates.

With coordinates `(t, r, θ, φ)`, mass `M` and spin `a`, `Σ = r² + a² cos²θ` and
`Δ = r² − 2Mr + a²`, the metric is

  `ds² = -(1 − 2Mr/Σ) dt² + (Σ/Δ) dr² + Σ dθ² + (r² + a² + 2Ma²r sin²θ / Σ) sin²θ dφ²`
  `      − (4Mar sin²θ / Σ) dt dφ`.

This module defines `Σ`, `Δ`, the metric components `kerrG` and the predicate `KerrValid`. It proves
that `kerrG` is symmetric and that at `a = 0` the `tt`, `tφ` and `θθ` components equal
`-(1 - 2M/r)`, 0 and `r²`. The vacuum Einstein equations for Kerr are not proved here.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- `Σ = r² + a² cos²θ`. -/
noncomputable def kerrSigma (a : ℝ) (r θ : ℝ) : ℝ :=
  r^2 + a^2 * (Real.cos θ)^2

/-- `Δ = r² − 2Mr + a²`. -/
noncomputable def kerrDelta (M a : ℝ) (r : ℝ) : ℝ :=
  r^2 - 2 * M * r + a^2

/-- The Kerr metric components in Boyer–Lindquist coordinates, including the `tφ` cross term. -/
noncomputable def kerrG (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  let r := x 1
  let θ := x 2
  let sg := kerrSigma a r θ
  let dl := kerrDelta M a r
  if μ = ⟨0, by decide⟩ ∧ ν = ⟨0, by decide⟩ then -(1 - 2 * M * r / sg)
  else if μ = ⟨1, by decide⟩ ∧ ν = ⟨1, by decide⟩ then sg / dl
  else if μ = ⟨2, by decide⟩ ∧ ν = ⟨2, by decide⟩ then sg
  else if μ = ⟨3, by decide⟩ ∧ ν = ⟨3, by decide⟩ then
    (r^2 + a^2 + 2 * M * a^2 * r * (Real.sin θ)^2 / sg) * (Real.sin θ)^2
  else if (μ = ⟨0, by decide⟩ ∧ ν = ⟨3, by decide⟩) ∨
          (μ = ⟨3, by decide⟩ ∧ ν = ⟨0, by decide⟩) then
    -(2 * M * a * r * (Real.sin θ)^2 / sg)
  else 0

/-- `Σ > 0`, `Δ > 0` and `sin θ ≠ 0` at the point `x`. The condition `Δ > 0` holds outside the
outer horizon and inside the inner horizon. -/
def KerrValid (M a : ℝ) (x : Fin 4 → ℝ) : Prop :=
  kerrSigma a (x 1) (x 2) > 0 ∧
  kerrDelta M a (x 1) > 0 ∧
  Real.sin (x 2) ≠ 0

/-- At `a = 0`, `Σ = r²`. -/
theorem kerrSigma_zero_spin (r θ : ℝ) : kerrSigma 0 r θ = r^2 := by
  unfold kerrSigma
  ring

/-- At `a = 0`, `Δ = r² - 2Mr`. -/
theorem kerrDelta_zero_spin (M r : ℝ) : kerrDelta M 0 r = r^2 - 2*M*r := by
  unfold kerrDelta
  ring

/-- `kerrG M a x μ ν = kerrG M a x ν μ`. -/
theorem kerrG_symm (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    kerrG M a x μ ν = kerrG M a x ν μ := by
  unfold kerrG
  -- Case analysis on all four possible (μ, ν) pairs.
  by_cases h1 : μ = ν
  · rw [h1]
  · fin_cases μ <;> fin_cases ν <;> simp_all

/-- If `r > 0`, then `Σ > 0`. -/
theorem kerrSigma_pos_of_r_pos (a r θ : ℝ) (hr : r > 0) :
    kerrSigma a r θ > 0 := by
  unfold kerrSigma
  have h1 : r^2 > 0 := by positivity
  have h2 : a^2 * (Real.cos θ)^2 ≥ 0 := by positivity
  linarith

/-- For `a = 0` and `r > 0`, the `tt` component equals `-(1 - 2M/r)`, the Schwarzschild value. -/
theorem kerrG_00_zero_spin (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 > 0) :
    kerrG M 0 x ⟨0, by decide⟩ ⟨0, by decide⟩ = -(1 - 2 * M / x 1) := by
  unfold kerrG
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr
  have hr_sq_ne : (x 1)^2 ≠ 0 := pow_ne_zero 2 hr_ne
  simp only [kerrSigma_zero_spin]
  simp
  field_simp

/-- For `a = 0`, the `tφ` component is 0. -/
theorem kerrG_tφ_zero_spin (M : ℝ) (x : Fin 4 → ℝ) :
    kerrG M 0 x ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 := by
  unfold kerrG
  simp

/-- For `a = 0`, the `θθ` component equals `r²`. -/
theorem kerrG_θθ_zero_spin (M : ℝ) (x : Fin 4 → ℝ) :
    kerrG M 0 x ⟨2, by decide⟩ ⟨2, by decide⟩ = (x 1)^2 := by
  unfold kerrG
  simp [kerrSigma_zero_spin]

end Curvature
end InfraFormalization
