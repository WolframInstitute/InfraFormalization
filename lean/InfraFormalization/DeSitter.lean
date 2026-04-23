/-
**de Sitter metric** — positive-Λ vacuum solution.

In static coordinates on the patch `r < √(3/Λ)` (inside the
cosmological horizon):

  `ds² = -(1 - Λr²/3) dt² + (1 - Λr²/3)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`

This is the vacuum solution to the Einstein field equations with a
positive cosmological constant Λ > 0. Limit Λ → 0 gives Minkowski
(in static spherical coordinates = Schwarzschild at M = 0).

This is the formal continuum-target that `minkowski4_flat_vacuum_forces_lambda_zero`
disproves for Minkowski + flat: non-zero Λ requires genuinely curved
geometry, which de Sitter supplies.

**Connection to hypergraphs.** Same anchor: continuum side. A
hypergraph rule producing exponentially expanding universe in some
limit would pair with this.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- **de Sitter lapse function** `f(r) = 1 - Λr²/3`. -/
noncomputable def dsLapse (Λ r : ℝ) : ℝ :=
  1 - Λ * r^2 / 3

/-- **de Sitter metric components** in static spherical coordinates. -/
noncomputable def dsG (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -dsLapse Λ r
    else if μ.val = 1 then 1 / dsLapse Λ r
    else if μ.val = 2 then r^2
    else r^2 * (Real.sin θ)^2

/-- **de Sitter inverse metric**: diagonal reciprocal of `dsG`. -/
noncomputable def dsGinv (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -1 / dsLapse Λ r
    else if μ.val = 1 then dsLapse Λ r
    else if μ.val = 2 then 1 / r^2
    else 1 / (r^2 * (Real.sin θ)^2)

/-- **de Sitter validity** (static patch): `r > 0`, `dsLapse > 0`
(inside the cosmological horizon), `sin θ ≠ 0` (off the axis). -/
def DSValid (Λ : ℝ) (x : Fin 4 → ℝ) : Prop :=
  x 1 > 0 ∧ dsLapse Λ (x 1) > 0 ∧ Real.sin (x 2) ≠ 0

/-- **de Sitter lapse at Λ = 0 is Minkowski**: `dsLapse 0 r = 1`. -/
theorem dsLapse_minkowski (r : ℝ) :
    dsLapse 0 r = 1 := by
  unfold dsLapse
  ring

/-- **de Sitter metric symmetry.** -/
theorem dsG_symm (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    dsG Λ x μ ν = dsG Λ x ν μ := by
  unfold dsG
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- **de Sitter inverse metric symmetry.** -/
theorem dsGinv_symm (Λ : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    dsGinv Λ x μ ν = dsGinv Λ x ν μ := by
  unfold dsGinv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- **Cosmological horizon location for Λ > 0**: `dsLapse Λ r > 0`
iff `r² < 3/Λ`, i.e., `r < √(3/Λ)`. -/
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

end Curvature
end InfraFormalization
