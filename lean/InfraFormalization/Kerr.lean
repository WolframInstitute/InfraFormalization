/-
**Kerr metric — rotating black hole** (B9 / #29).

In Boyer-Lindquist coordinates `(t, r, θ, φ)` with mass M and spin
parameter a:

  `Σ = r² + a² cos²θ`
  `Δ = r² − 2Mr + a²`

  `ds² = -(1 − 2Mr/Σ) dt² + (Σ/Δ) dr² + Σ dθ²`
  `    + (r² + a² + 2Ma²r sin²θ / Σ) sin²θ dφ²`
  `    − (4Mar sin²θ / Σ) dt dφ`

**Non-diagonal** — the `dt dφ` cross term is essential and represents
frame dragging. Horizons at `Δ = 0`, i.e. `r = M ± √(M² − a²)`.
Ergosphere at `Σ = 2Mr`. Validity: `Σ > 0 ∧ Δ > 0 ∧ sin θ ≠ 0`.

Reduces to Schwarzschild when `a = 0`. This file provides the
metric components + validity predicate as a target for B9 / future
Kerr-vacuum proof.

**Connection to hypergraphs.** Same anchor: continuum-target side.
The Kerr rule-origin claim (JGORARD et al.) is currently unsupported.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- **Boyer-Lindquist sigma function** `Σ = r² + a² cos²θ`. -/
noncomputable def kerrSigma (a : ℝ) (r θ : ℝ) : ℝ :=
  r^2 + a^2 * (Real.cos θ)^2

/-- **Boyer-Lindquist delta function** `Δ = r² − 2Mr + a²`. -/
noncomputable def kerrDelta (M a : ℝ) (r : ℝ) : ℝ :=
  r^2 - 2 * M * r + a^2

/-- **Kerr metric components** in Boyer-Lindquist coordinates. Has
both diagonal and `dt dφ` off-diagonal parts. -/
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

/-- **Kerr validity predicate**: outside the outer horizon and off
the axis. -/
def KerrValid (M a : ℝ) (x : Fin 4 → ℝ) : Prop :=
  kerrSigma a (x 1) (x 2) > 0 ∧
  kerrDelta M a (x 1) > 0 ∧
  Real.sin (x 2) ≠ 0

/-- **Kerr reduces to Schwarzschild when `a = 0`.** At spin zero:
`Σ(0, r, θ) = r²`, `Δ(M, 0, r) = r² - 2Mr = r(r - 2M)`.

Shown at the lapse-function level: `1 - 2Mr/Σ = 1 - 2M/r` for `a = 0`. -/
theorem kerrSigma_zero_spin (r θ : ℝ) : kerrSigma 0 r θ = r^2 := by
  unfold kerrSigma
  ring

theorem kerrDelta_zero_spin (M r : ℝ) : kerrDelta M 0 r = r^2 - 2*M*r := by
  unfold kerrDelta
  ring

/-- **Kerr metric is symmetric.** The diagonal is symmetric by
`if μ = ν` (commutative). The `dt dφ` = `dφ dt` cross term is
explicitly symmetric. -/
theorem kerrG_symm (M a : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    kerrG M a x μ ν = kerrG M a x ν μ := by
  unfold kerrG
  -- Case analysis on all four possible (μ, ν) pairs.
  by_cases h1 : μ = ν
  · rw [h1]
  · fin_cases μ <;> fin_cases ν <;> simp_all

/-- **Kerr sigma positivity**: at any `r, θ`, `Σ > 0` whenever
`r ≠ 0 ∨ a cos θ ≠ 0`. In particular `Σ > 0` whenever `r > 0`. -/
theorem kerrSigma_pos_of_r_pos (a r θ : ℝ) (hr : r > 0) :
    kerrSigma a r θ > 0 := by
  unfold kerrSigma
  have h1 : r^2 > 0 := by positivity
  have h2 : a^2 * (Real.cos θ)^2 ≥ 0 := by positivity
  linarith

/-- **Kerr at `a = 0` is Schwarzschild in spherical coordinates on the
diagonal `tt` component.** At spin zero, `Σ = r²`, so
`kerrG 0 x 0 0 = -(1 - 2M/r)`, matching Schwarzschild's `sgg M x 0 0`. -/
theorem kerrG_00_zero_spin (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 > 0) :
    kerrG M 0 x ⟨0, by decide⟩ ⟨0, by decide⟩ = -(1 - 2 * M / x 1) := by
  unfold kerrG
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr
  have hr_sq_ne : (x 1)^2 ≠ 0 := pow_ne_zero 2 hr_ne
  simp only [kerrSigma_zero_spin]
  simp
  field_simp

/-- **Kerr off-diagonal vanishes at `a = 0`.** The `tt-φφ` cross-term
is proportional to `a`, so it vanishes when the spin is zero — Kerr
reduces to a diagonal metric. -/
theorem kerrG_tφ_zero_spin (M : ℝ) (x : Fin 4 → ℝ) :
    kerrG M 0 x ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 := by
  unfold kerrG
  simp

/-- **Kerr θθ component at `a = 0`**: `kerrG 0 x 2 2 = r²`. -/
theorem kerrG_θθ_zero_spin (M : ℝ) (x : Fin 4 → ℝ) :
    kerrG M 0 x ⟨2, by decide⟩ ⟨2, by decide⟩ = (x 1)^2 := by
  unfold kerrG
  simp [kerrSigma_zero_spin]

end Curvature
end InfraFormalization
