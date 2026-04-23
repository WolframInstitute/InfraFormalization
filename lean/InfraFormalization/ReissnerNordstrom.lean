/-
**Reissner-Nordström metric** (B8 / #28).

The Reissner-Nordström metric describes a charged, non-rotating black
hole:

  `ds² = -(1 - 2M/r + Q²/r²) dt² + 1/(1 - 2M/r + Q²/r²) dr²
         + r² dθ² + r² sin²θ dφ²`

The horizons are at `r = M ± √(M² − Q²)`. For `Q = 0` this reduces to
Schwarzschild. The exterior region (outside the outer horizon
`r_+ = M + √(M² − Q²)`) is where the metric is non-singular.

This file provides the `PartialMetricData 4` packaging.

**Connection to hypergraphs.** Same anchor as `Schwarzschild.lean`:
continuum-target side. Future hypergraph rules claiming to produce
charged black holes would pair with this via a convergence bridge.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- **Reissner-Nordström lapse function** `f(r) = 1 − 2M/r + Q²/r²`. -/
noncomputable def rnLapse (M Q : ℝ) (r : ℝ) : ℝ :=
  1 - 2 * M / r + Q^2 / r^2

/-- **Reissner-Nordström metric components.** Diagonal in
`(t, r, θ, φ)` coordinates. -/
noncomputable def rnG (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -rnLapse M Q r
    else if μ.val = 1 then 1 / rnLapse M Q r
    else if μ.val = 2 then r^2
    else r^2 * (Real.sin θ)^2

/-- **Reissner-Nordström inverse metric.** Diagonal reciprocal. -/
noncomputable def rnGinv (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -1 / rnLapse M Q r
    else if μ.val = 1 then rnLapse M Q r
    else if μ.val = 2 then 1 / r^2
    else 1 / (r^2 * (Real.sin θ)^2)

/-- **Reissner-Nordström validity**: `r > 0`, `rnLapse > 0`
(outside the outer horizon), and `sin θ ≠ 0` (off the polar axis). -/
def RNValid (M Q : ℝ) (x : Fin 4 → ℝ) : Prop :=
  x 1 > 0 ∧ rnLapse M Q (x 1) > 0 ∧ Real.sin (x 2) ≠ 0

/-- **At `Q = 0`, Reissner-Nordström reduces to Schwarzschild.** The
`RNValid M 0` predicate is then equivalent to `r > 2M ∧ r > 0 ∧
sin θ ≠ 0` — matching the Schwarzschild `SchwarzschildValid`. -/
theorem rnLapse_schwarzschild (M r : ℝ) (hr : r > 0) :
    rnLapse M 0 r = 1 - 2 * M / r := by
  unfold rnLapse
  simp

/-- **`rnLapse > 0` iff `r > r_+`** where `r_+ = M + √(M² - Q²)` is
the outer horizon. In the case `Q = 0`, this becomes `r > 2M`. -/
theorem rnLapse_pos_of_large_r_Q_zero (M r : ℝ) (h2M : r > 2 * M) (hr : r > 0) :
    rnLapse M 0 r > 0 := by
  rw [rnLapse_schwarzschild M r hr]
  have hr_ne : r ≠ 0 := ne_of_gt hr
  rw [show (1 : ℝ) - 2 * M / r = (r - 2 * M) / r from by field_simp]
  exact div_pos (by linarith) hr

/-- **Reissner-Nordström metric symmetry.** -/
theorem rnG_symm (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    rnG M Q x μ ν = rnG M Q x ν μ := by
  unfold rnG
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- **Reissner-Nordström inverse metric symmetry.** -/
theorem rnGinv_symm (M Q : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    rnGinv M Q x μ ν = rnGinv M Q x ν μ := by
  unfold rnGinv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

end Curvature
end InfraFormalization
