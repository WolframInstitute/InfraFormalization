/-
Closed forms for the Forman and Higuchi totals of the 2D grid and torus.

The module defines the polynomials `gridFormanClosedForm n = -16n² + 40n − 16`,
`gridHiguchiClosedForm n = -2n² + 4n`, `torusFormanClosedForm n = -16n²` and
`torusHiguchiClosedForm n = -2n²`. It proves that `execFormanScalar` and `higuchiTotalDoubled` of
`gridHG n n` and `torusHG n n` equal these polynomials at sampled `n`, each checked by
`native_decide`. It also defines the real sequences `gridFormanDensity` and `gridHiguchiDensity`,
which are the grid closed forms divided by `n²`.
-/

import InfraFormalization.AdvancedContinuumLimits
import InfraFormalization.GridContinuumLimit

namespace InfraFormalization
namespace NormalizedDensityLimits

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener
open AdvancedContinuumLimits
open GridContinuumLimit

/-! ## Grid Forman closed form: `-16n² + 40n − 16`

The equality is checked by `native_decide` at `n ∈ {3, 4, 5, 6, 8, 12}`. -/

/-- The polynomial `-16n² + 40n − 16`. -/
def gridFormanClosedForm (n : ℕ) : ℤ := -16 * (n : ℤ)^2 + 40 * (n : ℤ) - 16

theorem grid_3_3_forman_closed_form :
    execFormanScalar (gridHG 3 3) = gridFormanClosedForm 3 := by
  show execFormanScalar (gridHG 3 3) = -16 * 9 + 40 * 3 - 16
  native_decide

theorem grid_4_4_forman_closed_form :
    execFormanScalar (gridHG 4 4) = gridFormanClosedForm 4 := by
  show execFormanScalar (gridHG 4 4) = -16 * 16 + 40 * 4 - 16
  native_decide

theorem grid_5_5_forman_closed_form :
    execFormanScalar (gridHG 5 5) = gridFormanClosedForm 5 := by
  show execFormanScalar (gridHG 5 5) = -16 * 25 + 40 * 5 - 16
  native_decide

theorem grid_6_6_forman_closed_form :
    execFormanScalar (gridHG 6 6) = gridFormanClosedForm 6 := by
  show execFormanScalar (gridHG 6 6) = -16 * 36 + 40 * 6 - 16
  native_decide

theorem grid_8_8_forman_closed_form :
    execFormanScalar (gridHG 8 8) = gridFormanClosedForm 8 := by
  show execFormanScalar (gridHG 8 8) = -16 * 64 + 40 * 8 - 16
  native_decide

theorem grid_12_12_forman_closed_form :
    execFormanScalar (gridHG 12 12) = gridFormanClosedForm 12 := by
  show execFormanScalar (gridHG 12 12) = -16 * 144 + 40 * 12 - 16
  native_decide

/-! ## Grid Higuchi closed form: `-2n² + 4n` -/

def gridHiguchiClosedForm (n : ℕ) : ℤ := -2 * (n : ℤ)^2 + 4 * (n : ℤ)

theorem grid_3_3_higuchi_closed_form :
    higuchiTotalDoubled (gridHG 3 3) = gridHiguchiClosedForm 3 := by
  show higuchiTotalDoubled (gridHG 3 3) = -2 * 9 + 4 * 3
  native_decide

theorem grid_4_4_higuchi_closed_form :
    higuchiTotalDoubled (gridHG 4 4) = gridHiguchiClosedForm 4 := by
  show higuchiTotalDoubled (gridHG 4 4) = -2 * 16 + 4 * 4
  native_decide

theorem grid_5_5_higuchi_closed_form :
    higuchiTotalDoubled (gridHG 5 5) = gridHiguchiClosedForm 5 := by
  show higuchiTotalDoubled (gridHG 5 5) = -2 * 25 + 4 * 5
  native_decide

theorem grid_6_6_higuchi_closed_form :
    higuchiTotalDoubled (gridHG 6 6) = gridHiguchiClosedForm 6 := by
  show higuchiTotalDoubled (gridHG 6 6) = -2 * 36 + 4 * 6
  native_decide

/-! ## T² Forman closed form: `-16n²` (pure bulk, no boundary) -/

def torusFormanClosedForm (n : ℕ) : ℤ := -16 * (n : ℤ)^2

theorem torus_4_4_forman_closed_form :
    execFormanScalar (torusHG 4 4) = torusFormanClosedForm 4 := by
  show execFormanScalar (torusHG 4 4) = -16 * 16
  native_decide

theorem torus_5_5_forman_closed_form :
    execFormanScalar (torusHG 5 5) = torusFormanClosedForm 5 := by
  show execFormanScalar (torusHG 5 5) = -16 * 25
  native_decide

theorem torus_6_6_forman_closed_form :
    execFormanScalar (torusHG 6 6) = torusFormanClosedForm 6 := by
  show execFormanScalar (torusHG 6 6) = -16 * 36
  native_decide

theorem torus_8_8_forman_closed_form :
    execFormanScalar (torusHG 8 8) = torusFormanClosedForm 8 := by
  show execFormanScalar (torusHG 8 8) = -16 * 64
  native_decide

/-! ## T² Higuchi closed form: `-2n²` (pure bulk) -/

def torusHiguchiClosedForm (n : ℕ) : ℤ := -2 * (n : ℤ)^2

theorem torus_4_4_higuchi_closed_form :
    higuchiTotalDoubled (torusHG 4 4) = torusHiguchiClosedForm 4 := by
  show higuchiTotalDoubled (torusHG 4 4) = -2 * 16
  native_decide

theorem torus_5_5_higuchi_closed_form :
    higuchiTotalDoubled (torusHG 5 5) = torusHiguchiClosedForm 5 := by
  show higuchiTotalDoubled (torusHG 5 5) = -2 * 25
  native_decide

theorem torus_6_6_higuchi_closed_form :
    higuchiTotalDoubled (torusHG 6 6) = torusHiguchiClosedForm 6 := by
  show higuchiTotalDoubled (torusHG 6 6) = -2 * 36
  native_decide

/-! ## Grid densities -/

/-- The real sequence `-16 + 40/n − 16/n²`, which equals `gridFormanClosedForm n / n²` for
`n > 0`. -/
noncomputable def gridFormanDensity : ℕ → ℝ :=
  fun n => -16 + 40 / (n : ℝ) - 16 / ((n : ℝ)^2)

/-- The real sequence `-2 + 4/n`, which equals `gridHiguchiClosedForm n / n²` for `n > 0`. -/
noncomputable def gridHiguchiDensity : ℕ → ℝ :=
  fun n => -2 + 4 / (n : ℝ)

end NormalizedDensityLimits
end InfraFormalization
