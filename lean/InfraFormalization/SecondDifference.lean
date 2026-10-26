/-
Central second differences.

This module defines `secondDifference f x h = f(x + h) − 2 f(x) + f(x − h)`
and computes it for constants, linear functions, `x²` and quadratics: for
`f(x) = a x² + b x + c` it equals `2 a h²`, so divided by `h² ≠ 0` it equals
`2 a`. It proves additivity and homogeneity in `f`. The limit for C²
functions is in `CTwoTaylor.lean`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization

/-- The central second difference `f(x + h) − 2 f(x) + f(x − h)`. -/
def secondDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + h) - 2 * f x + f (x - h)

/-- The central second difference of `y ↦ y²` is `2 h²`. -/
theorem secondDifference_sq (x h : ℝ) :
    secondDifference (fun y => y^2) x h = 2 * h^2 := by
  unfold secondDifference
  ring

/-- The central second difference of `y ↦ a y` is 0. -/
theorem secondDifference_linear (a : ℝ) (x h : ℝ) :
    secondDifference (fun y => a * y) x h = 0 := by
  unfold secondDifference
  ring

/-- The central second difference of a constant function is 0. -/
theorem secondDifference_const (c : ℝ) (x h : ℝ) :
    secondDifference (fun _ => c) x h = 0 := by
  unfold secondDifference
  ring

/-- The central second difference of `f + g` is the sum of those of `f`
and `g`. -/
theorem secondDifference_add (f g : ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun y => f y + g y) x h
    = secondDifference f x h + secondDifference g x h := by
  unfold secondDifference
  ring

/-- The central second difference of `c · f` is `c` times that of `f`. -/
theorem secondDifference_smul (c : ℝ) (f : ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun y => c * f y) x h = c * secondDifference f x h := by
  unfold secondDifference
  ring

/-- The central second difference of `y ↦ a y² + b y + c` is `2 a h²`. -/
theorem secondDifference_quadratic (a b c x h : ℝ) :
    secondDifference (fun y => a * y^2 + b * y + c) x h = 2 * a * h^2 := by
  unfold secondDifference
  ring

/-- For `h ≠ 0`, the central second difference of `y ↦ a y² + b y + c`
divided by `h²` is `2 a`. -/
theorem secondDifference_quadratic_div (a b c x h : ℝ) (hh : h ≠ 0) :
    secondDifference (fun y => a * y^2 + b * y + c) x h / h^2 = 2 * a := by
  rw [secondDifference_quadratic]
  field_simp

end InfraFormalization
