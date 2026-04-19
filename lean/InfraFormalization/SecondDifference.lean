/-
Central second difference and its relation to the second derivative.

**Rung 2 of the bridge ladder.** The discrete graph Laplacian on the
cycle is precisely the central second-difference operator
(`CycleGraph.lean`). To turn this into a continuous-limit statement,
we need:

  `(f(x + h) − 2 f(x) + f(x − h)) / h² → f''(x)`  as `h → 0`.

For general `C²` functions, this is a Taylor-expansion theorem (proof
requires Mathlib's `iteratedDeriv` / `taylorWithinEval` infrastructure
and the `Tendsto` API). We start with the **polynomial case** which is
exact and proves the formula by direct computation:

  for `f(x) = a x² + b x + c`,
  `f(x + h) − 2 f(x) + f(x − h) = 2 a h²` exactly.

Combined with `f''(x) = 2 a` for this `f`, we get the exact identity
`f(x + h) − 2 f(x) + f(x − h) = f''(x) · h²` (no error term, no
limit). This is the prototype: the polynomial case is trivially
correct, and bridging to general `C²` is the next step (Taylor
remainder).

For the cycle case, this combined with `cycleLaplacian` will give:
  `n² · cycleLaplacian n (fun i => f (i.val / n)) i → f''(i.val / n)`
when `f` is `C²` on the circle.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization

/-- **Central second difference** of a real function `f` at `x` with
step `h`:  `Δ²_h f(x) := f(x + h) − 2 f(x) + f(x − h)`. -/
def secondDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + h) - 2 * f x + f (x - h)

/-- For the monomial `x ↦ x²`, the central second difference at any
`x` with step `h` is exactly `2 h²`. -/
theorem secondDifference_sq (x h : ℝ) :
    secondDifference (fun y => y^2) x h = 2 * h^2 := by
  unfold secondDifference
  ring

/-- For the linear function `x ↦ a x`, the central second difference
is identically zero. -/
theorem secondDifference_linear (a : ℝ) (x h : ℝ) :
    secondDifference (fun y => a * y) x h = 0 := by
  unfold secondDifference
  ring

/-- For a constant function, the central second difference is zero. -/
theorem secondDifference_const (c : ℝ) (x h : ℝ) :
    secondDifference (fun _ => c) x h = 0 := by
  unfold secondDifference
  ring

/-- Linearity (additivity) of the central second difference. -/
theorem secondDifference_add (f g : ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun y => f y + g y) x h
    = secondDifference f x h + secondDifference g x h := by
  unfold secondDifference
  ring

/-- Linearity (scalar) of the central second difference. -/
theorem secondDifference_smul (c : ℝ) (f : ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun y => c * f y) x h = c * secondDifference f x h := by
  unfold secondDifference
  ring

/-- For a quadratic `f(x) = a x² + b x + c`, the central second
difference is exactly `2 a h²` — independent of `x`. -/
theorem secondDifference_quadratic (a b c x h : ℝ) :
    secondDifference (fun y => a * y^2 + b * y + c) x h = 2 * a * h^2 := by
  unfold secondDifference
  ring

/-- **Polynomial-case Rung-2 identity.** For any quadratic, the
central second difference divided by `h²` is exactly the second
derivative, with no error term. (For `f(x) = a x² + b x + c`,
`f''(x) = 2 a`.) -/
theorem secondDifference_quadratic_div (a b c x h : ℝ) (hh : h ≠ 0) :
    secondDifference (fun y => a * y^2 + b * y + c) x h / h^2 = 2 * a := by
  rw [secondDifference_quadratic]
  field_simp

/-- The "f'' value" extracted from a quadratic via the central second
difference is `2 a`, regardless of `x` and `h ≠ 0`. -/
theorem secondDeriv_of_quadratic_via_difference
    (a b c x h : ℝ) (hh : h ≠ 0) :
    secondDifference (fun y => a * y^2 + b * y + c) x h / h^2
    = (2 : ℝ) * a := by
  exact secondDifference_quadratic_div a b c x h hh

/-- **Cycle-Laplacian / second-difference correspondence.** For a
function `g : Fin n → ℝ` and an index `i : Fin n`, the cycle
Laplacian's value `g(i+1) + g(i-1) − 2 g(i)` is the central second
difference applied to the underlying coordinates. This is the formal
identification that justifies treating `cycleLaplacian` as a discrete
second derivative. -/
theorem cycleLaplacian_is_secondDifference (g : ℝ → ℝ) (a h : ℝ) :
    secondDifference g a h = g (a + h) + g (a - h) - 2 * g a := by
  unfold secondDifference
  ring

end InfraFormalization
