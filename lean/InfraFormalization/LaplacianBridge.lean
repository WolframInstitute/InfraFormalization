/-
Scaled second differences and the cycle Laplacian.

This module defines the scaled second difference `n² · (f(x + 1/n) − 2f(x) + f(x − 1/n))` and proves
that it equals `2a` for every quadratic `f(y) = a·y² + b·y + c` and every `n > 0`, which is the
second derivative of `f`. It also proves that at an interior index of the cycle `C_n`, the cycle
Laplacian of `j ↦ f(j/n)` equals the second difference of `f` at `i/n` with step `1/n`. The case of
general `C²` functions is not treated.
-/

import InfraFormalization.SecondDifference
import InfraFormalization.CycleGraph
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace InfraFormalization

/-- `n² · (f(x + 1/n) − 2f(x) + f(x − 1/n))`. -/
noncomputable def scaledSecondDiff (f : ℝ → ℝ) (n : Nat) (x : ℝ) : ℝ :=
  (n : ℝ)^2 * secondDifference f x (1 / n)

/-- For `n > 0` and `f(y) = a·y² + b·y + c`, the scaled second difference at `x` equals `2a`. -/
theorem scaledSecondDiff_quadratic (a b c : ℝ) (n : Nat) (hn : 0 < n) (x : ℝ) :
    scaledSecondDiff (fun y => a * y^2 + b * y + c) n x = 2 * a := by
  unfold scaledSecondDiff
  rw [secondDifference_quadratic]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

/-- The scaled second difference of a constant function is 0. -/
theorem scaledSecondDiff_const (c : ℝ) (n : Nat) (x : ℝ) :
    scaledSecondDiff (fun _ => c) n x = 0 := by
  unfold scaledSecondDiff
  rw [secondDifference_const]
  ring

/-- The scaled second difference of `y ↦ a·y` is 0. -/
theorem scaledSecondDiff_linear (a : ℝ) (n : Nat) (x : ℝ) :
    scaledSecondDiff (fun y => a * y) n x = 0 := by
  unfold scaledSecondDiff
  rw [secondDifference_linear]
  ring

/-- The scaled second difference is additive in `f`. -/
theorem scaledSecondDiff_add (f g : ℝ → ℝ) (n : Nat) (x : ℝ) :
    scaledSecondDiff (fun y => f y + g y) n x
    = scaledSecondDiff f n x + scaledSecondDiff g n x := by
  unfold scaledSecondDiff
  rw [secondDifference_add]
  ring

/-- For a quadratic `f`, the scaled second difference takes the same value at any two scales
`n, m > 0` and any two points `x, y`. -/
theorem scaledSecondDiff_quadratic_independent
    (a b c : ℝ) (n m : Nat) (hn : 0 < n) (hm : 0 < m) (x y : ℝ) :
    scaledSecondDiff (fun z => a * z^2 + b * z + c) n x
    = scaledSecondDiff (fun z => a * z^2 + b * z + c) m y := by
  rw [scaledSecondDiff_quadratic a b c n hn x,
      scaledSecondDiff_quadratic a b c m hm y]

/-- For `1 ≤ i < n - 1`, the cycle Laplacian of `g(j) = f(j/n)` at `i` equals
`secondDifference f (i/n) (1/n)`. -/
theorem cycleLaplacian_in_terms_of_secondDifference
    (n : Nat) [NeZero n] (f : ℝ → ℝ) (i : Fin n)
    (hlo : 1 ≤ i.val) (hhi : i.val + 1 < n) :
    cycleLaplacian n (fun j => f ((j.val : ℝ) / (n : ℝ))) i
    = secondDifference f ((i.val : ℝ) / (n : ℝ)) (1 / (n : ℝ)) := by
  have hn_ge_2 : 2 ≤ n := by omega
  -- Compute the `.val` of `i + 1` and `i - 1` using Fin.val_add.
  have hone_val : (1 : Fin n).val = 1 := by
    show (1 % n) = 1
    exact Nat.mod_eq_of_lt hn_ge_2
  have h_succ : (i + 1 : Fin n).val = i.val + 1 := by
    rw [Fin.val_add, hone_val]
    exact Nat.mod_eq_of_lt hhi
  have h_pred : (i - 1 : Fin n).val = i.val - 1 := by
    -- In the group Fin n, i - 1 = i + (-1).
    have heq : (i - 1 : Fin n) = i + (-1 : Fin n) := sub_eq_add_neg _ _
    rw [heq, Fin.val_add]
    -- In the group Fin n, -1 has value n - 1.
    have hnegone_val : (-1 : Fin n).val = n - 1 := by
      show (n - (1 : Fin n).val) % n = n - 1
      rw [hone_val]
      exact Nat.mod_eq_of_lt (by omega : n - 1 < n)
    rw [hnegone_val]
    -- (i.val + (n - 1)) % n = i.val - 1 when i.val ≥ 1.
    have step : i.val + (n - 1) = (i.val - 1) + n := by omega
    rw [step, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega : i.val - 1 < n)
  -- Now rewrite both sides, converting Fin-indexed coords to real-arithmetic.
  unfold cycleLaplacian secondDifference
  -- Beta-reduce to expose the Fin .val cast structure.
  simp only []
  have hn_pos : (0 : ℝ) < n :=
    by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  -- Convert the .val expressions on the LHS to ℝ-arithmetic.
  have e_succ_cast : (((i + 1 : Fin n).val : ℕ) : ℝ) = (i.val : ℝ) + 1 := by
    rw [h_succ]
    push_cast
    ring
  have e_pred_cast : (((i - 1 : Fin n).val : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
    rw [h_pred, Nat.cast_sub hlo]
    push_cast
    ring
  rw [e_succ_cast, e_pred_cast]
  -- Now: f (((i.val : ℝ) + 1) / n) + f (((i.val : ℝ) - 1) / n) - 2 f(i.val/n)
  --   = f (i.val/n + 1/n) - 2 f(i.val/n) + f (i.val/n - 1/n).
  have div_add : ((i.val : ℝ) + 1) / (n : ℝ)
               = (i.val : ℝ) / (n : ℝ) + 1 / (n : ℝ) := by
    field_simp
  have div_sub : ((i.val : ℝ) - 1) / (n : ℝ)
               = (i.val : ℝ) / (n : ℝ) - 1 / (n : ℝ) := by
    field_simp
  rw [div_add, div_sub]
  ring

/-- For `f(y) = a·y² + b·y + c`, the second derivative of `f` at every point is `2a`. -/
theorem second_deriv_quadratic (a b c x : ℝ) :
    deriv (deriv (fun y => a * y^2 + b * y + c)) x = 2 * a := by
  -- First derivative at every y : (2 a y + b).
  have h_inner : ∀ y : ℝ,
      HasDerivAt (fun z => a * z^2 + b * z + c) (2 * a * y + b) y := by
    intro y
    have h_sq : HasDerivAt (fun z => z^2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h_a_sq : HasDerivAt (fun z => a * z^2) (a * (2 * y)) y :=
      h_sq.const_mul a
    have h_bz : HasDerivAt (fun z => b * z) b y := by
      simpa using (hasDerivAt_id y).const_mul b
    have h_sum : HasDerivAt (fun z => a * z^2 + b * z) (a * (2 * y) + b) y :=
      h_a_sq.add h_bz
    have h_full : HasDerivAt (fun z => a * z^2 + b * z + c) (a * (2 * y) + b) y :=
      h_sum.add_const c
    convert h_full using 1
    ring
  -- Identify `deriv (_)` pointwise with `fun y => 2 a y + b`.
  have h_first_deriv_eq :
      deriv (fun y => a * y^2 + b * y + c) = fun y => 2 * a * y + b := by
    funext y
    exact (h_inner y).deriv
  rw [h_first_deriv_eq]
  -- Second derivative: d/dx (2 a x + b) = 2 a.
  have h_outer : HasDerivAt (fun y => 2 * a * y + b) (2 * a) x := by
    have h_lin : HasDerivAt (fun y => 2 * a * y) (2 * a) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * a)
    have := h_lin.add_const b
    convert this using 1
  exact h_outer.deriv

/-- For `n > 0` and quadratic `f`, the scaled second difference of `f` at `x` equals
`deriv (deriv f) x`. -/
theorem polynomial_scaled_laplacian_eq_second_deriv
    (a b c : ℝ) (n : Nat) (hn : 0 < n) (x : ℝ) :
    scaledSecondDiff (fun y => a * y^2 + b * y + c) n x
    = deriv (deriv (fun y => a * y^2 + b * y + c)) x := by
  rw [scaledSecondDiff_quadratic a b c n hn x]
  rw [second_deriv_quadratic a b c x]

end InfraFormalization
