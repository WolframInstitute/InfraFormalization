/-
Laplacian of the cycle graph `C_n`.

This module defines the cycle Laplacian as the second difference
`Δ_{C_n} f (i) = f(i + 1) + f(i − 1) − 2 f(i)` on `Fin n`, with addition
modulo `n`, for `n ≥ 1`. It proves that `Δ` is linear and vanishes on
constants, that `∑_i f(i) · (−Δ f)(i) = ∑_i (f(i+1) − f(i))²`, and that
this sum is nonnegative.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace InfraFormalization

/-- The cycle Laplacian `f(i + 1) + f(i − 1) − 2 f(i)`, with `+1` and
`−1` taken in `Fin n` modulo `n`. For `n ≥ 3` it is the negative of the
graph Laplacian of the cycle `C_n`. -/
def cycleLaplacian (n : Nat) [NeZero n] (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  f (i + 1) + f (i - 1) - 2 * f i

/-- Cycle Laplacian is additive. -/
theorem cycleLaplacian_add (n : Nat) [NeZero n] (f g : Fin n → ℝ) (i : Fin n) :
    cycleLaplacian n (f + g) i = cycleLaplacian n f i + cycleLaplacian n g i := by
  unfold cycleLaplacian
  simp [Pi.add_apply]
  ring

/-- Cycle Laplacian commutes with scalar multiplication. -/
theorem cycleLaplacian_smul (n : Nat) [NeZero n] (c : ℝ) (f : Fin n → ℝ) (i : Fin n) :
    cycleLaplacian n (fun j => c * f j) i = c * cycleLaplacian n f i := by
  unfold cycleLaplacian
  ring

/-- Cycle Laplacian of a constant is zero. -/
theorem cycleLaplacian_const (n : Nat) [NeZero n] (c : ℝ) (i : Fin n) :
    cycleLaplacian n (fun _ => c) i = 0 := by
  unfold cycleLaplacian
  ring

/-- The quadratic form of `−Δ` on the cycle equals the Dirichlet energy:
`∑_i f(i) · (−Δ f)(i) = ∑_i (f(i+1) − f(i))²`. -/
theorem cycle_dirichlet_form (n : Nat) [NeZero n] (f : Fin n → ℝ) :
    ∑ i : Fin n, f i * (- cycleLaplacian n f i)
    = ∑ i : Fin n, (f (i + 1) - f i)^2 := by
  unfold cycleLaplacian
  -- ∑ f i · (-(f(i+1) + f(i-1) - 2 f i))
  -- = ∑ f i · (2 f i - f(i+1) - f(i-1))
  -- = 2 ∑ f i² - ∑ f i f(i+1) - ∑ f i f(i-1).
  -- Reindex ∑ f i f(i-1) with j = i - 1, giving ∑ f(j+1) f j = ∑ f j f(j+1).
  -- So the LHS = 2 ∑ f² - 2 ∑ f i f(i+1).
  -- And RHS = ∑ (f(i+1) - f i)² = ∑ f(i+1)² - 2 f i f(i+1) + f i²
  --        = ∑ f(i+1)² + ∑ f i² - 2 ∑ f i f(i+1)
  --        = 2 ∑ f² - 2 ∑ f i f(i+1)  (reindex ∑ f(i+1)² = ∑ f²)
  -- So LHS = RHS.
  -- The shift `i ↦ i + 1` is a bijection of `Fin n`.
  have shift_bij : (Equiv.addRight (1 : Fin n)).toFun.Bijective :=
    (Equiv.addRight _).bijective
  -- Rewrite ∑ f i f(i-1) = ∑ f(j+1) f j via substitution i = j + 1.
  have reindex_minus :
      ∑ i : Fin n, f i * f (i - 1) = ∑ j : Fin n, f (j + 1) * f j :=
    Fintype.sum_equiv (Equiv.addRight (-1 : Fin n))
      (fun i => f i * f (i - 1))
      (fun j => f (j + 1) * f j)
      (fun i => by
        show f i * f (i - 1)
           = f (i + (-1) + 1) * f (i + (-1))
        congr 1
        · congr 1; abel
        · congr 1; abel)
  -- ∑ f(i+1)² = ∑ f j², via forward shift e : i ↦ i + 1, identifying
  -- f (e i) ^ 2 with f (i + 1) ^ 2.
  have reindex_square :
      ∑ i : Fin n, f (i + 1) * f (i + 1) = ∑ j : Fin n, f j * f j :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin n))
      (fun i => f (i + 1) * f (i + 1))
      (fun j => f j * f j)
      (fun i => by
        change f (i + 1) * f (i + 1) = f (i + 1) * f (i + 1)
        rfl)
  -- Compute LHS expansion.
  have lhs_expand :
      ∑ i : Fin n, f i * (-(f (i + 1) + f (i - 1) - 2 * f i))
      = 2 * (∑ i : Fin n, f i * f i) - 2 * (∑ i : Fin n, f i * f (i + 1)) := by
    have : ∀ i : Fin n,
        f i * (-(f (i + 1) + f (i - 1) - 2 * f i))
        = 2 * (f i * f i) - f i * f (i + 1) - f i * f (i - 1) := by
      intro i; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, reindex_minus]
    rw [show (∑ i : Fin n, f (i + 1) * f i) = (∑ i : Fin n, f i * f (i + 1)) from by
          apply Finset.sum_congr rfl
          intros i _
          ring]
    ring
  -- Compute RHS expansion.
  have rhs_expand :
      ∑ i : Fin n, (f (i + 1) - f i)^2
      = 2 * (∑ i : Fin n, f i * f i) - 2 * (∑ i : Fin n, f i * f (i + 1)) := by
    have : ∀ i : Fin n,
        (f (i + 1) - f i)^2 = f (i + 1) * f (i + 1) + f i * f i - 2 * (f i * f (i + 1)) := by
      intro i; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, reindex_square]
    rw [show (∑ i : Fin n, 2 * (f i * f (i + 1)))
          = 2 * ∑ i : Fin n, f i * f (i + 1) from by rw [← Finset.mul_sum]]
    ring
  rw [lhs_expand, rhs_expand]

/-- `∑_i f(i) · (−Δ f)(i) ≥ 0`. -/
theorem cycle_dirichlet_nonneg (n : Nat) [NeZero n] (f : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, f i * (- cycleLaplacian n f i) := by
  rw [cycle_dirichlet_form]
  apply Finset.sum_nonneg
  intros i _
  exact sq_nonneg _

end InfraFormalization
