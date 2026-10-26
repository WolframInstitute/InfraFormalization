/-
Shortest-path distance on the cycle graph C_n.

This module defines the unscaled shortest-path distance `cycleDist` on the cycle with vertex set
`Fin n` and proves that it is symmetric, zero on the diagonal, bounded by `n / 2`, satisfies the
triangle inequality, and vanishes only on the diagonal for `n ≥ 2`. The Gromov–Hausdorff convergence
of (C_n, d/n) to the circle ℝ/ℤ is not proved here.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace InfraFormalization
namespace Infra

/-- Graph distance on the cycle `Fin n` (unscaled).  `cycleDist n i j`
is `min(|i - j|, n - |i - j|)`, the shortest-path distance on the
cycle `C_n`. -/
def cycleDist (n : Nat) (i j : Fin n) : Nat :=
  let d := if i.val ≤ j.val then j.val - i.val else i.val - j.val
  min d (n - d)

@[simp] theorem cycleDist_self {n : Nat} (i : Fin n) :
    cycleDist n i i = 0 := by
  simp [cycleDist]

theorem cycleDist_symm {n : Nat} (i j : Fin n) :
    cycleDist n i j = cycleDist n j i := by
  unfold cycleDist
  by_cases h : i.val ≤ j.val
  · by_cases h' : j.val ≤ i.val
    · -- i.val = j.val
      have heq : i.val = j.val := Nat.le_antisymm h h'
      simp [h, h', heq]
    · simp [h, h']
  · have h' : j.val ≤ i.val := Nat.le_of_not_le h
    by_cases hij : i.val = j.val
    · simp [hij]
    · have hne : j.val ≠ i.val := fun x => hij x.symm
      have h_not : ¬ j.val ≥ i.val + 1 := by
        intro hge
        exact absurd (Nat.le_of_succ_le hge) h
      simp only [h, h']
      rfl

/-- `cycleDist n i j ≤ n / 2`: the diameter of C_n is at most `⌊n/2⌋`. -/
theorem cycleDist_le_half {n : Nat} (i j : Fin n) :
    cycleDist n i j ≤ n / 2 := by
  unfold cycleDist
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  by_cases h : i.val ≤ j.val
  · -- Case: i ≤ j. The "forward" distance is j - i.
    simp only [if_pos h]
    -- min(j-i, n-(j-i)) ≤ n/2
    have h1 : j.val - i.val < n := by omega
    omega
  · -- Case: i > j. The "forward" distance is i - j.
    simp only [if_neg h]
    have h1 : i.val - j.val < n := by omega
    omega

/-- For `n ≤ 1`, the cycle distance is 0. -/
theorem cycleDist_zero_of_small {n : Nat} (hn : n ≤ 1) (i j : Fin n) :
    cycleDist n i j = 0 := by
  unfold cycleDist
  interval_cases n
  · exact i.elim0
  · have : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    simp [this, hj]

/-- Triangle inequality for the cycle distance. -/
theorem cycleDist_triangle {n : Nat} (i j k : Fin n) :
    cycleDist n i k ≤ cycleDist n i j + cycleDist n j k := by
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  have hk : k.val < n := k.isLt
  unfold cycleDist
  by_cases hij : i.val ≤ j.val
  · by_cases hjk : j.val ≤ k.val
    · by_cases hik : i.val ≤ k.val
      · simp only [if_pos hij, if_pos hjk, if_pos hik]; omega
      · simp only [if_pos hij, if_pos hjk, if_neg hik]; omega
    · by_cases hik : i.val ≤ k.val
      · simp only [if_pos hij, if_neg hjk, if_pos hik]; omega
      · simp only [if_pos hij, if_neg hjk, if_neg hik]; omega
  · by_cases hjk : j.val ≤ k.val
    · by_cases hik : i.val ≤ k.val
      · simp only [if_neg hij, if_pos hjk, if_pos hik]; omega
      · simp only [if_neg hij, if_pos hjk, if_neg hik]; omega
    · by_cases hik : i.val ≤ k.val
      · simp only [if_neg hij, if_neg hjk, if_pos hik]; omega
      · simp only [if_neg hij, if_neg hjk, if_neg hik]; omega

/-- For `n ≥ 2`, `cycleDist n i j = 0` if and only if `i = j`. -/
theorem cycleDist_eq_zero_iff {n : Nat} (hn : 2 ≤ n) (i j : Fin n) :
    cycleDist n i j = 0 ↔ i = j := by
  constructor
  · intro h
    unfold cycleDist at h
    -- min d (n - d) = 0 with 0 ≤ d ≤ n means d = 0 or d = n.
    -- Since i, j < n, both options of d are in [0, n), so d = 0.
    have hi : i.val < n := i.isLt
    have hj : j.val < n := j.isLt
    by_cases hij : i.val ≤ j.val
    · simp only [if_pos hij] at h
      -- h : min (j.val - i.val) (n - (j.val - i.val)) = 0
      have : j.val - i.val = 0 := by omega
      have heq : i.val = j.val := by omega
      exact Fin.ext heq
    · simp only [if_neg hij] at h
      have : i.val - j.val = 0 := by omega
      have heq : i.val = j.val := by omega
      exact Fin.ext heq
  · intro h; rw [h, cycleDist_self]

end Infra
end InfraFormalization
