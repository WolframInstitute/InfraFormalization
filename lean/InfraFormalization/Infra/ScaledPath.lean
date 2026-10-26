/-
Path graph P_{n+1} with metric scaled by `1/n`.

This module defines the path distance `pathDist` on `Fin (n+1)` and the embedding
`pathEmbed n i = i/n` into [0, 1]. It proves that `pathDist` is a metric bounded by `n`, that
`|pathEmbed n i - pathEmbed n j| = pathDist n i j / n`, and that every point of [0, 1] is within
`1/(2n)` of the image of `pathEmbed n`.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfraFormalization
namespace Infra

/-- Shortest-path distance on the path graph with vertex set `Fin (n+1)`:
`pathDist n i j = |i - j|`. -/
def pathDist (n : Nat) (i j : Fin (n+1)) : Nat :=
  if i.val ≤ j.val then j.val - i.val else i.val - j.val

@[simp] theorem pathDist_self {n : Nat} (i : Fin (n+1)) :
    pathDist n i i = 0 := by
  simp [pathDist]

theorem pathDist_symm {n : Nat} (i j : Fin (n+1)) :
    pathDist n i j = pathDist n j i := by
  unfold pathDist
  by_cases h : i.val ≤ j.val
  · by_cases h' : j.val ≤ i.val
    · have heq : i.val = j.val := Nat.le_antisymm h h'
      simp [h, h', heq]
    · simp [h, h']
  · have h' : j.val ≤ i.val := Nat.le_of_not_le h
    by_cases hij : i.val = j.val
    · simp [hij]
    · simp only [h, h']; rfl

theorem pathDist_triangle {n : Nat} (i j k : Fin (n+1)) :
    pathDist n i k ≤ pathDist n i j + pathDist n j k := by
  unfold pathDist
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

theorem pathDist_le {n : Nat} (i j : Fin (n+1)) : pathDist n i j ≤ n := by
  unfold pathDist
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i.val ≤ j.val
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; omega

/-- The embedding `Fin (n+1) → ℝ`, `i ↦ i/n`. -/
noncomputable def pathEmbed (n : Nat) (i : Fin (n+1)) : ℝ := (i.val : ℝ) / n

theorem pathEmbed_mem_unit_interval {n : Nat} (hn : 0 < n) (i : Fin (n+1)) :
    0 ≤ pathEmbed n i ∧ pathEmbed n i ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · unfold pathEmbed
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_one hn_pos]
    have : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
    exact_mod_cast this

/-- For `n > 0`, `|pathEmbed n i - pathEmbed n j| = pathDist n i j / n`. -/
theorem pathEmbed_isometry {n : Nat} (hn : 0 < n) (i j : Fin (n+1)) :
    |pathEmbed n i - pathEmbed n j| = (pathDist n i j : ℝ) / n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pathEmbed pathDist
  by_cases hij : i.val ≤ j.val
  · simp only [if_pos hij]
    rw [abs_sub_comm]
    rw [show (j.val : ℝ) / n - (i.val : ℝ) / n = ((j.val - i.val : ℕ) : ℝ) / n from by
      rw [Nat.cast_sub hij]; ring]
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos))]
  · push_neg at hij
    simp only [if_neg (not_le.mpr hij)]
    have hji : j.val ≤ i.val := le_of_lt hij
    rw [show (i.val : ℝ) / n - (j.val : ℝ) / n = ((i.val - j.val : ℕ) : ℝ) / n from by
      rw [Nat.cast_sub hji]; ring]
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos))]

/-- For `n > 0`, every `x ∈ [0, 1]` is within `1/(2n)` of some `pathEmbed n i`. -/
theorem pathEmbed_covers {n : Nat} (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    ∃ i : Fin (n+1), |x - pathEmbed n i| ≤ 1 / (2 * n) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n_pos : (0 : ℝ) < 2 * n := by linarith
  -- Take m = ⌊n·x⌋ and compare x with m/n and (m+1)/n.
  set m : ℕ := ⌊(n : ℝ) * x⌋₊ with hm_def
  have hm_le : (m : ℝ) ≤ (n : ℝ) * x :=
    Nat.floor_le (mul_nonneg (le_of_lt hn_pos) hx)
  have hm_succ_gt : (n : ℝ) * x < (m : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one ((n : ℝ) * x)
  have hm_le_n : m ≤ n := by
    have : (m : ℝ) ≤ (n : ℝ) := by
      calc (m : ℝ) ≤ (n : ℝ) * x := hm_le
        _ ≤ (n : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hx' (le_of_lt hn_pos)
        _ = (n : ℝ) := by ring
    exact_mod_cast this
  by_cases h_left_close : x - (m : ℝ) / n ≤ 1 / (2 * n)
  · -- x is close to m/n. m ≤ n so m ∈ Fin (n+1).
    refine ⟨⟨m, Nat.lt_succ_of_le hm_le_n⟩, ?_⟩
    unfold pathEmbed
    have h_nn : 0 ≤ x - (m : ℝ) / n := by
      have : (m : ℝ) / n ≤ x := by
        rw [div_le_iff₀ hn_pos]
        linarith
      linarith
    rw [abs_of_nonneg h_nn]
    exact h_left_close
  · -- x closer to (m+1)/n. (m+1) ≤ n+1 = (n+1).
    push_neg at h_left_close
    have h_m_succ_le : m + 1 ≤ n + 1 := by omega
    have h_succ_bounded : (↑m + 1 : ℝ) / ↑n ≤ 1 + 1/n := by
      rw [show ((↑m + 1 : ℝ)) / ↑n = ↑m/↑n + 1/↑n from by field_simp]
      have : (m : ℝ) / n ≤ 1 := by
        rw [div_le_one hn_pos]
        exact_mod_cast hm_le_n
      linarith
    -- In this branch m < n (if m = n then m/n = 1, and x ≤ 1 forces
    -- x - m/n ≤ 0 ≤ 1/(2n), contradicting h_left_close).
    have hm_lt_n : m < n := by
      by_contra h
      push_neg at h
      have hm_eq : m = n := Nat.le_antisymm hm_le_n h
      have h_div : (m : ℝ) / n = 1 := by
        rw [hm_eq]; exact div_self (ne_of_gt hn_pos)
      have h_sub_nonpos : x - (m : ℝ) / n ≤ 0 := by rw [h_div]; linarith
      have h_inv_pos : (0 : ℝ) < 1 / (2 * n) := by positivity
      have : x - (m : ℝ) / n ≤ 1 / (2 * n) := le_of_lt (lt_of_le_of_lt h_sub_nonpos h_inv_pos)
      exact absurd this (not_le.mpr h_left_close)
    have h_valid : m + 1 < n + 1 := by omega
    refine ⟨⟨m + 1, h_valid⟩, ?_⟩
    unfold pathEmbed
    -- Normalise the Fin coercion: ((⟨m+1,_⟩).val : ℝ) = (m : ℝ) + 1.
    show |x - ((m + 1 : ℕ) : ℝ) / n| ≤ 1 / (2 * n)
    rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 from by push_cast; rfl]
    -- x < (m+1)/n (from floor property) so x - (m+1)/n ≤ 0.
    have h_sub_neg : x - ((m : ℝ) + 1) / n ≤ 0 := by
      have : x < ((m : ℝ) + 1) / n := by
        rw [lt_div_iff₀ hn_pos]
        have : x * n = n * x := by ring
        rw [this]; exact hm_succ_gt
      linarith
    rw [abs_of_nonpos h_sub_neg]
    have h_expand : ((m : ℝ) + 1) / n - x = 1/n - (x - (m : ℝ)/n) := by
      field_simp; ring
    have h_step : (1 : ℝ)/n - 1/(2*n) = 1/(2*n) := by field_simp; ring
    rw [show -(x - ((↑m + 1 : ℝ)) / ↑n) = ((↑m + 1 : ℝ)) / ↑n - x from by ring]
    rw [h_expand]
    linarith

/-- For `n > 0`, there is a map `f : Fin (n+1) → ℝ` with values in [0, 1] such that
`|f i - f j| = pathDist n i j / n` and every point of [0, 1] is within `1/(2n)` of the image of `f`.
These conditions bound the Gromov–Hausdorff distance between (P_{n+1}, pathDist/n) and [0, 1] by
`1/(2n)`. -/
theorem path_interval_gh_bound (n : Nat) (hn : 0 < n) :
    ∃ f : Fin (n+1) → ℝ,
      (∀ i, 0 ≤ f i ∧ f i ≤ 1) ∧
      (∀ i j, |f i - f j| = (pathDist n i j : ℝ) / n) ∧
      (∀ x, 0 ≤ x → x ≤ 1 → ∃ i, |x - f i| ≤ 1 / (2 * n)) := by
  refine ⟨pathEmbed n, ?_, ?_, ?_⟩
  · intro i; exact pathEmbed_mem_unit_interval hn i
  · intro i j; exact pathEmbed_isometry hn i j
  · intro x hx hx'; exact pathEmbed_covers hn x hx hx'

end Infra
end InfraFormalization
