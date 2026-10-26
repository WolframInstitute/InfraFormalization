/-
Circle distance on ℝ/ℤ and the embedding of the n-cycle into the circle.

The module defines `circleDist x y = min(|x - y|, 1 - |x - y|)` and the map
`latticeEmbed n : Fin n → ℝ`, `i ↦ i/n`. It proves that `circleDist` of two lattice
points equals `cycleDist n i j / n`, and that every `x ∈ [0, 1)` lies within circle distance
`1/(2n)` of some lattice point. The covering proof uses `LatticeDensity`.
-/

import InfraFormalization.Infra.ScaledCycle
import InfraFormalization.Infra.LatticeDensity

namespace InfraFormalization
namespace Infra

/-- `circleDist x y = min(|x - y|, 1 - |x - y|)`. For `x, y ∈ [0, 1)` this is the
distance on ℝ/ℤ between the classes of `x` and `y`. -/
noncomputable def circleDist (x y : ℝ) : ℝ :=
  min (|x - y|) (1 - |x - y|)

theorem circleDist_self (x : ℝ) : circleDist x x = 0 := by
  unfold circleDist
  simp

theorem circleDist_symm (x y : ℝ) : circleDist x y = circleDist y x := by
  unfold circleDist
  rw [abs_sub_comm]

theorem circleDist_nonneg {x y : ℝ} (hx : 0 ≤ x) (hx' : x < 1)
    (hy : 0 ≤ y) (hy' : y < 1) :
    0 ≤ circleDist x y := by
  unfold circleDist
  have habs : |x - y| < 1 := by
    rw [abs_sub_lt_iff]
    refine ⟨by linarith, by linarith⟩
  have habs_nn : 0 ≤ |x - y| := abs_nonneg _
  exact le_min habs_nn (by linarith)

theorem circleDist_le_half (x y : ℝ) : circleDist x y ≤ 1 / 2 := by
  unfold circleDist
  -- min(a, 1-a) ≤ 1/2 for any a : we have a + (1-a) = 1, so their min is ≤ 1/2.
  by_cases h : |x - y| ≤ 1 / 2
  · exact le_trans (min_le_left _ _) h
  · push_neg at h
    have : 1 - |x - y| ≤ 1 / 2 := by linarith
    exact le_trans (min_le_right _ _) this

/-- The map `Fin n → ℝ`, `i ↦ i/n`, with image `{0, 1/n, …, (n-1)/n}`. -/
noncomputable def latticeEmbed (n : Nat) (i : Fin n) : ℝ := (i.val : ℝ) / n

theorem latticeEmbed_mem_unit_interval {n : Nat} (hn : 0 < n) (i : Fin n) :
    0 ≤ latticeEmbed n i ∧ latticeEmbed n i < 1 := by
  refine ⟨?_, ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · unfold latticeEmbed
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_lt_one hn_pos]
    exact_mod_cast i.isLt

/-- For `n > 0`, every `x ∈ [0, 1)` lies within circle distance `1/(2n)` of
`latticeEmbed n i` for some `i`. -/
theorem latticeEmbed_covers {n : Nat} (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) :
    ∃ i : Fin n, circleDist x (latticeEmbed n i) ≤ 1 / (2 * n) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h2n_pos : (0 : ℝ) < 2 * n := by linarith
  -- (m + 1)/n = m/n + 1/n.
  have h_diff_1 : ∀ (m : ℝ), (m + 1) / n = m / n + 1 / n := by
    intro m; field_simp
  have h_half_diff : (1 : ℝ) / n - 1 / (2 * n) = 1 / (2 * n) := by
    field_simp; ring
  -- Use `exists_lattice_index` directly to get `i` with `i/n ≤ x < (i+1)/n`.
  obtain ⟨i, h_left, h_right⟩ := exists_lattice_index n hn x hx hx'
  have h_right' : x < (i.val : ℝ) / n + 1 / n := by
    have := h_right; rw [h_diff_1] at this; exact this
  -- So 0 ≤ x - i/n < 1/n.
  have h_nn : 0 ≤ x - (i.val : ℝ) / n := by linarith
  have h_lt_one_n : x - (i.val : ℝ) / n < 1 / n := by linarith
  -- Split: close to i/n on the right, or close to (i+1)/n on the left.
  by_cases h_left_close : x - (i.val : ℝ) / n ≤ 1 / (2 * n)
  · -- Closer to left. Output i.
    refine ⟨i, ?_⟩
    unfold circleDist latticeEmbed
    rw [abs_of_nonneg h_nn]
    exact le_trans (min_le_left _ _) h_left_close
  · -- Closer to right. Output `(i+1) mod n`.
    push_neg at h_left_close
    have h_right_close : 1 / n - (x - (i.val : ℝ) / n) ≤ 1 / (2 * n) := by
      linarith
    let j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
    refine ⟨j, ?_⟩
    unfold circleDist latticeEmbed
    by_cases hwrap : i.val + 1 < n
    · -- No wrap: j.val = i.val + 1.
      have hj_eq : j.val = i.val + 1 := Nat.mod_eq_of_lt hwrap
      have hj_cast : ((j.val : ℝ)) = (i.val : ℝ) + 1 := by
        rw [show (j.val : ℝ) = ((j.val : ℕ) : ℝ) from rfl]
        rw [hj_eq]; push_cast; rfl
      rw [hj_cast]
      have h_sub_neg : x - ((i.val : ℝ) + 1) / n ≤ 0 := by linarith
      have h_abs : |x - ((i.val : ℝ) + 1) / n| = ((i.val : ℝ) + 1) / n - x := by
        rw [abs_of_nonpos h_sub_neg]; ring
      rw [h_abs]
      have h_expand : ((i.val : ℝ) + 1) / n - x = 1 / n - (x - (i.val : ℝ) / n) := by
        rw [h_diff_1]; ring
      rw [h_expand]
      exact le_trans (min_le_left _ _) h_right_close
    · -- Wrap: i.val + 1 = n, so j.val = 0.
      push_neg at hwrap
      have hi_eq : i.val + 1 = n := le_antisymm (Nat.succ_le_of_lt i.isLt) hwrap
      have hj_eq : j.val = 0 := by
        show (i.val + 1) % n = 0
        rw [hi_eq]; exact Nat.mod_self _
      have hj_cast : ((j.val : ℝ)) = 0 := by rw [hj_eq]; norm_num
      rw [hj_cast, zero_div]
      -- Want: min(|x - 0|, 1 - |x - 0|) ≤ 1/(2n).  Simplify |x-0| = x (since x ≥ 0).
      have hx_abs : |x - 0| = x := by rw [sub_zero]; exact abs_of_nonneg hx
      rw [hx_abs]
      -- (i+1)/n = n/n = 1, so (i+1)/n - x = 1 - x. Combine with h_right_close.
      have h_i_plus_one : ((i.val : ℝ) + 1) / n = 1 := by
        have : ((i.val : ℝ) + 1) = (n : ℝ) := by
          rw [show (i.val : ℝ) + 1 = ((i.val + 1 : ℕ) : ℝ) from by push_cast; rfl]
          rw [hi_eq]
        rw [this]; exact div_self hn_ne
      have h_expand : ((i.val : ℝ) + 1) / n - x = 1 / n - (x - (i.val : ℝ) / n) := by
        rw [h_diff_1]; ring
      have h_close_to_1 : 1 - x ≤ 1 / (2 * n) := by
        have step1 : 1 - x = ((i.val : ℝ) + 1) / n - x := by rw [h_i_plus_one]
        rw [step1, h_expand]; exact h_right_close
      exact le_trans (min_le_right _ _) h_close_to_1

/-- For `n > 0`, `circleDist (i/n) (j/n) = cycleDist n i j / n`. -/
theorem latticeEmbed_isometry {n : Nat} (hn : 0 < n) (i j : Fin n) :
    circleDist (latticeEmbed n i) (latticeEmbed n j) =
      (cycleDist n i j : ℝ) / n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_inv_pos : (0 : ℝ) < 1 / n := by positivity
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  -- Symmetrise: WLOG i.val ≤ j.val.
  suffices h : ∀ i j : Fin n, i.val ≤ j.val →
      circleDist (latticeEmbed n i) (latticeEmbed n j) =
        (cycleDist n i j : ℝ) / n by
    by_cases hij : i.val ≤ j.val
    · exact h i j hij
    · push_neg at hij
      have hji : j.val ≤ i.val := le_of_lt hij
      have e1 : circleDist (latticeEmbed n i) (latticeEmbed n j) =
                circleDist (latticeEmbed n j) (latticeEmbed n i) := circleDist_symm _ _
      have e2 : cycleDist n i j = cycleDist n j i := cycleDist_symm i j
      rw [e1, e2]; exact h j i hji
  -- The i.val ≤ j.val case.
  intro i j hij
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  -- Let d := j.val - i.val. Then 0 ≤ d ≤ n.
  set d : ℕ := j.val - i.val with hd_def
  have hd_le : d ≤ n := by
    simp [hd_def]; omega
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  -- First: |i/n - j/n| = d/n.
  have h_abs_eq : |(i.val : ℝ) / n - (j.val : ℝ) / n| = (d : ℝ) / n := by
    have hji_real : (i.val : ℝ) / n ≤ (j.val : ℝ) / n := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hij
      · exact le_of_lt hn_pos
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hji_real)]
    rw [hd_def]; rw [Nat.cast_sub hij]; ring
  -- Second: 1 - d/n = (n - d)/n. [Real subtraction, using d ≤ n.]
  have h_compl_eq : (1 : ℝ) - (d : ℝ) / n = ((n - d : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hd_le]; field_simp
  -- Expand the definition of cycleDist.
  have h_cycle : cycleDist n i j = min d (n - d) := by
    simp [cycleDist, hd_def, hij]
  -- Convert the ℕ-valued min to ℝ.
  have h_cycle_cast : ((cycleDist n i j : ℕ) : ℝ) = min ((d : ℝ)) ((n - d : ℕ) : ℝ) := by
    rw [h_cycle, Nat.cast_min]
  -- Putting it all together.
  unfold circleDist latticeEmbed
  rw [h_abs_eq, h_compl_eq, h_cycle_cast]
  -- Goal: min (d/n) ((n-d)/n) = min d (n-d) / n
  -- Apply: the function x ↦ x/n is monotone for n > 0, so it commutes with min.
  have h_min_div : min ((d : ℝ) / n) (((n - d : ℕ) : ℝ) / n) =
                   min ((d : ℝ)) (((n - d : ℕ) : ℝ)) / n := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    rw [← min_mul_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  exact h_min_div

end Infra
end InfraFormalization
