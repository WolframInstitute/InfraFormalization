/-
The n-cycle with distance scaled by `1/n` embeds isometrically in the circle ℝ/ℤ with a
`1/(2n)`-dense image.

The statement uses the direct form, not Mathlib's `GromovHausdorff.GHSpace`: a map
`f : Fin n → [0, 1)` with `circleDist (f i) (f j) = cycleDist n i j / n`, such that every
`x ∈ [0, 1)` lies within circle distance `1/(2n)` of some `f i`. The proof combines
`latticeEmbed_isometry` and `latticeEmbed_covers`. A second theorem states that the
lattice image is `ε`-dense for every `ε > 0` and all sufficiently large `n`.
-/

import InfraFormalization.Infra.Circle

namespace InfraFormalization
namespace Infra

/-- For `n > 0` there is a map `f : Fin n → [0, 1)` with
`circleDist (f i) (f j) = cycleDist n i j / n` whose image is within circle distance
`1/(2n)` of every point of `[0, 1)`. -/
theorem cycle_circle_gh_bound (n : Nat) (hn : 0 < n) :
    ∃ f : Fin n → ℝ,
      (∀ i, 0 ≤ f i ∧ f i < 1) ∧
      (∀ i j, circleDist (f i) (f j) = (cycleDist n i j : ℝ) / n) ∧
      (∀ x, 0 ≤ x → x < 1 → ∃ i, circleDist x (f i) ≤ 1 / (2 * n)) := by
  refine ⟨latticeEmbed n, ?_, ?_, ?_⟩
  · intro i; exact latticeEmbed_mem_unit_interval hn i
  · intro i j; exact latticeEmbed_isometry hn i j
  · intro x hx hx'; exact latticeEmbed_covers hn x hx hx'

/-- For every `ε > 0` there is `N` such that for all `n ≥ N`, every `x ∈ [0, 1)` lies
within circle distance `ε` of some `latticeEmbed n i`. -/
theorem cycle_circle_eventual_epsilon_dense (ε : ℝ) (hε : 0 < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ x, 0 ≤ x → x < 1 →
        ∃ i : Fin n, circleDist x (latticeEmbed n i) ≤ ε := by
  -- Take N so that 1/(2N) ≤ ε, i.e., N ≥ 1/(2ε).
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (2 * ε))
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn_pos : 0 < n := by omega
  have hn_ge : (1 : ℝ) / (2 * ε) < n := by
    have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (le_max_left _ _) hn)
    linarith
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h2n_pos : (0 : ℝ) < 2 * n := by linarith
  have h2eps_pos : (0 : ℝ) < 2 * ε := by linarith
  have h_bound : (1 : ℝ) / (2 * n) ≤ ε := by
    rw [div_le_iff₀ h2n_pos]
    -- Goal: 1 ≤ ε * (2 * n)
    -- We have: 1/(2ε) < n, so 1 < 2εn, so 1 ≤ ε * (2 * n).
    have : 1 / (2 * ε) < (n : ℝ) := hn_ge
    have h1 : 1 < (n : ℝ) * (2 * ε) := by
      have h2 : 1 / (2 * ε) * (2 * ε) < (n : ℝ) * (2 * ε) :=
        mul_lt_mul_of_pos_right this h2eps_pos
      rwa [one_div_mul_cancel (ne_of_gt h2eps_pos)] at h2
    linarith
  intro x hx hx'
  obtain ⟨i, hi⟩ := latticeEmbed_covers hn_pos x hx hx'
  exact ⟨i, le_trans hi h_bound⟩

end Infra
end InfraFormalization
