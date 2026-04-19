/-
Packaged continuum-limit theorem: the scaled n-cycle is within
Gromov-Hausdorff distance `1 / (2n)` of the unit circle ℝ/ℤ.

This file packages `latticeEmbed_covers` (T19, the (1/(2n))-cover bound)
and `latticeEmbed_isometry` (T20, metric preservation by the embedding)
into a single named GH-distance-bound theorem.

Rather than invoking Mathlib's full `GromovHausdorff.GHSpace` quotient
(which is heavy machinery for our purposes), we state the bound in its
direct ε-approximation form: there exists a map `f : Fin n → ℝ`
whose image lies in `[0, 1)`, that is an isometry from `(Fin n,
cycleDist/n)` into `(ℝ, circleDist)`, and whose image is
(1/(2n))-Hausdorff-dense. This is equivalent to the GH bound and is
more directly usable for downstream theorems.
-/

import InfraFormalization.Infra.Circle

namespace InfraFormalization
namespace Infra

/-- The scaled n-cycle is (1/(2n))-GH-close to the unit circle ℝ/ℤ.
More precisely: there exists an isometric embedding `Fin n → [0,1)`
whose image is (1/(2n))-Hausdorff-dense in `[0, 1)`. -/
theorem cycle_circle_gh_bound (n : Nat) (hn : 0 < n) :
    ∃ f : Fin n → ℝ,
      (∀ i, 0 ≤ f i ∧ f i < 1) ∧
      (∀ i j, circleDist (f i) (f j) = (cycleDist n i j : ℝ) / n) ∧
      (∀ x, 0 ≤ x → x < 1 → ∃ i, circleDist x (f i) ≤ 1 / (2 * n)) := by
  refine ⟨latticeEmbed n, ?_, ?_, ?_⟩
  · intro i; exact latticeEmbed_mem_unit_interval hn i
  · intro i j; exact latticeEmbed_isometry hn i j
  · intro x hx hx'; exact latticeEmbed_covers hn x hx hx'

/-- **Convergence corollary.** The maximum circle-distance from any
point of `[0, 1)` to the lattice image is at most `1 / (2n)`, which
tends to zero as `n → ∞`. Explicitly: for every `ε > 0`, for
sufficiently large `n`, the lattice is `ε`-dense in `[0, 1)`. -/
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
