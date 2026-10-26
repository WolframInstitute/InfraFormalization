/-
Two-dimensional torus lattice with metric scaled by `1/n`.

This module defines the L∞ product `torusLatticeDist` of two cycle distances on `Fin n × Fin n`,
the L∞ product `torusDist` of two circle distances on ℝ × ℝ, and the embedding
`torusEmbed n (i, j) = (i/n, j/n)`. It proves that the embedding scales distances by `1/n` and that
every point of [0, 1)² is within `1/(2n)` of its image.
-/

import InfraFormalization.Infra.ScaledCycle
import InfraFormalization.Infra.Circle

namespace InfraFormalization
namespace Infra

/-- L∞ product of cycle distances on `Fin n × Fin n`:
`torusLatticeDist n (i₁, i₂) (j₁, j₂) = max (cycleDist n i₁ j₁) (cycleDist n i₂ j₂)`. -/
def torusLatticeDist (n : Nat) (p q : Fin n × Fin n) : Nat :=
  max (cycleDist n p.1 q.1) (cycleDist n p.2 q.2)

@[simp] theorem torusLatticeDist_self {n : Nat} (p : Fin n × Fin n) :
    torusLatticeDist n p p = 0 := by
  simp [torusLatticeDist]

theorem torusLatticeDist_symm {n : Nat} (p q : Fin n × Fin n) :
    torusLatticeDist n p q = torusLatticeDist n q p := by
  unfold torusLatticeDist
  rw [cycleDist_symm p.1 q.1, cycleDist_symm p.2 q.2]

theorem torusLatticeDist_triangle {n : Nat} (p q r : Fin n × Fin n) :
    torusLatticeDist n p r ≤ torusLatticeDist n p q + torusLatticeDist n q r := by
  unfold torusLatticeDist
  have h1 := cycleDist_triangle p.1 q.1 r.1
  have h2 := cycleDist_triangle p.2 q.2 r.2
  omega

/-- L∞ product of circle distances on ℝ × ℝ:
`torusDist (x₁, x₂) (y₁, y₂) = max (circleDist x₁ y₁) (circleDist x₂ y₂)`. -/
noncomputable def torusDist (p q : ℝ × ℝ) : ℝ :=
  max (circleDist p.1 q.1) (circleDist p.2 q.2)

theorem torusDist_self (p : ℝ × ℝ) : torusDist p p = 0 := by
  simp [torusDist, circleDist_self]

theorem torusDist_symm (p q : ℝ × ℝ) : torusDist p q = torusDist q p := by
  unfold torusDist
  rw [circleDist_symm p.1 q.1, circleDist_symm p.2 q.2]

/-- The embedding `Fin n × Fin n → ℝ × ℝ`, `(i, j) ↦ (i/n, j/n)`. -/
noncomputable def torusEmbed (n : Nat) (p : Fin n × Fin n) : ℝ × ℝ :=
  (latticeEmbed n p.1, latticeEmbed n p.2)

theorem torusEmbed_mem_unit_square {n : Nat} (hn : 0 < n) (p : Fin n × Fin n) :
    (0 ≤ (torusEmbed n p).1 ∧ (torusEmbed n p).1 < 1) ∧
    (0 ≤ (torusEmbed n p).2 ∧ (torusEmbed n p).2 < 1) := by
  exact ⟨latticeEmbed_mem_unit_interval hn p.1, latticeEmbed_mem_unit_interval hn p.2⟩

/-- For `n > 0`, `torusDist (torusEmbed n p) (torusEmbed n q) = torusLatticeDist n p q / n`. -/
theorem torusEmbed_isometry {n : Nat} (hn : 0 < n) (p q : Fin n × Fin n) :
    torusDist (torusEmbed n p) (torusEmbed n q) =
      (torusLatticeDist n p q : ℝ) / n := by
  unfold torusDist torusEmbed torusLatticeDist
  rw [latticeEmbed_isometry hn p.1 q.1, latticeEmbed_isometry hn p.2 q.2]
  -- max(a/n, b/n) = max(a, b)/n for n > 0.
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast [Nat.cast_max]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  rw [← max_mul_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]

/-- For `n > 0`, every `(x, y) ∈ [0, 1) × [0, 1)` is within `torusDist` distance `1/(2n)` of some
`torusEmbed n (i, j)`. -/
theorem torusEmbed_covers {n : Nat} (hn : 0 < n)
    (x y : ℝ) (hx : 0 ≤ x) (hx' : x < 1) (hy : 0 ≤ y) (hy' : y < 1) :
    ∃ p : Fin n × Fin n, torusDist (x, y) (torusEmbed n p) ≤ 1 / (2 * n) := by
  obtain ⟨i, hi⟩ := latticeEmbed_covers hn x hx hx'
  obtain ⟨j, hj⟩ := latticeEmbed_covers hn y hy hy'
  refine ⟨(i, j), ?_⟩
  unfold torusDist torusEmbed
  exact max_le hi hj

/-- For `n > 0`, there is a map `f : Fin n × Fin n → ℝ × ℝ` with values in [0, 1)² such that
`torusDist (f p) (f q) = torusLatticeDist n p q / n` and every point of [0, 1)² is within
`1/(2n)` of the image of `f`. -/
theorem torus_gh_bound (n : Nat) (hn : 0 < n) :
    ∃ f : Fin n × Fin n → ℝ × ℝ,
      (∀ p, 0 ≤ (f p).1 ∧ (f p).1 < 1 ∧ 0 ≤ (f p).2 ∧ (f p).2 < 1) ∧
      (∀ p q, torusDist (f p) (f q) = (torusLatticeDist n p q : ℝ) / n) ∧
      (∀ x y, 0 ≤ x → x < 1 → 0 ≤ y → y < 1 →
        ∃ p, torusDist (x, y) (f p) ≤ 1 / (2 * n)) := by
  refine ⟨torusEmbed n, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨⟨hp1, hp1'⟩, ⟨hp2, hp2'⟩⟩ := torusEmbed_mem_unit_square hn p
    exact ⟨hp1, hp1', hp2, hp2'⟩
  · intro p q; exact torusEmbed_isometry hn p q
  · intro x y hx hx' hy hy'; exact torusEmbed_covers hn x y hx hx' hy hy'

end Infra
end InfraFormalization
