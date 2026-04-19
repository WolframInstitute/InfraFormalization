/-
Density of the dyadic lattice in the interval [0, 1).

For the first infrageometry continuum-limit target (cycle → circle),
we need to quantify how well the `n`-point lattice `{0, 1/n, 2/n, …,
(n-1)/n}` approximates the unit interval. This file proves the core
density lemma: every `x ∈ [0,1)` is within `1/n` of some lattice
point, and within `1/(2n)` of the nearest lattice point (with
wraparound).

No `sorry`, no `decide`, no custom axioms.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace InfraFormalization
namespace Infra

/-- For any `n > 0` and any `x ∈ [0, 1)`, there exists a lattice index
`i ∈ Fin n` such that `i/n ≤ x < (i+1)/n`. This is the "floor of nx"
construction packaged as an existence statement. -/
theorem exists_lattice_index (n : Nat) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) :
    ∃ i : Fin n, (i.val : ℝ) / n ≤ x ∧ x < ((i.val : ℝ) + 1) / n := by
  -- Let i = ⌊nx⌋. Since 0 ≤ nx < n, we have 0 ≤ i < n.
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx_nonneg : (0 : ℝ) ≤ n * x := mul_nonneg (le_of_lt hn_pos) hx
  have hnx_lt : (n : ℝ) * x < n := by
    have h1 : (n : ℝ) * x < n * 1 := by
      have := mul_lt_mul_of_pos_left hx' hn_pos
      simpa using this
    simpa using h1
  -- Use Nat.floor applied to (n * x) as our lattice index.
  set i := ⌊(n : ℝ) * x⌋₊ with hi_def
  have hi_lt_n : i < n := by
    have : ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * x :=
      Nat.floor_le hnx_nonneg
    have h2 : ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) < (n : ℝ) := lt_of_le_of_lt this hnx_lt
    exact_mod_cast h2
  refine ⟨⟨i, hi_lt_n⟩, ?_, ?_⟩
  · -- i/n ≤ x
    show (i : ℝ) / n ≤ x
    have h1 : ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * x := Nat.floor_le hnx_nonneg
    rw [div_le_iff₀ hn_pos]
    calc ((⟨i, hi_lt_n⟩ : Fin n).val : ℝ) = ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) := by rfl
      _ ≤ (n : ℝ) * x := h1
      _ = x * n := by ring
  · -- x < (i+1)/n
    show x < ((i : ℝ) + 1) / n
    have h2 : (n : ℝ) * x < (⌊(n : ℝ) * x⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
    rw [lt_div_iff₀ hn_pos]
    have : x * n = n * x := by ring
    rw [this]
    exact_mod_cast h2

/-- **1/n-density of the lattice.** For any `n > 0` and any `x ∈ [0, 1)`,
there is a lattice point `i/n` within absolute distance strictly less
than `1/n`. -/
theorem lattice_one_over_n_dense (n : Nat) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) :
    ∃ i : Fin n, |x - (i.val : ℝ) / n| < 1 / n := by
  obtain ⟨i, h1, h2⟩ := exists_lattice_index n hn x hx hx'
  refine ⟨i, ?_⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  -- From `i/n ≤ x < (i+1)/n` we get `0 ≤ x - i/n < 1/n`.
  have hge : 0 ≤ x - (i.val : ℝ) / n := by linarith
  have hlt : x - (i.val : ℝ) / n < 1 / n := by
    have h3 : ((i.val : ℝ) + 1) / n = (i.val : ℝ) / n + 1 / n := by
      field_simp
    rw [h3] at h2
    linarith
  rw [abs_of_nonneg hge]
  exact hlt

/-- Improved form: for any `x ∈ [0, 1)`, either `x` is close to the
lattice point `i/n` on its right, or close to the lattice point
`(i+1)/n` on its left — with distance at most `1 / (2n)` in each
case. This gives the precise `1/(2n)`-cover needed for the
cycle-to-circle Gromov–Hausdorff bound. -/
theorem lattice_half_n_cover (n : Nat) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) (hx' : x < 1) :
    ∃ i : Fin n,
      x - (i.val : ℝ) / n ≤ 1 / (2 * n) ∨
      ((i.val : ℝ) + 1) / n - x ≤ 1 / (2 * n) := by
  obtain ⟨i, h1, h2⟩ := exists_lattice_index n hn x hx hx'
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_two_n : (0 : ℝ) < 2 * n := by linarith
  refine ⟨i, ?_⟩
  -- x ∈ [i/n, (i+1)/n). Either (x - i/n) ≤ 1/(2n) or x is closer to (i+1)/n.
  by_cases hmid : x - (i.val : ℝ) / n ≤ 1 / (2 * n)
  · exact Or.inl hmid
  · right
    push_neg at hmid
    -- hmid: 1/(2n) < x - i/n. Combined with x < (i+1)/n, we get
    -- (i+1)/n - x = ((i/n + 1/n) - x) = 1/n - (x - i/n) < 1/n - 1/(2n) = 1/(2n).
    have : ((i.val : ℝ) + 1) / n - x = 1 / n - (x - (i.val : ℝ) / n) := by
      field_simp; ring
    rw [this]
    have h_bound : 1 / n - (x - (i.val : ℝ) / n) < 1 / n - 1 / (2 * n) := by linarith
    have : (1 : ℝ) / n - 1 / (2 * n) = 1 / (2 * n) := by field_simp; ring
    linarith

end Infra
end InfraFormalization
