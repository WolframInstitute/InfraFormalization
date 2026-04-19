/-
Scaled cycle graphs and their metric structure.

We define the cycle on `n` vertices (`Fin n`) with the shortest-path
graph metric scaled by `1/n`. The long-term goal of this file is the
Gromov–Hausdorff convergence

  (C_n, d_graph/n)  →  ℝ/ℤ  as n → ∞.

This is the first continuum-limit target of the infrageometry
programme's Phase 3. This file establishes definitional infrastructure
and proves the bare combinatorial facts needed downstream.

**Discipline:** no `sorry`, no `decide`/`native_decide`, no custom
axioms. Every theorem here depends only on Lean's three standard
axioms.
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

/-- `cycleDist n i j ≤ n / 2` — the diameter of the cycle graph on `n`
vertices is at most `⌊n/2⌋`. -/
theorem cycleDist_le_half {n : Nat} (i j : Fin n) :
    cycleDist n i j ≤ n / 2 := by
  unfold cycleDist
  -- Simply handle the two branches of the `if`.
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

/-- Degenerate diameter: on `C_0` and `C_1`, the cycle distance is
trivially 0. -/
theorem cycleDist_zero_of_small {n : Nat} (hn : n ≤ 1) (i j : Fin n) :
    cycleDist n i j = 0 := by
  unfold cycleDist
  interval_cases n
  · exact i.elim0
  · have : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    simp [this, hj]

end Infra
end InfraFormalization
