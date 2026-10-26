/-
Prefix sums on `Fin n`.

This module defines `dagPrefixSum f j`, the sum of `f k` over `k < j`, and
proves that it vanishes at `j = 0` and is linear in `f`.
-/

import InfraFormalization.DagBlowup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic

namespace InfraFormalization

variable {n : Nat}

/-- The sum of `f k` over all `k : Fin n` with `k < j`. -/
def dagPrefixSum (f : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < j.val), f k

/-- The prefix sum at index 0 is 0. -/
theorem dagPrefixSum_zero {n : Nat} [NeZero n] (f : Fin n → ℝ) :
    dagPrefixSum f ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ = 0 := by
  unfold dagPrefixSum
  apply Finset.sum_eq_zero
  intros k hk
  rw [Finset.mem_filter] at hk
  have : k.val < 0 := hk.2
  omega

/-- The prefix sum of `f + g` is the sum of the prefix sums of `f` and `g`. -/
theorem dagPrefixSum_add (f g : Fin n → ℝ) (j : Fin n) :
    dagPrefixSum (fun v => f v + g v) j
    = dagPrefixSum f j + dagPrefixSum g j := by
  unfold dagPrefixSum
  rw [← Finset.sum_add_distrib]

/-- The prefix sum of `c * f` is `c` times the prefix sum of `f`. -/
theorem dagPrefixSum_smul (c : ℝ) (f : Fin n → ℝ) (j : Fin n) :
    dagPrefixSum (fun v => c * f v) j = c * dagPrefixSum f j := by
  unfold dagPrefixSum
  rw [Finset.mul_sum]

end InfraFormalization
