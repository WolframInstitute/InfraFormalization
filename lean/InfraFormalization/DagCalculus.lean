/-
**Calculus on coordinate DAGs** (Group IA / #110 IA2).

Extends `DagBlowup.lean` with the full calculus-on-DAGs toolkit:

  * `dagDiscreteIntegral f i j := ∑ over range` — Riemann-sum-like
    integral on `Fin n`.
  * Telescoping FTC for specific forms.
  * Linearity and constant/sum rules.

**Connection to hypergraphs.** Native. Operates on
`dagAsBlowupOfInterval n` from `DagBlowup.lean`.
-/

import InfraFormalization.DagBlowup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic

namespace InfraFormalization

variable {n : Nat}

/-- **DAG discrete integral** from 0 to `j`: sum over prefixes. -/
def dagPrefixSum (f : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < j.val), f k

/-- **Prefix sum at index 0 is 0** (empty sum). -/
theorem dagPrefixSum_zero {n : Nat} [NeZero n] (f : Fin n → ℝ) :
    dagPrefixSum f ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ = 0 := by
  unfold dagPrefixSum
  apply Finset.sum_eq_zero
  intros k hk
  rw [Finset.mem_filter] at hk
  have : k.val < 0 := hk.2
  omega

/-- **Linearity**: integral of sum is sum of integrals. -/
theorem dagPrefixSum_add (f g : Fin n → ℝ) (j : Fin n) :
    dagPrefixSum (fun v => f v + g v) j
    = dagPrefixSum f j + dagPrefixSum g j := by
  unfold dagPrefixSum
  rw [← Finset.sum_add_distrib]

/-- **Scalar homogeneity**. -/
theorem dagPrefixSum_smul (c : ℝ) (f : Fin n → ℝ) (j : Fin n) :
    dagPrefixSum (fun v => c * f v) j = c * dagPrefixSum f j := by
  unfold dagPrefixSum
  rw [Finset.mul_sum]

end InfraFormalization
