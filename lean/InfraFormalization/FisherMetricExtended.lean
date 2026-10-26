/-
Algebraic properties of the Fisher inner product.

This module proves, for `FisherInner slice μ` with `μ : BranchialProbability slice`, additivity and
real scaling in each argument, `0 ≤ FisherInner slice μ δp δp`, and that the inner product with the
zero function on either side is 0.
-/

import InfraFormalization.FisherMetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `FisherInner` is additive in its first function argument. -/
theorem fisherInner_add_left
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp₁ δp₂ δp₃ : Hypergraph V → ℝ) :
    FisherInner slice μ (fun h => δp₁ h + δp₂ h) δp₃
      = FisherInner slice μ δp₁ δp₃ + FisherInner slice μ δp₂ δp₃ := by
  unfold FisherInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros h _
  by_cases hp : μ.p h = 0
  · simp [hp]
  · rw [if_neg hp, if_neg hp, if_neg hp]
    have : δp₁ h * δp₃ h + δp₂ h * δp₃ h = (δp₁ h + δp₂ h) * δp₃ h := by ring
    rw [← this]
    rw [add_div]

/-- `FisherInner` is additive in its second function argument. The proof uses `fisherInner_symm`
and `fisherInner_add_left`. -/
theorem fisherInner_add_right
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp₁ δp₂ δp₃ : Hypergraph V → ℝ) :
    FisherInner slice μ δp₁ (fun h => δp₂ h + δp₃ h)
      = FisherInner slice μ δp₁ δp₂ + FisherInner slice μ δp₁ δp₃ := by
  rw [fisherInner_symm, fisherInner_add_left,
      fisherInner_symm slice μ δp₂ δp₁, fisherInner_symm slice μ δp₃ δp₁]

/-- `FisherInner slice μ (c · δp₁) δp₂ = c · FisherInner slice μ δp₁ δp₂`. -/
theorem fisherInner_smul_left
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice) (c : ℝ)
    (δp₁ δp₂ : Hypergraph V → ℝ) :
    FisherInner slice μ (fun h => c * δp₁ h) δp₂
      = c * FisherInner slice μ δp₁ δp₂ := by
  unfold FisherInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros h _
  by_cases hp : μ.p h = 0
  · simp [hp]
  · rw [if_neg hp, if_neg hp]
    rw [mul_assoc, mul_div_assoc]

/-- `FisherInner slice μ δp₁ (c · δp₂) = c · FisherInner slice μ δp₁ δp₂`. -/
theorem fisherInner_smul_right
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice) (c : ℝ)
    (δp₁ δp₂ : Hypergraph V → ℝ) :
    FisherInner slice μ δp₁ (fun h => c * δp₂ h)
      = c * FisherInner slice μ δp₁ δp₂ := by
  rw [fisherInner_symm, fisherInner_smul_left,
      fisherInner_symm slice μ δp₂ δp₁]

/-- `0 ≤ FisherInner slice μ δp δp`. -/
theorem fisherInner_self_nonneg
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp : Hypergraph V → ℝ) :
    0 ≤ FisherInner slice μ δp δp := by
  unfold FisherInner
  refine Finset.sum_nonneg (fun h _ => ?_)
  by_cases hp : μ.p h = 0
  · simp [hp]
  · rw [if_neg hp]
    have h_denom_nonneg : 0 ≤ μ.p h := μ.nonneg h
    have h_num_nonneg : 0 ≤ δp h * δp h := mul_self_nonneg _
    exact div_nonneg h_num_nonneg h_denom_nonneg

/-- `FisherInner slice μ 0 δp = 0`. -/
theorem fisherInner_zero_left
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp : Hypergraph V → ℝ) :
    FisherInner slice μ (fun _ => 0) δp = 0 := by
  unfold FisherInner
  apply Finset.sum_eq_zero
  intros h _
  by_cases hp : μ.p h = 0
  · simp [hp]
  · rw [if_neg hp]; simp

/-- `FisherInner slice μ δp 0 = 0`. -/
theorem fisherInner_zero_right
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp : Hypergraph V → ℝ) :
    FisherInner slice μ δp (fun _ => 0) = 0 := by
  rw [fisherInner_symm, fisherInner_zero_left]

end InfraFormalization
