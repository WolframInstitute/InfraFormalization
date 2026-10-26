/-
Fisher inner product on probability distributions over a finite set of hypergraph states.

This module defines `BranchialProbability`, a non-negative function on hypergraphs that sums to 1
over a finite set `slice` and vanishes off it, and `FisherInner`, the sum over `slice` of
`δp₁ h * δp₂ h / p h` with zero terms where `p h = 0`.
It proves that `FisherInner` is symmetric in its two tangent arguments.
-/

import InfraFormalization.Branchial
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A function `p : Hypergraph V → ℝ` that is non-negative, sums to 1 over `slice`, and is zero
outside `slice`. -/
structure BranchialProbability (slice : Finset (Hypergraph V)) where
  p : Hypergraph V → ℝ
  nonneg : ∀ h, 0 ≤ p h
  normalised : ∑ h ∈ slice, p h = 1
  support : ∀ h, h ∉ slice → p h = 0

/-- The sum over `h ∈ slice` of `δp₁ h * δp₂ h / μ.p h`, with the term set to 0 where
`μ.p h = 0`. The definition does not require `δp₁` or `δp₂` to sum to zero. -/
noncomputable def FisherInner
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp₁ δp₂ : Hypergraph V → ℝ) : ℝ :=
  ∑ h ∈ slice,
    if μ.p h = 0 then 0
    else (δp₁ h * δp₂ h) / μ.p h

/-- `FisherInner slice μ δp₁ δp₂ = FisherInner slice μ δp₂ δp₁`. -/
theorem fisherInner_symm
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp₁ δp₂ : Hypergraph V → ℝ) :
    FisherInner slice μ δp₁ δp₂ = FisherInner slice μ δp₂ δp₁ := by
  unfold FisherInner
  apply Finset.sum_congr rfl
  intros h _
  by_cases hp : μ.p h = 0
  · simp [hp]
  · rw [if_neg hp, if_neg hp]
    rw [mul_comm]

end InfraFormalization
