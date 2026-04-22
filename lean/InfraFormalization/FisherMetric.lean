/-
**Fisher information metric on a branchial graph** (Group IQ / #152 IQ5).

For a probability distribution on a branchial slice, the Fisher
metric is a Riemannian metric on the space of distributions. In
the continuum limit, this converges to the Fubini-Study metric on
`ℂP^n` (IQ6, follow-up).

This file gives the predicate-level definition for discrete
branchial slices.

**Connection to hypergraphs.** Native. Branchial slices are sets of
`Hypergraph V` states; probability distributions are functions
`slice → ℝ` with `∑ p = 1`.
-/

import InfraFormalization.Branchial
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Branchial probability distribution** on a finite slice: a
function `slice → ℝ` that is non-negative and sums to 1. We work
with a `Finset` representation of the slice. -/
structure BranchialProbability (slice : Finset (Hypergraph V)) where
  p : Hypergraph V → ℝ
  nonneg : ∀ h, 0 ≤ p h
  normalised : ∑ h ∈ slice, p h = 1
  support : ∀ h, h ∉ slice → p h = 0

/-- **Fisher inner product** between two tangent vectors at a point
`μ` in the space of probabilities. Tangent vectors are functions
`δp : slice → ℝ` with `∑ δp = 0`. -/
noncomputable def FisherInner
    (slice : Finset (Hypergraph V))
    (μ : BranchialProbability slice)
    (δp₁ δp₂ : Hypergraph V → ℝ) : ℝ :=
  ∑ h ∈ slice,
    if μ.p h = 0 then 0
    else (δp₁ h * δp₂ h) / μ.p h

/-- **Fisher inner product is symmetric**. -/
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
