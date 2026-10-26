/-
Integration of 1-forms over 1-chains of hyperedges.

This module defines `Chain1 V`, a finitely supported function from hyperedges to `ℤ`, the zero
chain, the chain of a single hyperedge, and `integrate ω γ = ∑ γ(e) · ω(e)` over the support of
`γ`.
It proves that the integral over the zero chain is zero.
-/

import InfraFormalization.DeRham

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A function from hyperedges to `ℤ` with finite support. -/
structure Chain1 (V : Type*) where
  coefficients : Hyperedge V → ℤ
  finiteSupport : Set.Finite { e | coefficients e ≠ 0 }

/-- The chain with every coefficient equal to 0. -/
def Chain1.zero (V : Type*) : Chain1 V :=
  { coefficients := fun _ => 0
    finiteSupport := by
      simp }

/-- The chain with coefficient 1 on `e` and 0 elsewhere. -/
noncomputable def Chain1.ofEdge (e : Hyperedge V) : Chain1 V :=
  { coefficients := fun e' => if e' = e then 1 else 0
    finiteSupport := by
      apply Set.Finite.subset (Set.finite_singleton e)
      intro x hx
      by_cases h : x = e
      · simp [h]
      · simp [h] at hx }

/-- `∑ γ(e) · ω(e)` over the finite support of `γ`. -/
noncomputable def integrate (ω : OneForm V) (γ : Chain1 V) : ℝ :=
  ∑ e ∈ γ.finiteSupport.toFinset, (γ.coefficients e : ℝ) * ω e

/-- `integrate ω (Chain1.zero V) = 0`. -/
theorem integrate_zero (ω : OneForm V) :
    integrate ω (Chain1.zero V) = 0 := by
  unfold integrate Chain1.zero
  simp

end InfraFormalization
