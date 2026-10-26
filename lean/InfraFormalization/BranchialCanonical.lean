/-
Adjacency operator of `BranchialRelated` on a finite branchial slice.

For a rewriting system `sys`, a seed `s₀` and a depth `n` with finite
slice `BranchialSlice sys s₀ n`, this module defines the relation
`branchialSliceAdj` (`BranchialRelated` restricted to the slice) and
the ℂ-linear operator `branchialSliceHamiltonian`, which is
`branchialAdjLM` of that relation on `BranchialHilbert`. It proves the
relation symmetric and the operator self-adjoint for the inner product,
and packages the operator as a `BranchialObservable`.
-/

import InfraFormalization.BranchialHilbert
import InfraFormalization.BranchialSchrodinger
import InfraFormalization.BranchialFinite

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

section
open Classical

/-- Two states of the depth-`n` slice are adjacent when they are
`BranchialRelated` under `sys`. -/
noncomputable def branchialSliceAdj (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : ℕ) :
    ↑(BranchialSlice sys s₀ n) → ↑(BranchialSlice sys s₀ n) → Prop :=
  fun s₁ s₂ => BranchialRelated sys s₁.val s₂.val

/-- `branchialSliceAdj` is symmetric, by `branchial_symm`. -/
theorem branchialSliceAdj_symm (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : ℕ) :
    ∀ a b : ↑(BranchialSlice sys s₀ n),
      branchialSliceAdj sys s₀ n a b → branchialSliceAdj sys s₀ n b a :=
  fun _ _ h => branchial_symm sys h

/-- The ℂ-linear adjacency operator `branchialAdjLM` of
`branchialSliceAdj` on `BranchialHilbert ↑(BranchialSlice sys s₀ n)`.
Decidability of the relation is supplied classically. -/
noncomputable def branchialSliceHamiltonian (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : ℕ) (h : BranchialSliceFinite sys s₀ n) :
    letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
    BranchialHilbert ↑(BranchialSlice sys s₀ n) →ₗ[ℂ]
      BranchialHilbert ↑(BranchialSlice sys s₀ n) :=
  letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
  letI : DecidableEq ↑(BranchialSlice sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  letI : DecidableRel (branchialSliceAdj sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  branchialAdjLM (branchialSliceAdj sys s₀ n)

/-- `branchialSliceHamiltonian` is self-adjoint:
`⟨H φ, ψ⟩ = ⟨φ, H ψ⟩` for all `φ, ψ`. Proved from `branchialAdjLM_inner`
and `branchialSliceAdj_symm`. -/
theorem branchialSliceHamiltonian_isSymm
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) :
    letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
    ∀ φ ψ : BranchialHilbert ↑(BranchialSlice sys s₀ n),
      @inner ℂ _ _ ((branchialSliceHamiltonian sys s₀ n h) φ) ψ
      = @inner ℂ _ _ φ ((branchialSliceHamiltonian sys s₀ n h) ψ) := by
  letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
  letI : DecidableEq ↑(BranchialSlice sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  letI : DecidableRel (branchialSliceAdj sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  intro φ ψ
  exact branchialAdjLM_inner (branchialSliceAdj sys s₀ n)
    (branchialSliceAdj_symm sys s₀ n) φ ψ

/-- `branchialSliceHamiltonian` as a `BranchialObservable`. -/
noncomputable def branchialSliceObservable
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) :
    letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
    BranchialObservable ↑(BranchialSlice sys s₀ n) :=
  letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
  { op := branchialSliceHamiltonian sys s₀ n h
    isSymm := branchialSliceHamiltonian_isSymm sys s₀ n h }

end

end InfraFormalization
