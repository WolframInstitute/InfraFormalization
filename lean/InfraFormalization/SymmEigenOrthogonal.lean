/-
**Symmetric-matrix eigenvector orthogonality** (infrastructure for D6).

A classical finite-dimensional spectral-theorem fact: eigenvectors
of a real symmetric matrix with distinct eigenvalues are orthogonal
under the standard ℓ² inner product on `Fin n → ℝ`.

This is the key ingredient for eigenbasis decomposition on the
cycle hypergraph, needed to close full D6 (long-time heat convergence
for arbitrary initial data on the eigenbasis).

The proof is `(λ − μ) ⟨v, w⟩ = ⟨Mv, w⟩ − ⟨v, Mw⟩ = 0` using `M.IsSymm`
and `dotProduct_mulVec`.
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic
import InfraFormalization.CycleMatrixSpectrum

namespace InfraFormalization

open Matrix

variable {n : ℕ}

/-- **Eigenvector orthogonality for a symmetric real matrix.**

If `M : Matrix (Fin n) (Fin n) ℝ` is symmetric, and `v`, `w` are
eigenvectors with distinct eigenvalues `λ ≠ μ`, then their dot product
vanishes: `∑ i, v i * w i = 0`. -/
theorem symm_eigenvectors_orthogonal
    (M : Matrix (Fin n) (Fin n) ℝ) (hsymm : M.IsSymm)
    {v w : Fin n → ℝ} {l m : ℝ}
    (hv : M.mulVec v = l • v) (hw : M.mulVec w = m • w)
    (hne : l ≠ m) :
    v ⬝ᵥ w = 0 := by
  have h_left : M.mulVec v ⬝ᵥ w = l * (v ⬝ᵥ w) := by
    rw [hv, smul_dotProduct]; rfl
  have h_right : v ⬝ᵥ M.mulVec w = m * (v ⬝ᵥ w) := by
    rw [hw, dotProduct_smul]; rfl
  -- Symmetry gives ⟨Mv, w⟩ = ⟨v, M w⟩.
  have h_symm_eq : M.mulVec v ⬝ᵥ w = v ⬝ᵥ M.mulVec w := by
    rw [dotProduct_mulVec]
    rw [← Matrix.mulVec_transpose]
    have h_Mt : Mᵀ = M := hsymm
    rw [h_Mt]
  -- Combine: l · (v·w) = m · (v·w), so (l − m)(v·w) = 0 ⇒ v·w = 0.
  have h_eq : l * (v ⬝ᵥ w) = m * (v ⬝ᵥ w) := by rw [← h_left, h_symm_eq, h_right]
  have h_diff : (l - m) * (v ⬝ᵥ w) = 0 := by
    have h' : l * (v ⬝ᵥ w) - m * (v ⬝ᵥ w) = 0 := by rw [h_eq]; ring
    calc (l - m) * (v ⬝ᵥ w)
        = l * (v ⬝ᵥ w) - m * (v ⬝ᵥ w) := by ring
      _ = 0 := h'
  have h_ne : l - m ≠ 0 := sub_ne_zero.mpr hne
  have := (mul_eq_zero.mp h_diff).resolve_left h_ne
  exact this

/-- **Cycle eigenvector orthogonality** — immediate consequence of
`symm_eigenvectors_orthogonal` applied to the symmetric cycle
Laplacian matrix. Two cycle eigenvectors with distinct eigenvalues
are orthogonal under the standard dot product on `Fin n → ℝ`. -/
theorem cycleEigenvector_orthogonal
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) {j k : ℕ}
    (hjk : cycleEigenvalue n j ≠ cycleEigenvalue n k) :
    cycleEigenvector n j ⬝ᵥ cycleEigenvector n k = 0 :=
  symm_eigenvectors_orthogonal
    (Hypergraph.laplacianMatrix (cycleHypergraph n))
    (Hypergraph.laplacianMatrix_symm _)
    (laplacianMatrix_cycleHypergraph_eigen hn j)
    (laplacianMatrix_cycleHypergraph_eigen hn k)
    hjk

/-- **Constant mode is orthogonal to every non-constant mode**
(specialization). For `1 ≤ k < n`, the constant eigenvector
`cycleEigenvector n 0` (= 1 everywhere) has dot product `0` with
`cycleEigenvector n k`. Automatic from
`cycleEigenvector_orthogonal` + `cycleEigenvalue_zero_ne_nonzero_mode`. -/
theorem cycleEigenvector_const_orthogonal_nonzero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k < n) :
    cycleEigenvector n 0 ⬝ᵥ cycleEigenvector n k = 0 :=
  cycleEigenvector_orthogonal hn (cycleEigenvalue_zero_ne_nonzero_mode k hk_lo hk_hi)

/-- **Distinct first-half eigenvectors are pairwise orthogonal.** For
`1 ≤ j < k ≤ n/2`, the cycle eigenvectors `cycleEigenvector n j` and
`cycleEigenvector n k` have dot product zero. Closes the pairwise
orthogonality of the first-half eigenvectors — a substantial part of
the orthonormal-eigenbasis structure needed for full D6. -/
theorem cycleEigenvector_first_half_orthogonal
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) {j k : ℕ}
    (hj_lo : 1 ≤ j) (hjk : j ≠ k) (hj_hi : 2 * j ≤ n) (hk_hi : 2 * k ≤ n)
    (hk_lo : 1 ≤ k) :
    cycleEigenvector n j ⬝ᵥ cycleEigenvector n k = 0 :=
  cycleEigenvector_orthogonal hn
    (cycleEigenvalue_ne_first_half hj_lo hjk hj_hi hk_hi hk_lo)

end InfraFormalization
