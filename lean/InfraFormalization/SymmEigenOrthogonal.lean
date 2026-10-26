/-
Orthogonality of eigenvectors of symmetric real matrices.

This module proves that eigenvectors of a real symmetric matrix with
distinct eigenvalues have dot product 0, using
`(λ − μ) ⟨v, w⟩ = ⟨Mv, w⟩ − ⟨v, Mw⟩ = 0`. It applies the result to the
Laplacian matrix of `cycleHypergraph n`: eigenvectors with distinct
eigenvalues, the constant eigenvector and any mode `1 ≤ k < n`, and two
distinct modes `1 ≤ j, k ≤ n/2` are orthogonal.
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic
import InfraFormalization.CycleMatrixSpectrum

namespace InfraFormalization

open Matrix

variable {n : ℕ}

/-- If `M : Matrix (Fin n) (Fin n) ℝ` is symmetric and `v`, `w` are
eigenvectors with eigenvalues `l ≠ m`, then `v ⬝ᵥ w = 0`. -/
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
  -- l · (v·w) = m · (v·w), so (l − m)(v·w) = 0 and v·w = 0.
  have h_eq : l * (v ⬝ᵥ w) = m * (v ⬝ᵥ w) := by rw [← h_left, h_symm_eq, h_right]
  have h_diff : (l - m) * (v ⬝ᵥ w) = 0 := by
    have h' : l * (v ⬝ᵥ w) - m * (v ⬝ᵥ w) = 0 := by rw [h_eq]; ring
    calc (l - m) * (v ⬝ᵥ w)
        = l * (v ⬝ᵥ w) - m * (v ⬝ᵥ w) := by ring
      _ = 0 := h'
  have h_ne : l - m ≠ 0 := sub_ne_zero.mpr hne
  have := (mul_eq_zero.mp h_diff).resolve_left h_ne
  exact this

/-- For `n ≥ 2`, cycle eigenvectors `j` and `k` with
`cycleEigenvalue n j ≠ cycleEigenvalue n k` have dot product 0. -/
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

/-- For `n ≥ 2` and `1 ≤ k < n`, `cycleEigenvector n 0` and
`cycleEigenvector n k` have dot product 0. -/
theorem cycleEigenvector_const_orthogonal_nonzero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k < n) :
    cycleEigenvector n 0 ⬝ᵥ cycleEigenvector n k = 0 :=
  cycleEigenvector_orthogonal hn (cycleEigenvalue_zero_ne_nonzero_mode k hk_lo hk_hi)

/-- For `n ≥ 2`, `j ≠ k`, `1 ≤ j`, `1 ≤ k`, `2j ≤ n` and `2k ≤ n`,
`cycleEigenvector n j` and `cycleEigenvector n k` have dot product 0. -/
theorem cycleEigenvector_first_half_orthogonal
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) {j k : ℕ}
    (hj_lo : 1 ≤ j) (hjk : j ≠ k) (hj_hi : 2 * j ≤ n) (hk_hi : 2 * k ≤ n)
    (hk_lo : 1 ≤ k) :
    cycleEigenvector n j ⬝ᵥ cycleEigenvector n k = 0 :=
  cycleEigenvector_orthogonal hn
    (cycleEigenvalue_ne_first_half hj_lo hjk hj_hi hk_hi hk_lo)

end InfraFormalization
