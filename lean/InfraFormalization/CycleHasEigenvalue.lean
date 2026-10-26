/-
Cycle Laplacian eigenvalues in `Module.End.HasEigenvalue` form.

This module restates `laplacianMatrix_cycleHypergraph_eigen` as
`Module.End.HasEigenvalue (Matrix.toLin' (laplacianMatrix (cycleHypergraph n)))
(cycleEigenvalue n k)`.
-/

import InfraFormalization.CycleMatrixSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace InfraFormalization

open Module

/-- The cycle eigenvector takes the value 1 at index 0. -/
lemma cycleEigenvector_zero_val (n k : ℕ) [NeZero n] :
    cycleEigenvector n k (0 : Fin n) = 1 := by
  unfold cycleEigenvector
  simp

/-- `cycleEigenvector n k` is a nonzero function (viewed as `Fin n → ℝ`). -/
lemma cycleEigenvector_ne_zero (n k : ℕ) [NeZero n] :
    cycleEigenvector n k ≠ (0 : Fin n → ℝ) := by
  intro h
  have : cycleEigenvector n k (0 : Fin n) = 0 := by rw [h]; rfl
  rw [cycleEigenvector_zero_val] at this
  exact one_ne_zero this

/-- For `n ≥ 2`, the linear map of the cycle-hypergraph Laplacian matrix has
`cycleEigenvalue n k = -4 sin²(πk/n)` as an eigenvalue, with eigenvector
`cycleEigenvector n k`. -/
theorem laplacianMatrix_cycleHypergraph_hasEigenvalue
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) :
    Module.End.HasEigenvalue
      (Matrix.toLin' (Hypergraph.laplacianMatrix (cycleHypergraph n)))
      (cycleEigenvalue n k) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, cycleEigenvector_ne_zero n k⟩
  rw [Module.End.mem_eigenspace_iff]
  -- Goal: `Matrix.toLin' M (cycleEigenvector n k) = cycleEigenvalue n k • cycleEigenvector n k`.
  rw [Matrix.toLin'_apply]
  exact laplacianMatrix_cycleHypergraph_eigen hn k

end InfraFormalization
