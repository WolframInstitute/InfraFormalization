/-
**Cycle hypergraph Laplacian matrix: explicit eigenvalue / eigenvector pair** (R2/R5 extension).

Combines three earlier theorems:
  * `cycleLaplacian_eigen` — the cycle Laplacian applied to `cycleEigenvector`
    gives the eigenvalue times the eigenvector, at all indices `i : Fin n`
    (including wrap).
  * `laplacianHyper_cycleHypergraph` — the hypergraph Laplacian on the cycle
    hypergraph equals `cycleLaplacian` pointwise.
  * `laplacianMatrix_mulVec` — the matrix action equals the hypergraph Laplacian.

Result: the eigenvector `cycleEigenvector n k : Fin n → ℝ` is a genuine
matrix eigenvector of `laplacianMatrix (cycleHypergraph n)` with
eigenvalue `cycleEigenvalue n k`.
-/

import InfraFormalization.CycleSpectrum
import InfraFormalization.LaplacianMatrix
import InfraFormalization.HypergraphCycleBridge

namespace InfraFormalization

/-- **Matrix eigenvalue equation** for the cycle hypergraph Laplacian:
the Mathlib matrix `laplacianMatrix (cycleHypergraph n)` has
`cycleEigenvector n k` as an eigenvector with eigenvalue
`cycleEigenvalue n k`. -/
theorem laplacianMatrix_cycleHypergraph_eigen
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) :
    (Hypergraph.laplacianMatrix (cycleHypergraph n)).mulVec (cycleEigenvector n k)
      = cycleEigenvalue n k • cycleEigenvector n k := by
  funext i
  rw [Hypergraph.laplacianMatrix_mulVec]
  rw [laplacianHyper_cycleHypergraph hn]
  rw [cycleLaplacian_eigen hn k i]
  simp [Pi.smul_apply, smul_eq_mul]

end InfraFormalization
