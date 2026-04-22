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
import InfraFormalization.ExpEigenvector

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

/-- **Heat kernel acts on the cycle eigenvector with eigenvalue
`Real.exp (t · λ_k)`**. Composes T2 (`exp_mulVec_of_eigenvector`) with
the matrix eigenvalue equation: for `n ≥ 2` and any `k : ℕ`, `t : ℝ`,

  `(heatKernel (cycleHypergraph n) t).mulVec (cycleEigenvector n k)
   = Real.exp (t * cycleEigenvalue n k) • cycleEigenvector n k`.

Concrete statement of heat flow on the cycle: each spatial mode
`cos(2πkj/n)` decays as `exp(−4 t sin²(πk/n))`. -/
theorem heatKernel_cycleHypergraph_mulVec_eigenvector
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (t : ℝ) :
    (Hypergraph.heatKernel (cycleHypergraph n) t).mulVec (cycleEigenvector n k)
      = Real.exp (t * cycleEigenvalue n k) • cycleEigenvector n k := by
  unfold Hypergraph.heatKernel
  -- (t • Δ).mulVec v = (t * λ) • v from Δ.mulVec v = λ • v.
  have h_scaled_eigen :
      (t • Hypergraph.laplacianMatrix (cycleHypergraph n)).mulVec
        (cycleEigenvector n k)
      = (t * cycleEigenvalue n k) • cycleEigenvector n k := by
    rw [Matrix.smul_mulVec, laplacianMatrix_cycleHypergraph_eigen hn k]
    ext i
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  -- Apply T2: exp(A) fixes eigenvectors with exp(λ).
  exact Hypergraph.exp_mulVec_of_eigenvector
    (t • Hypergraph.laplacianMatrix (cycleHypergraph n))
    (cycleEigenvector n k) (t * cycleEigenvalue n k) h_scaled_eigen

end InfraFormalization
