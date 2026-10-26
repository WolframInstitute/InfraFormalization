/-
Eigenvectors of the cycle hypergraph Laplacian matrix.

From `cycleLaplacian_eigen`, `laplacianHyper_cycleHypergraph` and
`laplacianMatrix_mulVec`, this module proves that for `n ≥ 2`,
`cycleEigenvector n k` is an eigenvector of
`laplacianMatrix (cycleHypergraph n)` with eigenvalue `cycleEigenvalue n k`,
and that the heat kernel multiplies it by `exp(t · cycleEigenvalue n k)`.
-/

import InfraFormalization.CycleSpectrum
import InfraFormalization.LaplacianMatrix
import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.ExpEigenvector

namespace InfraFormalization

/-- For `n ≥ 2`, `laplacianMatrix (cycleHypergraph n)` maps
`cycleEigenvector n k` to `cycleEigenvalue n k • cycleEigenvector n k`. -/
theorem laplacianMatrix_cycleHypergraph_eigen
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) :
    (Hypergraph.laplacianMatrix (cycleHypergraph n)).mulVec (cycleEigenvector n k)
      = cycleEigenvalue n k • cycleEigenvector n k := by
  funext i
  rw [Hypergraph.laplacianMatrix_mulVec]
  rw [laplacianHyper_cycleHypergraph hn]
  rw [cycleLaplacian_eigen hn k i]
  simp [Pi.smul_apply, smul_eq_mul]

/-- For `n ≥ 2`, `k : ℕ` and `t : ℝ`,
`(heatKernel (cycleHypergraph n) t).mulVec (cycleEigenvector n k)
= Real.exp (t * cycleEigenvalue n k) • cycleEigenvector n k`. -/
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
  -- `exp_mulVec_of_eigenvector`: `exp A` multiplies an eigenvector of `A` with eigenvalue `λ` by `exp λ`.
  exact Hypergraph.exp_mulVec_of_eigenvector
    (t • Hypergraph.laplacianMatrix (cycleHypergraph n))
    (cycleEigenvector n k) (t * cycleEigenvalue n k) h_scaled_eigen

end InfraFormalization
