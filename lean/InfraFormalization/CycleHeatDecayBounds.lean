/-
Heat kernel on the cycle hypergraph: constant and first modes.

This module proves that the heat kernel of `cycleHypergraph n` fixes
constant vectors, that `cycleEigenvalue n 1 < 0` for `n ≥ 2`, that the
heat kernel multiplies the first cycle eigenvector by `exp(t · λ₁)`, and
that the zeroth eigenvector is the constant vector 1 with sum `n`.
-/

import InfraFormalization.HeatKernelDecay

namespace InfraFormalization

open Filter Topology Real

/-- The heat kernel of the cycle hypergraph maps every constant vector to
itself. -/
theorem heatKernel_cycleHypergraph_mulVec_const {n : ℕ} [NeZero n]
    (c : ℝ) (t : ℝ) :
    (Hypergraph.heatKernel (cycleHypergraph n) t).mulVec (fun _ => c)
      = (fun _ => c) :=
  Hypergraph.heatKernel_mulVec_const (cycleHypergraph n) c t

/-- For `n ≥ 2`, `cycleEigenvalue n 1 < 0`. -/
theorem cycleHypergraph_spectral_gap_neg {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    cycleEigenvalue n 1 < 0 :=
  cycleEigenvalue_one_neg hn

/-- For `n ≥ 2`,
`((heatKernel t).mulVec (cycleEigenvector n 1)) i = exp(t · λ₁) · cycleEigenvector n 1 i`
with `λ₁ = cycleEigenvalue n 1`. -/
theorem heatKernel_cycleHypergraph_firstMode_explicit {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (t : ℝ) (i : Fin n) :
    ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
      (cycleEigenvector n 1)) i
    = Real.exp (t * cycleEigenvalue n 1) * cycleEigenvector n 1 i := by
  rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn 1 t]
  simp [Pi.smul_apply, smul_eq_mul]

/-- For `n ≥ 2`, the heat kernel fixes `cycleEigenvector n 0`. -/
theorem heatKernel_cycleHypergraph_constMode_fixed {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (t : ℝ) :
    (Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
      (cycleEigenvector n 0) = cycleEigenvector n 0 :=
  heatKernel_cycleHypergraph_constMode_invariant hn t

/-- Every entry of `cycleEigenvector n 0` equals 1. -/
theorem cycleEigenvector_zero_is_constant {n : ℕ} [NeZero n] (j : Fin n) :
    cycleEigenvector n 0 j = 1 :=
  cycleEigenvector_zero_eq_one n j

/-- The entries of `cycleEigenvector n 0` sum to `n`. -/
theorem sum_cycleEigenvector_zero {n : ℕ} [NeZero n] :
    ∑ j : Fin n, cycleEigenvector n 0 j = (n : ℝ) := by
  simp [cycleEigenvector_zero_is_constant]

end InfraFormalization
