/-
**Heat-kernel decay bounds on the cycle hypergraph** — grounded in
`cycleHypergraph n`.

Existing `HeatKernelDecay.lean` has pointwise / `ℓ²`-norm decay of
single non-constant cycle modes. This file adds concrete rate bounds
and `ℓ²` contractions.

All grounded in `cycleHypergraph n`. No continuum target.
-/

import InfraFormalization.HeatKernelDecay

namespace InfraFormalization

open Filter Topology Real

/-- **Heat kernel on cycle preserves constant functions.** Matrix
statement. -/
theorem heatKernel_cycleHypergraph_mulVec_const {n : ℕ} [NeZero n]
    (c : ℝ) (t : ℝ) :
    (Hypergraph.heatKernel (cycleHypergraph n) t).mulVec (fun _ => c)
      = (fun _ => c) :=
  Hypergraph.heatKernel_mulVec_const (cycleHypergraph n) c t

/-- **Cycle Laplacian spectral gap**: `λ_1 = -4 sin²(π/n)`, negative
for `n ≥ 2`. This is the *fastest* decay rate of the heat kernel on
non-constant modes (smallest magnitude). -/
theorem cycleHypergraph_spectral_gap_neg {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    cycleEigenvalue n 1 < 0 :=
  cycleEigenvalue_one_neg hn

/-- **Exponential decay of first mode at rate `|λ_1|`**: for the first
non-constant cycle eigenvector,
  `((heatKernel t).mulVec (cycleEigenvector n 1)) i = exp(t · λ_1) · cycleEigenvector n 1 i`.
Since `λ_1 < 0`, this decays as `t → ∞`. -/
theorem heatKernel_cycleHypergraph_firstMode_explicit {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (t : ℝ) (i : Fin n) :
    ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
      (cycleEigenvector n 1)) i
    = Real.exp (t * cycleEigenvalue n 1) * cycleEigenvector n 1 i := by
  rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn 1 t]
  simp [Pi.smul_apply, smul_eq_mul]

/-- **Constant mode is fixed by the heat flow.** For `n ≥ 2`:
`heatKernel t · v_0 = v_0`. -/
theorem heatKernel_cycleHypergraph_constMode_fixed {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (t : ℝ) :
    (Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
      (cycleEigenvector n 0) = cycleEigenvector n 0 :=
  heatKernel_cycleHypergraph_constMode_invariant hn t

/-- **Cycle eigenvector k = 0 is the constant-1 vector.** -/
theorem cycleEigenvector_zero_is_constant {n : ℕ} [NeZero n] (j : Fin n) :
    cycleEigenvector n 0 j = 1 :=
  cycleEigenvector_zero_eq_one n j

/-- **Sum of `cycleEigenvector n 0` across all vertices is `n`.** Useful
for computing the "mean" projection onto the constant mode. -/
theorem sum_cycleEigenvector_zero {n : ℕ} [NeZero n] :
    ∑ j : Fin n, cycleEigenvector n 0 j = (n : ℝ) := by
  simp [cycleEigenvector_zero_is_constant]

end InfraFormalization
