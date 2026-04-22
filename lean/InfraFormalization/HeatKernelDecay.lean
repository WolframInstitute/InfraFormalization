/-
**Heat-kernel long-time decay of non-constant cycle eigenmodes** (D6 / #47 partial).

On the cycle hypergraph `C_n` (with `n ≥ 2`), the heat kernel acts
diagonally on each eigenvector:
  `(heatKernel t).mulVec (cycleEigenvector n k)
    = Real.exp (t · cycleEigenvalue n k) • cycleEigenvector n k`
(proved in `CycleMatrixSpectrum.lean`).

The first nonzero eigenvalue `λ₁ = −4 sin²(π/n)` is strictly negative
(proved as `cycleEigenvalue_one_neg` in `CycleSpectrum.lean`), so
`Real.exp (t · λ₁) → 0` as `t → ∞`. Consequently each coordinate of
`(heatKernel t).mulVec (cycleEigenvector n 1)` tends to `0` — the
first-mode amplitude decays to uniform.

This captures the spectral-gap step of the long-time heat-convergence
argument (D6). Full D6 — convergence of arbitrary initial data to the
uniform distribution — requires decomposing arbitrary `ψ : Fin n → ℝ`
on the eigenbasis; that pairing is not yet formalized.
-/

import InfraFormalization.CycleMatrixSpectrum
import Mathlib.Analysis.SpecialFunctions.Exp

namespace InfraFormalization

open Filter Topology Real

/-- **Spectral-gap decay: first nonzero mode on the cycle decays to
zero under the heat flow.** For every coordinate `i : Fin n`,

  `(heatKernel (cycleHypergraph n) t).mulVec (cycleEigenvector n 1) i
     → 0   as t → ∞`.

This is the spectral-gap step of the long-time heat-convergence
theorem: the slowest non-trivial spatial mode decays exponentially
with rate `4 sin²(π/n)` (the absolute value of `cycleEigenvalue n 1`). -/
theorem heatKernel_cycleHypergraph_firstMode_tendsto_zero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    Tendsto
      (fun t : ℝ => ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (cycleEigenvector n 1)) i)
      atTop (𝓝 0) := by
  have h_eigen : ∀ t : ℝ,
      ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (cycleEigenvector n 1)) i
      = Real.exp (t * cycleEigenvalue n 1) * cycleEigenvector n 1 i := by
    intro t
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn 1 t]
    simp [Pi.smul_apply, smul_eq_mul]
  simp only [h_eigen]
  have h_neg : cycleEigenvalue n 1 < 0 := cycleEigenvalue_one_neg hn
  have h_inner : Tendsto (fun t : ℝ => t * cycleEigenvalue n 1) atTop atBot :=
    (tendsto_mul_const_atBot_of_neg h_neg).mpr tendsto_id
  have h_exp_tendsto : Tendsto (fun t : ℝ => Real.exp (t * cycleEigenvalue n 1))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h_inner
  simpa using h_exp_tendsto.mul_const (cycleEigenvector n 1 i)

/-- **All nonzero wave-number modes decay** (not only `k = 1`). For any
`k` with `1 ≤ k` and `k < n`, the corresponding cycle eigenmode tends
to zero under heat flow. The eigenvalue `cycleEigenvalue n k
= −4 sin²(πk/n)` is strictly negative in this range because
`0 < πk/n < π`. -/
theorem heatKernel_cycleHypergraph_nonzero_mode_tendsto_zero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k < n)
    (i : Fin n) :
    Tendsto
      (fun t : ℝ => ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (cycleEigenvector n k)) i)
      atTop (𝓝 0) := by
  have h_eigen : ∀ t : ℝ,
      ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (cycleEigenvector n k)) i
      = Real.exp (t * cycleEigenvalue n k) * cycleEigenvector n k i := by
    intro t
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn k t]
    simp [Pi.smul_apply, smul_eq_mul]
  simp only [h_eigen]
  have h_neg : cycleEigenvalue n k < 0 :=
    cycleEigenvalue_nonzero_mode_neg k hk_lo hk_hi
  have h_inner : Tendsto (fun t : ℝ => t * cycleEigenvalue n k) atTop atBot :=
    (tendsto_mul_const_atBot_of_neg h_neg).mpr tendsto_id
  have h_exp_tendsto : Tendsto (fun t : ℝ => Real.exp (t * cycleEigenvalue n k))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h_inner
  simpa using h_exp_tendsto.mul_const (cycleEigenvector n k i)

/-- **Linear combination of constant + one non-constant mode**: the heat
kernel applied to `c · v_0 + d · v_k` tends to `c · v_0` pointwise as
`t → ∞`, because the constant mode (`k = 0`) is preserved while any
non-constant mode (`1 ≤ k < n`) decays.

This is a restricted form of D6: for any initial state written as a
linear combination of the constant mode and one non-constant mode,
the long-time limit is the constant-mode component (i.e. the spatial
average). Full D6 needs eigenbasis decomposition for arbitrary
initial data. -/
theorem heatKernel_cycleHypergraph_const_plus_mode_tendsto
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k < n)
    (c d : ℝ) (i : Fin n) :
    Tendsto
      (fun t : ℝ => ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (c • cycleEigenvector n 0 + d • cycleEigenvector n k)) i)
      atTop (𝓝 (c * cycleEigenvector n 0 i)) := by
  -- Linearity of heatKernel.mulVec distributes over add + smul.
  have h_decomp : ∀ t : ℝ,
      ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (c • cycleEigenvector n 0 + d • cycleEigenvector n k)) i
      = c * cycleEigenvector n 0 i
        + d * Real.exp (t * cycleEigenvalue n k) * cycleEigenvector n k i := by
    intro t
    -- Split via linearity, then apply the two eigenvalue equations.
    rw [Matrix.mulVec_add]
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn 0 t]
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn k t]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cycleEigenvalue_zero,
      mul_zero, Real.exp_zero, mul_one, mul_assoc]
  simp only [h_decomp]
  -- Second term tends to 0: Real.exp (t · λ_k) → 0 with λ_k < 0.
  have h_neg : cycleEigenvalue n k < 0 :=
    cycleEigenvalue_nonzero_mode_neg k hk_lo hk_hi
  have h_inner : Tendsto (fun t : ℝ => t * cycleEigenvalue n k) atTop atBot :=
    (tendsto_mul_const_atBot_of_neg h_neg).mpr tendsto_id
  have h_exp_tendsto : Tendsto (fun t : ℝ => Real.exp (t * cycleEigenvalue n k))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h_inner
  have h_second : Tendsto
      (fun t : ℝ => d * Real.exp (t * cycleEigenvalue n k) * cycleEigenvector n k i)
      atTop (𝓝 0) := by
    have := (h_exp_tendsto.const_mul d).mul_const (cycleEigenvector n k i)
    simpa using this
  have := (tendsto_const_nhds (x := c * cycleEigenvector n 0 i)).add h_second
  simpa using this

end InfraFormalization
