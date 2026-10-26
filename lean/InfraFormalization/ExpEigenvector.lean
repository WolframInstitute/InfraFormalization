/-
The matrix exponential on an eigenvector.

For `A : Matrix V V ℝ` and `v : V → ℝ` with `A.mulVec v = λ • v`, the module
proves `(A^n).mulVec v = λ^n • v` and
`(NormedSpace.exp A).mulVec v = Real.exp λ • v`. The proof writes the
exponential as a series (`exp_eq_tsum_rat`) and moves `mulVec v` inside the
sum with `ContinuousLinearMap.map_tsum`. As a consequence, the heat kernel
`exp(t · Δ)` of a hypergraph maps every constant vector to itself.
-/

import InfraFormalization.LaplacianMatrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Operator
open NormedSpace

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The map `M ↦ M.mulVec v`, as a continuous linear map on matrices. -/
noncomputable def mulVecCLM (v : V → ℝ) : Matrix V V ℝ →L[ℝ] (V → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.mulVec v
      map_add' := by
        intro M N
        ext w
        simp [Matrix.add_mulVec, Pi.add_apply]
      map_smul' := by
        intro c M
        ext w
        show (c • M).mulVec v w = c • M.mulVec v w
        rw [Matrix.smul_mulVec]
        rfl }

@[simp] lemma mulVecCLM_apply (v : V → ℝ) (M : Matrix V V ℝ) :
    mulVecCLM v M = M.mulVec v := rfl

/-- If `A.mulVec v = λ • v`, then `(A^n).mulVec v = λ^n • v` for every `n`. -/
theorem matrix_pow_mulVec_of_eigenvector (A : Matrix V V ℝ) (v : V → ℝ) (lam : ℝ)
    (hv : A.mulVec v = lam • v) : ∀ n : ℕ, (A^n).mulVec v = lam^n • v := by
  intro n
  induction n with
  | zero =>
    simp [pow_zero, Matrix.one_mulVec]
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv]
    rw [Matrix.mulVec_smul, ih]
    rw [smul_smul]
    rw [mul_comm lam (lam ^ n), ← pow_succ]

/-- If `A.mulVec v = λ • v`, then `(NormedSpace.exp A).mulVec v = Real.exp λ • v`. -/
theorem exp_mulVec_of_eigenvector (A : Matrix V V ℝ) (v : V → ℝ) (lam : ℝ)
    (hv : A.mulVec v = lam • v) :
    (NormedSpace.exp A).mulVec v = Real.exp lam • v := by
  -- Summability: the exp series for A is summable (radius = ⊤).
  have h_summable : Summable fun n : ℕ => (n.factorial⁻¹ : ℚ) • A^n := by
    have := NormedSpace.expSeries_summable' (𝕂 := ℚ) A
    simpa [NormedSpace.expSeries_apply_eq] using this
  -- Rewrite (exp A).mulVec v as a CLM application, then commute with tsum.
  show mulVecCLM v (NormedSpace.exp A) = Real.exp lam • v
  rw [NormedSpace.exp_eq_tsum_rat]
  rw [ContinuousLinearMap.map_tsum (mulVecCLM v) h_summable]
  -- Rewrite each term: mulVecCLM v ((n!⁻¹ : ℚ) • A^n) = ((n!)⁻¹ * lam^n : ℝ) • v.
  have h_term : ∀ n : ℕ,
      mulVecCLM v ((n.factorial⁻¹ : ℚ) • A^n) =
        (((n.factorial : ℝ)⁻¹) * lam^n) • v := by
    intro n
    rw [mulVecCLM_apply]
    show ((n.factorial⁻¹ : ℚ) • A^n).mulVec v = _
    rw [Matrix.smul_mulVec, matrix_pow_mulVec_of_eigenvector A v lam hv n]
    -- Now: ((n!⁻¹ : ℚ) : ℝ) • (lam^n • v) = ((n!)⁻¹ * lam^n) • v
    ext w
    show ((n.factorial⁻¹ : ℚ) : ℝ) * (lam^n * v w) =
           ((n.factorial : ℝ)⁻¹ * lam^n) * v w
    push_cast
    ring
  rw [tsum_congr h_term]
  -- Now: ∑' n, ((n!)⁻¹ * lam^n) • v = Real.exp lam • v
  -- Compute the scalar tsum: ∑' n, (n!)⁻¹ * lam^n = Real.exp lam.
  have h_scalar : (∑' n : ℕ, ((n.factorial : ℝ)⁻¹ * lam^n : ℝ)) = Real.exp lam := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_rat]
    apply tsum_congr
    intro n
    show ((n.factorial : ℝ)⁻¹ * lam ^ n) = ((n.factorial⁻¹ : ℚ) : ℝ) • lam ^ n
    rw [smul_eq_mul]
    push_cast
    rfl
  -- Summability of the scalar series via Real.summable_pow_div_factorial.
  have h_summable_scalar : Summable fun n : ℕ => ((n.factorial : ℝ)⁻¹ * lam^n) := by
    have h := Real.summable_pow_div_factorial lam
    -- h : Summable (fun n => lam^n / n.factorial)
    refine h.congr ?_
    intro n
    rw [div_eq_mul_inv, mul_comm]
  -- HasSum for the scalar series.
  have h_hasSum : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ * lam^n)) (Real.exp lam) := by
    have := h_summable_scalar.hasSum
    rwa [h_scalar] at this
  -- Lift to V → ℝ via HasSum.smul_const.
  exact (h_hasSum.smul_const v).tsum_eq

/-- For all `c, t : ℝ`, `(heatKernel H t).mulVec (fun _ => c) = (fun _ => c)`.
The proof applies `exp_mulVec_of_eigenvector` with eigenvalue 0, since the
Laplacian maps constant vectors to 0. -/
theorem heatKernel_mulVec_const (H : Hypergraph V) (c : ℝ) (t : ℝ) :
    (heatKernel H t).mulVec (fun _ => c) = (fun _ => c) := by
  unfold heatKernel
  have h_lapvec_zero : (laplacianMatrix H).mulVec (fun _ : V => c) = 0 := by
    funext v
    exact laplacianMatrix_mulVec_const H c v
  have h_eigen : (t • laplacianMatrix H).mulVec (fun _ : V => c) =
                 (0 : ℝ) • (fun _ : V => c) := by
    rw [Matrix.smul_mulVec, h_lapvec_zero, smul_zero, zero_smul]
  have := exp_mulVec_of_eigenvector (t • laplacianMatrix H) (fun _ => c) 0 h_eigen
  rw [this]
  simp

end Hypergraph
end InfraFormalization
