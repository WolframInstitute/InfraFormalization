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
import InfraFormalization.SymmEigenOrthogonal
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

/-- **Heat kernel preserves the constant eigenvector** on the cycle.
Corollary of `heatKernel_cycleHypergraph_mulVec_eigenvector` at `k = 0`:
since `cycleEigenvalue n 0 = 0` and `Real.exp 0 = 1`, the heat flow
of `cycleEigenvector n 0` is just `cycleEigenvector n 0` itself. -/
theorem heatKernel_cycleHypergraph_constMode_invariant
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (t : ℝ) :
    (Hypergraph.heatKernel (cycleHypergraph n) t).mulVec (cycleEigenvector n 0)
      = cycleEigenvector n 0 := by
  rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn 0 t]
  rw [cycleEigenvalue_zero, mul_zero, Real.exp_zero, one_smul]

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

/-! ### ℓ²-norm-squared decay on the 2-mode subspace -/

/-- **ℓ²-norm-squared contraction for a non-constant heat-kernel mode.**
For every non-constant cycle eigenmode and every time `t`,

  `‖(heatKernel t).mulVec (cycleEigenvector n k)‖² = exp(2·t·λ_k) · ‖cycleEigenvector n k‖²`.

In particular, `‖·‖²` decays to zero exponentially in `t` for `1 ≤ k < n`. -/
theorem heatKernel_cycleHypergraph_mulVec_nonzero_mode_normSq
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (t : ℝ) :
    dotProduct
        ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
          (cycleEigenvector n k))
        ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
          (cycleEigenvector n k))
      = Real.exp (t * cycleEigenvalue n k) ^ 2
        * dotProduct (cycleEigenvector n k) (cycleEigenvector n k) := by
  rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn k t]
  -- ⟨a • v, a • v⟩ = a² · ⟨v, v⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Non-constant mode ℓ² contraction tends to 0.** For `1 ≤ k < n`,
the squared ℓ² norm of the heat-flowed `k`-th eigenmode tends to zero
as `t → ∞`. Stronger than the coordinate-wise decay — this is full
L²(Fin n → ℝ) decay of non-constant modes. -/
theorem heatKernel_cycleHypergraph_nonzero_mode_normSq_tendsto_zero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k < n) :
    Tendsto
      (fun t : ℝ => dotProduct
        ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
          (cycleEigenvector n k))
        ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
          (cycleEigenvector n k)))
      atTop (𝓝 0) := by
  have h_rewrite : ∀ t : ℝ,
      dotProduct
          ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
            (cycleEigenvector n k))
          ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
            (cycleEigenvector n k))
        = Real.exp (t * cycleEigenvalue n k) ^ 2
          * dotProduct (cycleEigenvector n k) (cycleEigenvector n k) :=
    fun t => heatKernel_cycleHypergraph_mulVec_nonzero_mode_normSq hn k t
  simp only [h_rewrite]
  have h_neg : cycleEigenvalue n k < 0 :=
    cycleEigenvalue_nonzero_mode_neg k hk_lo hk_hi
  have h_inner : Tendsto (fun t : ℝ => t * cycleEigenvalue n k) atTop atBot :=
    (tendsto_mul_const_atBot_of_neg h_neg).mpr tendsto_id
  have h_exp : Tendsto (fun t : ℝ => Real.exp (t * cycleEigenvalue n k)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_inner
  have h_exp_sq : Tendsto (fun t : ℝ => Real.exp (t * cycleEigenvalue n k) ^ 2)
      atTop (𝓝 0) := by
    have := h_exp.mul h_exp
    simpa [pow_two] using this
  have := h_exp_sq.mul_const
    (dotProduct (cycleEigenvector n k) (cycleEigenvector n k))
  simpa using this

/-- **2-mode Parseval identity.** For `v = c · v_0 + d · v_k` with
`v_0, v_k` orthogonal cycle eigenvectors (here `v_0` is the constant
mode, `v_k` with `1 ≤ k < n` is non-constant), the squared ℓ² norm of
the heat-flowed vector splits as

  `⟨heatKernel t · v, heatKernel t · v⟩
     = c² · ⟨v_0, v_0⟩ + d² · exp(2·t·λ_k) · ⟨v_k, v_k⟩`.

Cross terms vanish by orthogonality (`cycleEigenvector_const_orthogonal_nonzero`).
This is the concrete Parseval-style decomposition on the 2-mode subspace,
with each mode decaying at its own eigenvalue rate. -/
theorem heatKernel_cycleHypergraph_two_mode_parseval
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k < n)
    (c d : ℝ) (t : ℝ) :
    dotProduct
        ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
          (c • cycleEigenvector n 0 + d • cycleEigenvector n k))
        ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
          (c • cycleEigenvector n 0 + d • cycleEigenvector n k))
      = c ^ 2 * dotProduct (cycleEigenvector n 0) (cycleEigenvector n 0)
        + d ^ 2 * Real.exp (t * cycleEigenvalue n k) ^ 2
          * dotProduct (cycleEigenvector n k) (cycleEigenvector n k) := by
  -- Distribute heatKernel.mulVec over add + smul, use eigenvalue actions.
  have h_heat_v :
      (Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (c • cycleEigenvector n 0 + d • cycleEigenvector n k)
      = c • cycleEigenvector n 0
          + (d * Real.exp (t * cycleEigenvalue n k)) • cycleEigenvector n k := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn 0 t]
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn k t]
    rw [cycleEigenvalue_zero, mul_zero, Real.exp_zero, one_smul]
    rw [smul_smul]
  rw [h_heat_v]
  -- ⟨c·v_0 + e·v_k, c·v_0 + e·v_k⟩ = c²⟨v_0,v_0⟩ + e²⟨v_k,v_k⟩ + 2ce·⟨v_0, v_k⟩.
  -- Orthogonality kills the cross term.
  rw [show (c • cycleEigenvector n 0
          + (d * Real.exp (t * cycleEigenvalue n k)) • cycleEigenvector n k) ⬝ᵥ
          (c • cycleEigenvector n 0
          + (d * Real.exp (t * cycleEigenvalue n k)) • cycleEigenvector n k)
        = c * c * dotProduct (cycleEigenvector n 0) (cycleEigenvector n 0)
          + c * (d * Real.exp (t * cycleEigenvalue n k))
            * dotProduct (cycleEigenvector n 0) (cycleEigenvector n k)
          + (d * Real.exp (t * cycleEigenvalue n k)) * c
            * dotProduct (cycleEigenvector n k) (cycleEigenvector n 0)
          + (d * Real.exp (t * cycleEigenvalue n k))
            * (d * Real.exp (t * cycleEigenvalue n k))
            * dotProduct (cycleEigenvector n k) (cycleEigenvector n k) from by
    simp [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, mul_assoc]
    ring]
  rw [cycleEigenvector_const_orthogonal_nonzero hn k hk_lo hk_hi]
  have h_sym : dotProduct (cycleEigenvector n k) (cycleEigenvector n 0) = 0 := by
    rw [show (cycleEigenvector n k ⬝ᵥ cycleEigenvector n 0)
          = (cycleEigenvector n 0 ⬝ᵥ cycleEigenvector n k) from dotProduct_comm _ _]
    exact cycleEigenvector_const_orthogonal_nonzero hn k hk_lo hk_hi
  rw [h_sym]
  ring

/-! ### Multi-mode convergence to constant component (D6 core step) -/

/-- **Multi-mode heat-flow convergence.** For any finite set `S` of
non-constant mode indices (each `k ∈ S` with `1 ≤ k < n`) and any
coefficient assignment `d : Fin n → ℝ`, the heat kernel applied to

  `c • v_0 + ∑_{k ∈ S} d k • v_k`

converges pointwise to `c • v_0` as `t → ∞`, because each non-constant
mode decays independently. This is the core spectral-theorem
ingredient of D6: once an eigenbasis decomposition is established, the
long-time limit of the heat flow is the projection onto the constant
(average) component. -/
theorem heatKernel_cycleHypergraph_multi_mode_tendsto
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k ∧ k < n)
    (c : ℝ) (d : ℕ → ℝ) (i : Fin n) :
    Tendsto
      (fun t : ℝ => ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (c • cycleEigenvector n 0
          + ∑ k ∈ S, d k • cycleEigenvector n k)) i)
      atTop (𝓝 (c * cycleEigenvector n 0 i)) := by
  -- Step 1: rewrite heatKernel applied to the sum using linearity + eigenvalue action.
  have h_rewrite : ∀ t : ℝ,
      ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (c • cycleEigenvector n 0
          + ∑ k ∈ S, d k • cycleEigenvector n k)) i
      = c * cycleEigenvector n 0 i
        + ∑ k ∈ S, d k * Real.exp (t * cycleEigenvalue n k)
          * cycleEigenvector n k i := by
    intro t
    rw [Matrix.mulVec_add]
    rw [Matrix.mulVec_smul]
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn 0 t]
    rw [cycleEigenvalue_zero, mul_zero, Real.exp_zero, one_smul]
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [heatKernel_cycleHypergraph_mulVec_eigenvector hn k t]
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp only [h_rewrite]
  -- Step 2: show each summand tends to 0, then the finite sum also does.
  have h_each_tendsto : ∀ k ∈ S,
      Tendsto
        (fun t : ℝ => d k * Real.exp (t * cycleEigenvalue n k)
          * cycleEigenvector n k i)
        atTop (𝓝 0) := by
    intro k hk
    obtain ⟨hk_lo, hk_hi⟩ := hS k hk
    have h_neg : cycleEigenvalue n k < 0 :=
      cycleEigenvalue_nonzero_mode_neg k hk_lo hk_hi
    have h_inner : Tendsto (fun t : ℝ => t * cycleEigenvalue n k) atTop atBot :=
      (tendsto_mul_const_atBot_of_neg h_neg).mpr tendsto_id
    have h_exp : Tendsto (fun t : ℝ => Real.exp (t * cycleEigenvalue n k))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h_inner
    have h1 := (h_exp.const_mul (d k)).mul_const (cycleEigenvector n k i)
    simpa using h1
  have h_sum_tendsto :
      Tendsto
        (fun t : ℝ => ∑ k ∈ S, d k * Real.exp (t * cycleEigenvalue n k)
          * cycleEigenvector n k i)
        atTop (𝓝 0) := by
    have h := tendsto_finset_sum S
      (f := fun k t =>
        d k * Real.exp (t * cycleEigenvalue n k) * cycleEigenvector n k i)
      (fun k hk => h_each_tendsto k hk)
    simpa using h
  have := (tendsto_const_nhds (x := c * cycleEigenvector n 0 i)).add h_sum_tendsto
  simpa using this

end InfraFormalization
