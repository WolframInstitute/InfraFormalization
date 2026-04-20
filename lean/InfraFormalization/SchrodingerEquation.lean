/-
Discrete Schrödinger equation on a hypergraph `Hypergraph V`.

**Connection to hypergraphs.** Native. The wavefunction `ψ : ℝ → V → ℂ`
lives on the same `Hypergraph V` that carries the Wolfram-model
rewriting. The spatial operator is `Hypergraph.laplacianHyper`.

**Representation.** We represent `ψ = u + i v` as an ordered pair of
real-valued functions `u v : ℝ → V → ℝ`. The Schrödinger equation

  `i ∂_t ψ = −Δ_H ψ`    ⇔    `∂_t ψ = i · Δ_H ψ`

(using our `Δ_H = A − D` sign convention, which makes `Δ_H` negative
semidefinite and hence `−Δ_H` a non-negative self-adjoint Hamiltonian)
decomposes into

  `u' = −Δ_H v`,    `v' = +Δ_H u`.

**What this file contributes.**

  * `SchrodingerSolution H u v` — the structure that captures both
    equations of motion.
  * `schrodingerProbability H u v t := ∑_x (u t x)² + (v t x)²` — the
    total probability, which is `‖ψ‖²` in the ℓ²(V) norm.
  * `schrodinger_unitary_evolution` — the total probability is
    conserved for all `t`. This is the finite-dimensional incarnation
    of unitarity of `e^{itH/ℏ}` with `H = −Δ_H`.

The proof uses self-adjointness of `Δ_H` from `HypergraphLaplacian.lean`:
`∑_x u(t,x) · Δ_H v(t) x = ∑_x v(t,x) · Δ_H u(t) x`.
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.WaveEquation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Discrete Schrödinger equation** on a hypergraph, written in
real-imaginary components. For `ψ = u + i v` satisfying
`i ∂_t ψ = −Δ_H ψ`:

  * `real_eq`: `u'(t, x) = −Δ_H v(t) x`
  * `imag_eq`: `v'(t, x) = +Δ_H u(t) x`
-/
structure SchrodingerSolution (H : Hypergraph V) (u v : ℝ → V → ℝ) :
    Prop where
  real_eq : ∀ t x, HasDerivAt (fun s => u s x)
    (- Hypergraph.laplacianHyper H (v t) x) t
  imag_eq : ∀ t x, HasDerivAt (fun s => v s x)
    (Hypergraph.laplacianHyper H (u t) x) t

/-- **Total probability** `‖ψ(t)‖² = ∑_x (u(t,x))² + (v(t,x))²`. -/
noncomputable def schrodingerProbability (u v : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  ∑ x : V, ((u t x) ^ 2 + (v t x) ^ 2)

/-- **Derivative of total probability is zero.** The time derivative
of `∑_x u² + v²` along a Schrödinger solution is identically zero,
as self-adjointness of `Δ_H` makes the cross terms
`−2 u · Δ v + 2 v · Δ u` cancel when summed. -/
theorem hasDerivAt_schrodingerProbability (H : Hypergraph V)
    {u v : ℝ → V → ℝ}
    (hψ : SchrodingerSolution H u v) (t : ℝ) :
    HasDerivAt (schrodingerProbability u v) 0 t := by
  unfold schrodingerProbability
  -- Pointwise derivative: 2u·u' + 2v·v' = -2u·Δv + 2v·Δu
  have hper : ∀ x : V,
      HasDerivAt (fun s => (u s x) ^ 2 + (v s x) ^ 2)
        (- 2 * (u t x) * Hypergraph.laplacianHyper H (v t) x
         + 2 * (v t x) * Hypergraph.laplacianHyper H (u t) x) t := by
    intro x
    have hu := (hψ.real_eq t x).pow 2
    have hv := (hψ.imag_eq t x).pow 2
    simp only [Nat.cast_ofNat] at hu hv
    have hsum := hu.add hv
    convert hsum using 1
    ring
  have hsum_deriv :
      HasDerivAt (fun s => ∑ x : V, ((u s x) ^ 2 + (v s x) ^ 2))
        (∑ x : V,
          (- 2 * (u t x) * Hypergraph.laplacianHyper H (v t) x
           + 2 * (v t x) * Hypergraph.laplacianHyper H (u t) x)) t :=
    HasDerivAt.fun_sum (fun x _ => hper x)
  have hcancel :
      (∑ x : V,
        (- 2 * (u t x) * Hypergraph.laplacianHyper H (v t) x
         + 2 * (v t x) * Hypergraph.laplacianHyper H (u t) x)) = 0 := by
    rw [Finset.sum_add_distrib]
    have hadj :
        (∑ x : V, u t x * Hypergraph.laplacianHyper H (v t) x)
        = ∑ x : V, v t x * Hypergraph.laplacianHyper H (u t) x :=
      Hypergraph.laplacianHyper_self_adjoint H (u t) (v t)
    have hreindex1 :
        (∑ x : V, - 2 * (u t x) * Hypergraph.laplacianHyper H (v t) x)
        = - 2 * ∑ x : V, (u t x) * Hypergraph.laplacianHyper H (v t) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros x _
      ring
    have hreindex2 :
        (∑ x : V, 2 * (v t x) * Hypergraph.laplacianHyper H (u t) x)
        = 2 * ∑ x : V, (v t x) * Hypergraph.laplacianHyper H (u t) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros x _
      ring
    rw [hreindex1, hreindex2, hadj]
    ring
  rw [hcancel] at hsum_deriv
  exact hsum_deriv

/-- **Unitarity of Schrödinger evolution.** The total probability
`‖ψ(t)‖² = ∑_x u² + v²` is constant in time. This is the finite-
dimensional incarnation of the fact that `ψ(t) = e^{-iHt/ℏ} ψ(0)` with
`H = −Δ_H` is unitary. -/
theorem schrodinger_unitary_evolution (H : Hypergraph V)
    {u v : ℝ → V → ℝ}
    (hψ : SchrodingerSolution H u v) (t : ℝ) :
    schrodingerProbability u v t = schrodingerProbability u v 0 := by
  have hdiff : Differentiable ℝ (schrodingerProbability u v) := fun x =>
    (hasDerivAt_schrodingerProbability H hψ x).differentiableAt
  have hzero : ∀ x : ℝ, deriv (schrodingerProbability u v) x = 0 := fun x =>
    (hasDerivAt_schrodingerProbability H hψ x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- **Stronger unitarity:** `‖ψ(t₁)‖² = ‖ψ(t₂)‖²` for any two times. -/
theorem schrodinger_unitary_evolution' (H : Hypergraph V)
    {u v : ℝ → V → ℝ}
    (hψ : SchrodingerSolution H u v) (t₁ t₂ : ℝ) :
    schrodingerProbability u v t₁ = schrodingerProbability u v t₂ := by
  rw [schrodinger_unitary_evolution H hψ t₁,
      schrodinger_unitary_evolution H hψ t₂]

/-- **Probability is non-negative.** Immediate from the sum of
squares structure. -/
theorem schrodingerProbability_nonneg (u v : ℝ → V → ℝ) (t : ℝ) :
    0 ≤ schrodingerProbability u v t := by
  unfold schrodingerProbability
  apply Finset.sum_nonneg
  intros x _
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

end InfraFormalization
