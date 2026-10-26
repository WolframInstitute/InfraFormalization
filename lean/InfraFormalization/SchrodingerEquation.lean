/-
Discrete Schrödinger equation on a hypergraph.

A wavefunction `ψ = u + i v` on the vertices of `H : Hypergraph V` is
represented by two real functions `u v : ℝ → V → ℝ`. With the sign
convention `Δ_H = A − D` of `Hypergraph.laplacianHyper`, the equation
`i ∂_t ψ = −Δ_H ψ` becomes `u' = −Δ_H v`, `v' = Δ_H u`. This module defines
solutions of this system and the total probability `∑_x u² + v²`, and
proves, using the self-adjointness of `Δ_H`, that the total probability of
a solution is constant in time.
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.WaveEquation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `u` and `v` satisfy `∂_t u(t, x) = −Δ_H v(t) x` and
`∂_t v(t, x) = Δ_H u(t) x` for all `t` and `x`. -/
structure SchrodingerSolution (H : Hypergraph V) (u v : ℝ → V → ℝ) :
    Prop where
  real_eq : ∀ t x, HasDerivAt (fun s => u s x)
    (- Hypergraph.laplacianHyper H (v t) x) t
  imag_eq : ∀ t x, HasDerivAt (fun s => v s x)
    (Hypergraph.laplacianHyper H (u t) x) t

/-- The total probability `∑_x (u(t,x))² + (v(t,x))²`. -/
noncomputable def schrodingerProbability (u v : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  ∑ x : V, ((u t x) ^ 2 + (v t x) ^ 2)

/-- For a solution, the total probability has derivative 0 at every `t`;
the terms `−2 u · Δ v` and `2 v · Δ u` cancel in the sum by
self-adjointness of `Δ_H`. -/
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

/-- For a solution, the total probability at time `t` equals its value at
time 0. -/
theorem schrodinger_unitary_evolution (H : Hypergraph V)
    {u v : ℝ → V → ℝ}
    (hψ : SchrodingerSolution H u v) (t : ℝ) :
    schrodingerProbability u v t = schrodingerProbability u v 0 := by
  have hdiff : Differentiable ℝ (schrodingerProbability u v) := fun x =>
    (hasDerivAt_schrodingerProbability H hψ x).differentiableAt
  have hzero : ∀ x : ℝ, deriv (schrodingerProbability u v) x = 0 := fun x =>
    (hasDerivAt_schrodingerProbability H hψ x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- For a solution, the total probability takes the same value at any two
times `t₁`, `t₂`. -/
theorem schrodinger_unitary_evolution' (H : Hypergraph V)
    {u v : ℝ → V → ℝ}
    (hψ : SchrodingerSolution H u v) (t₁ t₂ : ℝ) :
    schrodingerProbability u v t₁ = schrodingerProbability u v t₂ := by
  rw [schrodinger_unitary_evolution H hψ t₁,
      schrodinger_unitary_evolution H hψ t₂]

/-- The total probability is nonnegative. -/
theorem schrodingerProbability_nonneg (u v : ℝ → V → ℝ) (t : ℝ) :
    0 ≤ schrodingerProbability u v t := by
  unfold schrodingerProbability
  apply Finset.sum_nonneg
  intros x _
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

end InfraFormalization
