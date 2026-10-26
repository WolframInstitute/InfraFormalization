/-
Discrete Klein–Gordon equation on a hypergraph.

With the hypergraph Laplacian `Δ_H = A − D` (negative semidefinite), the equation is
`u''(t, v) = Δ_H u(t) v − m² · u(t, v)` for `u : ℝ → V → ℝ`. This module defines solutions
`KleinGordonSolution H m u du` and the energy
`E(t) = ∑_v (du t v)² − ∑_v u(t, v) · Δ_H u(t) v + m² · ∑_v u(t, v)²`, and proves that the energy is
non-negative and constant in `t`. For `m = 0` the equation is the one in `WaveSolution`.
-/

import InfraFormalization.WaveEquation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `(u, du)` is a solution of the discrete Klein–Gordon equation with mass `m` if `du` is the time
derivative of `u` and the time derivative of `du` is `Δ_H u − m² · u`, at every vertex and time. -/
structure KleinGordonSolution (H : Hypergraph V) (m : ℝ) (u du : ℝ → V → ℝ) :
    Prop where
  position : ∀ t v, HasDerivAt (fun s => u s v) (du t v) t
  velocity : ∀ t v, HasDerivAt (fun s => du s v)
    (Hypergraph.laplacianHyper H (u t) v - m ^ 2 * u t v) t

/-- The Klein–Gordon energy
`E(t) = ∑_v (du t v)² − ∑_v u(t, v) · Δ_H u(t) v + m² · ∑_v (u t v)²`. -/
noncomputable def kleinGordonEnergy (H : Hypergraph V) (m : ℝ)
    (u du : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  (∑ v : V, (du t v) ^ 2)
  - (∑ v : V, u t v * Hypergraph.laplacianHyper H (u t) v)
  + m ^ 2 * (∑ v : V, (u t v) ^ 2)

/-- The Klein–Gordon energy is non-negative: the first and third terms are sums of squares times
non-negative factors, and `∑_v u · Δ_H u ≤ 0`. -/
theorem kleinGordonEnergy_nonneg (H : Hypergraph V) (m : ℝ)
    (u du : ℝ → V → ℝ) (t : ℝ) :
    0 ≤ kleinGordonEnergy H m u du t := by
  unfold kleinGordonEnergy
  have hkin : (0 : ℝ) ≤ ∑ v : V, (du t v) ^ 2 := by
    apply Finset.sum_nonneg
    intros v _
    exact sq_nonneg _
  have hgrad : (∑ v : V, u t v * Hypergraph.laplacianHyper H (u t) v) ≤ 0 :=
    Hypergraph.laplacianHyper_dirichlet_nonpos H (u t)
  have hmass : (0 : ℝ) ≤ m ^ 2 * ∑ v : V, (u t v) ^ 2 := by
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intros v _
    exact sq_nonneg _
  linarith

/-- For a solution, the time derivative of `∑_v (du s v)²` is
`∑_v 2 · du t v · (Δ_H u(t) v − m² · u t v)`. -/
theorem hasDerivAt_KG_kinetic (H : Hypergraph V) (m : ℝ)
    {u du : ℝ → V → ℝ} (hu : KleinGordonSolution H m u du) (t : ℝ) :
    HasDerivAt (fun s => ∑ v : V, (du s v) ^ 2)
      (∑ v : V, 2 * (du t v) *
        (Hypergraph.laplacianHyper H (u t) v - m ^ 2 * u t v)) t := by
  apply HasDerivAt.fun_sum
  intros v _
  have hv := (hu.velocity t v).pow 2
  simp only [Nat.cast_ofNat] at hv
  convert hv using 1
  ring

/-- For a solution, the time derivative of `m² · ∑_v (u s v)²` is `m² · ∑_v 2 · u t v · du t v`. -/
theorem hasDerivAt_KG_mass (H : Hypergraph V) (m : ℝ)
    {u du : ℝ → V → ℝ} (hu : KleinGordonSolution H m u du) (t : ℝ) :
    HasDerivAt (fun s => m ^ 2 * ∑ v : V, (u s v) ^ 2)
      (m ^ 2 * ∑ v : V, 2 * (u t v) * (du t v)) t := by
  have hper : ∀ v : V,
      HasDerivAt (fun s => (u s v) ^ 2) (2 * (u t v) * du t v) t := by
    intro v
    have hv := (hu.position t v).pow 2
    simp only [Nat.cast_ofNat] at hv
    convert hv using 1
    ring
  have hsum :
      HasDerivAt (fun s => ∑ v : V, (u s v) ^ 2)
        (∑ v : V, 2 * (u t v) * du t v) t :=
    HasDerivAt.fun_sum (fun v _ => hper v)
  exact hsum.const_mul (m ^ 2)

/-- For a solution, the time derivative of the Klein–Gordon energy is 0 at every `t`. -/
theorem hasDerivAt_kleinGordonEnergy (H : Hypergraph V) (m : ℝ)
    {u du : ℝ → V → ℝ} (hu : KleinGordonSolution H m u du) (t : ℝ) :
    HasDerivAt (kleinGordonEnergy H m u du) 0 t := by
  unfold kleinGordonEnergy
  have hkin := hasDerivAt_KG_kinetic H m hu t
  have hmass := hasDerivAt_KG_mass H m hu t
  -- Derivative of the gradient term `∑ u · Δu`, using self-adjointness of `Δ_H`.
  have hposition := hu.position
  have hgrad :
      HasDerivAt
        (fun s => ∑ v : V, u s v * Hypergraph.laplacianHyper H (u s) v)
        (2 * ∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v) t := by
    -- This step uses only the `position` part of the solution.
    have hper : ∀ v : V,
        HasDerivAt (fun s => u s v * Hypergraph.laplacianHyper H (u s) v)
          (du t v * Hypergraph.laplacianHyper H (u t) v
           + u t v * Hypergraph.laplacianHyper H (du t) v) t := by
      intro v
      exact (hposition t v).mul
        (hasDerivAt_laplacianHyper_coord H hposition t v)
    have hsum :
        HasDerivAt
          (fun s => ∑ v : V, u s v * Hypergraph.laplacianHyper H (u s) v)
          (∑ v : V, (du t v * Hypergraph.laplacianHyper H (u t) v
             + u t v * Hypergraph.laplacianHyper H (du t) v)) t :=
      HasDerivAt.fun_sum (fun v _ => hper v)
    have hrewrite :
        (∑ v : V, (du t v * Hypergraph.laplacianHyper H (u t) v
           + u t v * Hypergraph.laplacianHyper H (du t) v))
        = 2 * ∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v := by
      rw [Finset.sum_add_distrib]
      rw [show (∑ v : V, u t v * Hypergraph.laplacianHyper H (du t) v)
           = ∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v
           from Hypergraph.laplacianHyper_self_adjoint H (u t) (du t)]
      ring
    rw [hrewrite] at hsum
    exact hsum
  have hcombined := (hkin.sub hgrad).add hmass
  convert hcombined using 1
  -- The three derivatives sum to 0.
  have hkin_expand :
      (∑ v : V, 2 * (du t v) *
        (Hypergraph.laplacianHyper H (u t) v - m ^ 2 * u t v))
      = 2 * (∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v)
        - 2 * m ^ 2 * ∑ v : V, du t v * u t v := by
    rw [show (2 * m ^ 2 * ∑ v : V, du t v * u t v)
         = ∑ v : V, 2 * m ^ 2 * (du t v * u t v) from by
           rw [Finset.mul_sum]]
    rw [show (2 * ∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v)
         = ∑ v : V, 2 * (du t v * Hypergraph.laplacianHyper H (u t) v) from by
           rw [Finset.mul_sum]]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros v _
    ring
  have hmass_expand :
      (m ^ 2 * ∑ v : V, 2 * (u t v) * (du t v))
      = 2 * m ^ 2 * ∑ v : V, du t v * u t v := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros v _
    ring
  rw [hkin_expand, hmass_expand]
  ring

/-- For a solution, `E(t) = E(0)` for every `t`. -/
theorem klein_gordon_energy_conservation (H : Hypergraph V) (m : ℝ)
    {u du : ℝ → V → ℝ} (hu : KleinGordonSolution H m u du) (t : ℝ) :
    kleinGordonEnergy H m u du t = kleinGordonEnergy H m u du 0 := by
  have hdiff : Differentiable ℝ (kleinGordonEnergy H m u du) := fun x =>
    (hasDerivAt_kleinGordonEnergy H m hu x).differentiableAt
  have hzero : ∀ x : ℝ, deriv (kleinGordonEnergy H m u du) x = 0 := fun x =>
    (hasDerivAt_kleinGordonEnergy H m hu x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

end InfraFormalization
