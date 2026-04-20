/-
Discrete Klein-Gordon equation on a hypergraph `Hypergraph V`.

**Connection to hypergraphs.** Native. The unknown `u : ℝ → V → ℝ`
and its time derivative `du` both live on `Hypergraph V`. The spatial
operator is `Hypergraph.laplacianHyper`; the additional mass term is
a pointwise scalar multiplication.

**Sign convention.** In our convention `Δ_H = A − D` negative
semidefinite, the massive wave equation (Klein-Gordon) is

  `u''(t, v) = Δ_H u(t) v  −  m² · u(t, v)`.

The spectrum of the evolution operator `Δ_H − m²` is `{λ − m² : λ ≤ 0}`,
which is always `≤ −m² ≤ 0` — hence genuinely oscillatory with
frequencies `√(m² − λ) ≥ m` (the mass gap).

**What this file contributes.**

  * `KleinGordonSolution H m u du` — structure capturing `du = u'`
    and `du' = Δ_H u − m² · u`.
  * `kleinGordonEnergy H m u du t` — the conserved energy
    `∑_v (du v)² − ∑_v u · Δ_H u + m² · ∑_v u²`.
  * `klein_gordon_energy_conservation` — `E(t) = E(0)` for all `t`.
  * `kleinGordonEnergy_nonneg` — the energy is non-negative.

The mass-zero case specialises to `WaveSolution` with the same
energy-conservation structure (but with an additional `+ m² ∑ u²`
term in the energy).
-/

import InfraFormalization.WaveEquation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Discrete Klein-Gordon equation** on a hypergraph. A pair
`(u, du)` forms a solution if `du = u'` (position ↔ velocity) and
`du' = Δ_H u − m² · u` (massive spatial operator).

Here `m : ℝ` is the mass parameter; `m = 0` recovers
`WaveSolution`. -/
structure KleinGordonSolution (H : Hypergraph V) (m : ℝ) (u du : ℝ → V → ℝ) :
    Prop where
  position : ∀ t v, HasDerivAt (fun s => u s v) (du t v) t
  velocity : ∀ t v, HasDerivAt (fun s => du s v)
    (Hypergraph.laplacianHyper H (u t) v - m ^ 2 * u t v) t

/-- Conserved **Klein-Gordon energy**: kinetic + gradient + mass.

  `E(t) := ∑_v (du t v)²  −  ∑_v u(t,v) · Δ_H u(t) v  +  m² · ∑_v (u t v)²`.

All three terms are `≥ 0`: kinetic is a sum of squares; gradient
part equals `−(Dirichlet form) ≥ 0`; mass term `≥ 0` since `m² ≥ 0`
and `u² ≥ 0`. -/
noncomputable def kleinGordonEnergy (H : Hypergraph V) (m : ℝ)
    (u du : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  (∑ v : V, (du t v) ^ 2)
  - (∑ v : V, u t v * Hypergraph.laplacianHyper H (u t) v)
  + m ^ 2 * (∑ v : V, (u t v) ^ 2)

/-- **Energy non-negativity.** All three contributions are ≥ 0. -/
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

/-- **Derivative of the kinetic term** using Klein-Gordon equation. -/
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

/-- **Derivative of the mass term.** -/
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

/-- **Klein-Gordon energy conservation (infinitesimal).** -/
theorem hasDerivAt_kleinGordonEnergy (H : Hypergraph V) (m : ℝ)
    {u du : ℝ → V → ℝ} (hu : KleinGordonSolution H m u du) (t : ℝ) :
    HasDerivAt (kleinGordonEnergy H m u du) 0 t := by
  unfold kleinGordonEnergy
  -- Extract the wave-solution part (position + velocity-without-mass).
  -- But velocity here includes `− m² · u`; reuse wave machinery by
  -- direct calculation.
  have hkin := hasDerivAt_KG_kinetic H m hu t
  have hmass := hasDerivAt_KG_mass H m hu t
  -- Derivative of the gradient term `∑ u · Δu`. The u' here is
  -- `du`, same as in WaveEquation; reuse hasDerivAt_wave_potential.
  have hposition := hu.position
  have hgrad :
      HasDerivAt
        (fun s => ∑ v : V, u s v * Hypergraph.laplacianHyper H (u s) v)
        (2 * ∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v) t := by
    -- Direct reuse of `hasDerivAt_wave_potential` requires only the
    -- `position` part of the solution, not the velocity equation.
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
  -- Algebraic cancellation: derivatives sum to 0.
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

/-- **Klein-Gordon energy conservation.** `E(t) = E(0)` for all `t`. -/
theorem klein_gordon_energy_conservation (H : Hypergraph V) (m : ℝ)
    {u du : ℝ → V → ℝ} (hu : KleinGordonSolution H m u du) (t : ℝ) :
    kleinGordonEnergy H m u du t = kleinGordonEnergy H m u du 0 := by
  have hdiff : Differentiable ℝ (kleinGordonEnergy H m u du) := fun x =>
    (hasDerivAt_kleinGordonEnergy H m hu x).differentiableAt
  have hzero : ∀ x : ℝ, deriv (kleinGordonEnergy H m u du) x = 0 := fun x =>
    (hasDerivAt_kleinGordonEnergy H m hu x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

end InfraFormalization
