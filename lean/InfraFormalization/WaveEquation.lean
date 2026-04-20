/-
Discrete wave equation on a hypergraph `Hypergraph V`.

**Connection to hypergraphs.** Native. The unknown `u : ℝ → V → ℝ`
and its time derivative `du : ℝ → V → ℝ` both live on the same
`Hypergraph V` that carries the Wolfram-model rewriting. The spatial
operator is `Hypergraph.laplacianHyper` from `HypergraphLaplacian.lean`.

**Sign convention.** With `Δ_H = A − D` negative semidefinite, the
oscillatory (conservative) wave equation is

  `u''(t, v) = Δ_H u(t) v`

(eigenmodes `Δ_H u = λu` with `λ ≤ 0` give oscillatory solutions
`cos(√(−λ) t)` and `sin(√(−λ) t)`). No extra minus sign.

**What this file contributes.**

  * `WaveSolution H u du` — the structure of a pair `(u, du)` with
    `du = u'` and `du' = Δ_H u`.
  * `hasDerivAt_laplacianHyper_coord` — time-derivative of
    `s ↦ Δ_H (u s) v` equals `Δ_H (du t) v` (linearity of `Δ_H`).
  * `waveEnergy H u du t := ∑_v (du t v)² − ∑_v u(t,v) · Δ_H u(t) v`
    — the conserved energy. Non-negative: kinetic part ≥ 0 trivially,
    potential part ≥ 0 by `laplacianHyper_dirichlet_nonpos`.
  * `wave_energy_conservation` — `E(t) = E(0)` for all `t`, via
    self-adjointness of `Δ_H` (`laplacianHyper_self_adjoint`) and
    `is_const_of_deriv_eq_zero`.
-/

import InfraFormalization.HypergraphLaplacian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Time-derivative of `Δ_H u(s) v`.** If `s ↦ u s v` has
derivative `du t v` at each time `t`, then
`s ↦ Hypergraph.laplacianHyper H (u s) v` has derivative
`Hypergraph.laplacianHyper H (du t) v` at `t`. Follows from
`Δ_H`'s linearity and edge-by-edge multiset induction. -/
theorem hasDerivAt_laplacianHyper_coord (H : Hypergraph V)
    {u du : ℝ → V → ℝ}
    (hu : ∀ t v, HasDerivAt (fun s => u s v) (du t v) t) (t : ℝ) (v : V) :
    HasDerivAt (fun s => Hypergraph.laplacianHyper H (u s) v)
               (Hypergraph.laplacianHyper H (du t) v) t := by
  unfold Hypergraph.laplacianHyper
  induction H.edges using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero]
    exact hasDerivAt_const t 0
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have he_deriv :
        HasDerivAt (fun s => ∑ w ∈ e.others v, (u s w - u s v))
                   (∑ w ∈ e.others v, (du t w - du t v)) t := by
      apply HasDerivAt.fun_sum
      intros w _
      exact (hu t w).sub (hu t v)
    exact he_deriv.add ih

/-- **Discrete wave equation** on a hypergraph. A pair `(u, du)`
forms a solution if `du = u'` (position ↔ velocity) and
`du' = Δ_H u` (acceleration ↔ spatial Laplacian). -/
structure WaveSolution (H : Hypergraph V) (u du : ℝ → V → ℝ) : Prop where
  position : ∀ t v, HasDerivAt (fun s => u s v) (du t v) t
  velocity : ∀ t v, HasDerivAt (fun s => du s v)
    (Hypergraph.laplacianHyper H (u t) v) t

/-- Conserved **wave energy**: kinetic plus potential.

  `E(t) := ∑_v (du t v)² − ∑_v u(t,v) · Δ_H u(t) v`.

Both terms are non-negative: the kinetic term is a sum of squares;
the potential term equals `−(Dirichlet form)` which is `≥ 0` by
`laplacianHyper_dirichlet_nonpos`. The factor `1/2` is dropped from
the standard continuum convention to simplify identities. -/
noncomputable def waveEnergy (H : Hypergraph V) (u du : ℝ → V → ℝ)
    (t : ℝ) : ℝ :=
  (∑ v : V, (du t v) ^ 2)
  - (∑ v : V, u t v * Hypergraph.laplacianHyper H (u t) v)

/-- **Wave energy is non-negative.** Kinetic part is a sum of
squares; potential part equals `−(Dirichlet form) ≥ 0`. -/
theorem waveEnergy_nonneg (H : Hypergraph V) (u du : ℝ → V → ℝ)
    (t : ℝ) :
    0 ≤ waveEnergy H u du t := by
  unfold waveEnergy
  have hkin : (0 : ℝ) ≤ ∑ v : V, (du t v) ^ 2 := by
    apply Finset.sum_nonneg
    intros v _
    exact sq_nonneg _
  have hpot : (∑ v : V, u t v * Hypergraph.laplacianHyper H (u t) v) ≤ 0 :=
    Hypergraph.laplacianHyper_dirichlet_nonpos H (u t)
  linarith

/-- **Derivative of the kinetic term.** -/
theorem hasDerivAt_wave_kinetic (H : Hypergraph V) {u du : ℝ → V → ℝ}
    (hu : WaveSolution H u du) (t : ℝ) :
    HasDerivAt (fun s => ∑ v : V, (du s v) ^ 2)
      (∑ v : V, 2 * (du t v) * Hypergraph.laplacianHyper H (u t) v) t := by
  apply HasDerivAt.fun_sum
  intros v _
  have hv := (hu.velocity t v).pow 2
  simp only [Nat.cast_ofNat] at hv
  convert hv using 1
  ring

/-- **Derivative of the potential term.** Uses self-adjointness of
`Δ_H` to collapse the product-rule output into `2 · ∑ du · Δu`. -/
theorem hasDerivAt_wave_potential (H : Hypergraph V) {u du : ℝ → V → ℝ}
    (hu : WaveSolution H u du) (t : ℝ) :
    HasDerivAt
      (fun s => ∑ v : V, u s v * Hypergraph.laplacianHyper H (u s) v)
      (2 * ∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v) t := by
  have hper : ∀ v : V,
      HasDerivAt (fun s => u s v * Hypergraph.laplacianHyper H (u s) v)
        (du t v * Hypergraph.laplacianHyper H (u t) v
         + u t v * Hypergraph.laplacianHyper H (du t) v) t := by
    intro v
    exact (hu.position t v).mul
      (hasDerivAt_laplacianHyper_coord H hu.position t v)
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

/-- **Wave energy conservation (infinitesimal).** The derivative of
the energy `E` along any wave solution is identically zero. -/
theorem hasDerivAt_waveEnergy (H : Hypergraph V) {u du : ℝ → V → ℝ}
    (hu : WaveSolution H u du) (t : ℝ) :
    HasDerivAt (waveEnergy H u du) 0 t := by
  unfold waveEnergy
  have hkin := hasDerivAt_wave_kinetic H hu t
  have hpot := hasDerivAt_wave_potential H hu t
  have hkin' :
      HasDerivAt (fun s => ∑ v : V, (du s v) ^ 2)
        (2 * ∑ v : V, du t v * Hypergraph.laplacianHyper H (u t) v) t := by
    convert hkin using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros v _
    ring
  have := hkin'.sub hpot
  convert this using 1
  ring

/-- **Wave energy conservation.** `E(t) = E(0)` for every `t`. -/
theorem wave_energy_conservation (H : Hypergraph V) {u du : ℝ → V → ℝ}
    (hu : WaveSolution H u du) (t : ℝ) :
    waveEnergy H u du t = waveEnergy H u du 0 := by
  have hdiff : Differentiable ℝ (waveEnergy H u du) := fun x =>
    (hasDerivAt_waveEnergy H hu x).differentiableAt
  have hzero : ∀ x : ℝ, deriv (waveEnergy H u du) x = 0 := fun x =>
    (hasDerivAt_waveEnergy H hu x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- **Stronger energy conservation.** Energy at any two times is equal. -/
theorem wave_energy_conservation' (H : Hypergraph V) {u du : ℝ → V → ℝ}
    (hu : WaveSolution H u du) (t₁ t₂ : ℝ) :
    waveEnergy H u du t₁ = waveEnergy H u du t₂ := by
  rw [wave_energy_conservation H hu t₁, wave_energy_conservation H hu t₂]

end InfraFormalization
