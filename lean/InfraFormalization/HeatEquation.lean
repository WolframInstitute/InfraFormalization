/-
Discrete heat equation on a hypergraph `Hypergraph V`.

**Connection to hypergraphs.** Native. The unknown `u : ℝ → V → ℝ`
assigns a real value to each vertex of the same `Hypergraph V` that
carries the Wolfram-model rewriting. The evolution operator is the
`Hypergraph.laplacianHyper` from `HypergraphLaplacian.lean`.

**Sign convention.** Our `laplacianHyper` is `A − D` (the "raising"
Laplacian), i.e. `Δf(v) = ∑_w (f(w) − f(v))`. In this convention it
is negative semidefinite, and the dissipative heat equation is

  `d/dt u(t, v) = Δ_H u(t) (v)`

(with no extra minus sign). Eigenmodes with eigenvalue `λ ≤ 0` of
`Δ_H` evolve as `e^{λ t}` and therefore decay.

**What this file contributes.**

  * `HeatSolution H u` — the predicate that `u : ℝ → V → ℝ` solves
    the discrete heat equation on the hypergraph `H` pointwise in
    time and in every vertex.
  * `heatSolution_zero`, `heatSolution_add`, `heatSolution_smul` —
    linearity of the solution space.
  * `heat_mass_conservation` — `∑_v u(t, v) = ∑_v u(0, v)` for every
    `t`, via the discrete divergence theorem
    `laplacianHyper_sum_zero`.

Existence / uniqueness via `Matrix.exp` is deferred to the follow-up
file on the heat semigroup (Rung 6 task D3).
-/

import InfraFormalization.HypergraphLaplacian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Discrete heat equation** on a hypergraph. A function
`u : ℝ → V → ℝ` is a solution if, at every time `t` and every vertex
`v`, the time derivative of `t ↦ u t v` equals
`Hypergraph.laplacianHyper H (u t) v`. -/
def HeatSolution (H : Hypergraph V) (u : ℝ → V → ℝ) : Prop :=
  ∀ t : ℝ, ∀ v : V,
    HasDerivAt (fun s => u s v) (Hypergraph.laplacianHyper H (u t) v) t

/-! ## Linearity of the solution space -/

/-- The zero function is a solution. -/
theorem heatSolution_zero (H : Hypergraph V) :
    HeatSolution H (fun _ _ => 0) := by
  intro t v
  have hΔ : Hypergraph.laplacianHyper H (fun _ => (0 : ℝ)) v = 0 :=
    Hypergraph.laplacianHyper_const H 0 v
  rw [hΔ]
  exact hasDerivAt_const t 0

/-- Sum of two solutions is a solution. -/
theorem heatSolution_add (H : Hypergraph V) {u₁ u₂ : ℝ → V → ℝ}
    (h₁ : HeatSolution H u₁) (h₂ : HeatSolution H u₂) :
    HeatSolution H (fun t v => u₁ t v + u₂ t v) := by
  intro t v
  have hsum : HasDerivAt (fun s => u₁ s v + u₂ s v)
      (Hypergraph.laplacianHyper H (u₁ t) v +
       Hypergraph.laplacianHyper H (u₂ t) v) t :=
    (h₁ t v).add (h₂ t v)
  have hΔ : Hypergraph.laplacianHyper H (u₁ t) v +
            Hypergraph.laplacianHyper H (u₂ t) v
          = Hypergraph.laplacianHyper H (fun w => u₁ t w + u₂ t w) v := by
    rw [Hypergraph.laplacianHyper_add]
  rw [hΔ] at hsum
  exact hsum

/-- Scalar multiple of a solution is a solution. -/
theorem heatSolution_smul (H : Hypergraph V) (c : ℝ) {u : ℝ → V → ℝ}
    (hu : HeatSolution H u) :
    HeatSolution H (fun t v => c * u t v) := by
  intro t v
  have hmul : HasDerivAt (fun s => c * u s v)
      (c * Hypergraph.laplacianHyper H (u t) v) t :=
    (hu t v).const_mul c
  have hΔ : c * Hypergraph.laplacianHyper H (u t) v
          = Hypergraph.laplacianHyper H (fun w => c * u t w) v := by
    rw [Hypergraph.laplacianHyper_smul]
  rw [hΔ] at hmul
  exact hmul

/-! ## Mass conservation

The total mass `M(t) := ∑_v u(t, v)` is conserved. The derivative
equals `∑_v Δ_H u(t) v = 0` by the discrete divergence theorem
`laplacianHyper_sum_zero`, and a function with vanishing derivative
on all of `ℝ` is constant. -/

/-- **Derivative of total mass is zero.** If `u` solves the heat
equation on `H`, then `d/dt ∑_v u(t, v) = 0` at every `t`. -/
theorem heat_mass_derivative (H : Hypergraph V) {u : ℝ → V → ℝ}
    (hu : HeatSolution H u) (t : ℝ) :
    HasDerivAt (fun s => ∑ v : V, u s v) 0 t := by
  have h1 : HasDerivAt (fun s => ∑ v : V, u s v)
      (∑ v : V, Hypergraph.laplacianHyper H (u t) v) t :=
    HasDerivAt.fun_sum (fun v _ => hu t v)
  have h2 : (∑ v : V, Hypergraph.laplacianHyper H (u t) v) = 0 :=
    Hypergraph.laplacianHyper_sum_zero H (u t)
  rw [h2] at h1
  exact h1

/-- **Mass conservation.** For any solution `u` of the discrete
heat equation, the total mass is constant in time:
`∑_v u(t, v) = ∑_v u(0, v)` for all `t`. -/
theorem heat_mass_conservation (H : Hypergraph V) {u : ℝ → V → ℝ}
    (hu : HeatSolution H u) (t : ℝ) :
    ∑ v : V, u t v = ∑ v : V, u 0 v := by
  have hdiff : Differentiable ℝ (fun s => ∑ v : V, u s v) := fun x =>
    (heat_mass_derivative H hu x).differentiableAt
  have hzero : ∀ x : ℝ, deriv (fun s => ∑ v : V, u s v) x = 0 := fun x =>
    (heat_mass_derivative H hu x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- **Stronger mass conservation.** The total mass is the *same* at
any two times `t₁ t₂ : ℝ`. -/
theorem heat_mass_conservation' (H : Hypergraph V) {u : ℝ → V → ℝ}
    (hu : HeatSolution H u) (t₁ t₂ : ℝ) :
    ∑ v : V, u t₁ v = ∑ v : V, u t₂ v := by
  rw [heat_mass_conservation H hu t₁, heat_mass_conservation H hu t₂]

/-! ## L² decay

The L² energy `E(t) := ∑_v (u(t, v))²` is non-increasing along
solutions of the discrete heat equation. Proof:

  `d/dt E(t) = ∑_v 2 · u(t, v) · Δ_H u(t) v ≤ 0`

by `laplacianHyper_dirichlet_nonpos`. Antitonicity follows from
`antitone_of_deriv_nonpos`. -/

/-- **Derivative of the L² energy.** For a heat-equation solution `u`,
`d/dt ∑_v (u(t, v))² = 2 · ∑_v u(t, v) · Δ_H u(t) v`. -/
theorem heat_L2_derivative (H : Hypergraph V) {u : ℝ → V → ℝ}
    (hu : HeatSolution H u) (t : ℝ) :
    HasDerivAt (fun s => ∑ v : V, (u s v) ^ 2)
      (∑ v : V, 2 * (u t v) * Hypergraph.laplacianHyper H (u t) v) t := by
  have hper : ∀ v : V,
      HasDerivAt (fun s => (u s v) ^ 2)
        (2 * (u t v) * Hypergraph.laplacianHyper H (u t) v) t := by
    intro v
    have := (hu t v).pow 2
    simp only [Nat.cast_ofNat] at this
    convert this using 1
    ring
  exact HasDerivAt.fun_sum (fun v _ => hper v)

/-- **L² energy derivative is ≤ 0** along the heat equation. -/
theorem heat_L2_derivative_nonpos (H : Hypergraph V) (u : ℝ → V → ℝ) (t : ℝ) :
    (∑ v : V, 2 * (u t v) * Hypergraph.laplacianHyper H (u t) v) ≤ 0 := by
  have hrewrite :
      (∑ v : V, 2 * (u t v) * Hypergraph.laplacianHyper H (u t) v)
      = 2 * ∑ v : V, (u t v) * Hypergraph.laplacianHyper H (u t) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros v _
    ring
  rw [hrewrite]
  have hdirichlet :
      (∑ v : V, (u t v) * Hypergraph.laplacianHyper H (u t) v) ≤ 0 :=
    Hypergraph.laplacianHyper_dirichlet_nonpos H (u t)
  linarith

/-- **L² energy is antitone** along the heat equation. If `u` solves
the discrete heat equation on `H`, then `t ↦ ∑_v (u(t, v))²` is
antitone on all of `ℝ`. -/
theorem heat_L2_antitone (H : Hypergraph V) {u : ℝ → V → ℝ}
    (hu : HeatSolution H u) :
    Antitone (fun t => ∑ v : V, (u t v) ^ 2) := by
  apply antitone_of_hasDerivAt_nonpos (f' := fun t => ∑ v : V,
      2 * (u t v) * Hypergraph.laplacianHyper H (u t) v)
  · intro t
    exact heat_L2_derivative H hu t
  · intro t
    exact heat_L2_derivative_nonpos H u t

/-- **L² decay for the discrete heat equation.** For any `0 ≤ t`,
`∑_v (u(t, v))² ≤ ∑_v (u(0, v))²`. The L² norm is non-increasing
along the forward heat flow. -/
theorem heat_L2_decay (H : Hypergraph V) {u : ℝ → V → ℝ}
    (hu : HeatSolution H u) {t : ℝ} (ht : 0 ≤ t) :
    (∑ v : V, (u t v) ^ 2) ≤ (∑ v : V, (u 0 v) ^ 2) :=
  heat_L2_antitone H hu ht

end InfraFormalization
