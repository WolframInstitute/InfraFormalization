/-
**Existence + uniqueness for the discrete heat equation** (task D2).

  * **Existence** (`heat_exists`): for any initial data `u₀ : V → ℝ`,
    there is a `HeatSolution H u` with `u 0 = u₀`, namely the matrix
    heat-kernel action `t ↦ (heatKernel H t).mulVec u₀`.
  * **Uniqueness on `t ≥ 0`** (`heat_unique_forward`): two heat solutions
    with the same initial value agree at all `t ≥ 0`. Proof via
    `heat_L2_antitone` applied to the difference (a heat solution with
    zero initial data).
  * **Uniqueness (two-sided)** fails in general because the heat equation
    is irreversible: backward-time flow amplifies. But we state the
    forward result rigorously.

Combined with `heatKernel_isHeatSolution` (T1), this closes D2 in the
sense of "for every u₀ there is a unique solution going forward in time,
namely the matrix heat kernel action."
-/

import InfraFormalization.HeatKernelODE

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Existence of heat solutions.** For any initial data `u₀ : V → ℝ`,
the map `t ↦ (heatKernel H t).mulVec u₀` is a `HeatSolution H` with
initial value `u₀`. -/
theorem heat_exists (H : Hypergraph V) (u₀ : V → ℝ) :
    ∃ u : ℝ → V → ℝ, HeatSolution H u ∧ u 0 = u₀ := by
  refine ⟨fun t v => (heatKernel H t).mulVec u₀ v,
          heatKernel_isHeatSolution H u₀, ?_⟩
  funext v
  show (heatKernel H 0).mulVec u₀ v = u₀ v
  rw [heatKernel_zero]
  rw [Matrix.one_mulVec]

/-- **Heat solutions form a vector space closed under subtraction.** The
pointwise difference of two heat solutions is a heat solution. -/
theorem heatSolution_sub (H : Hypergraph V) {u₁ u₂ : ℝ → V → ℝ}
    (h₁ : HeatSolution H u₁) (h₂ : HeatSolution H u₂) :
    HeatSolution H (fun t v => u₁ t v - u₂ t v) := by
  intro t v
  have hdiff : HasDerivAt (fun s => u₁ s v - u₂ s v)
      (Hypergraph.laplacianHyper H (u₁ t) v -
       Hypergraph.laplacianHyper H (u₂ t) v) t :=
    (h₁ t v).sub (h₂ t v)
  convert hdiff using 1
  -- Goal: laplacianHyper H ((fun t v => u₁ t v - u₂ t v) t) v = Δ(u₁ t) v - Δ(u₂ t) v
  show Hypergraph.laplacianHyper H
        (fun w => u₁ t w - u₂ t w) v = _
  have h_rewrite : (fun w => u₁ t w - u₂ t w) =
                   fun w => u₁ t w + (-1) * u₂ t w := by
    funext w; ring
  rw [h_rewrite, Hypergraph.laplacianHyper_add]
  have : Hypergraph.laplacianHyper H (fun w => (-1) * u₂ t w) v =
      (-1) * Hypergraph.laplacianHyper H (u₂ t) v :=
    Hypergraph.laplacianHyper_smul H (-1) (u₂ t) v
  rw [this]
  ring

/-- **Forward-time uniqueness of heat solutions.** Two heat solutions
with the same initial value agree at all `t ≥ 0`. Via `heat_L2_antitone`
applied to the difference: a heat solution with zero initial value has
zero L² norm for all `t ≥ 0`, hence is zero. -/
theorem heat_unique_forward (H : Hypergraph V) {u₁ u₂ : ℝ → V → ℝ}
    (h₁ : HeatSolution H u₁) (h₂ : HeatSolution H u₂)
    (h_init : u₁ 0 = u₂ 0) {t : ℝ} (ht : 0 ≤ t) :
    u₁ t = u₂ t := by
  set w : ℝ → V → ℝ := fun s v => u₁ s v - u₂ s v with hw_def
  have h_w : HeatSolution H w := heatSolution_sub H h₁ h₂
  have hw0 : w 0 = (fun _ => 0) := by
    funext v
    show u₁ 0 v - u₂ 0 v = 0
    rw [h_init]; ring
  -- L²(w(0)) = 0.
  have h_L2_zero : (∑ v : V, (w 0 v) ^ 2) = 0 := by
    rw [hw0]
    simp
  -- L²(w(t)) ≤ L²(w(0)) = 0 (by heat_L2_decay).
  have h_L2_t_le : (∑ v : V, (w t v) ^ 2) ≤ 0 := by
    have := heat_L2_decay H h_w ht
    linarith
  -- L² is non-negative, so L²(w(t)) = 0.
  have h_L2_nn : (0 : ℝ) ≤ (∑ v : V, (w t v) ^ 2) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_L2_eq : (∑ v : V, (w t v) ^ 2) = 0 :=
    le_antisymm h_L2_t_le h_L2_nn
  -- Each summand is zero.
  have h_wt_zero : ∀ v : V, w t v = 0 := by
    intro v
    have h_sq_zero : (w t v) ^ 2 = 0 := by
      have h_summand_nn : ∀ v' ∈ (Finset.univ : Finset V), 0 ≤ (w t v') ^ 2 :=
        fun v' _ => sq_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg h_summand_nn).mp h_L2_eq v (Finset.mem_univ v)
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq_zero
  funext v
  have := h_wt_zero v
  show u₁ t v = u₂ t v
  linarith

/-- **Existence + forward uniqueness package.** Closes D2: for every
initial datum `u₀`, a unique forward-time heat solution exists, namely
`t ↦ (heatKernel H t).mulVec u₀`. -/
theorem heat_exists_unique_forward (H : Hypergraph V) (u₀ : V → ℝ) :
    ∃ u : ℝ → V → ℝ,
      (HeatSolution H u ∧ u 0 = u₀) ∧
      (∀ u' : ℝ → V → ℝ, HeatSolution H u' → u' 0 = u₀ →
        ∀ t : ℝ, 0 ≤ t → u' t = u t) := by
  obtain ⟨u, h_heat, h_init⟩ := heat_exists H u₀
  refine ⟨u, ⟨h_heat, h_init⟩, ?_⟩
  intro u' h_u' h_u'_init t ht
  exact heat_unique_forward H h_u' h_heat (h_u'_init.trans h_init.symm) ht

/-- **Matrix-level mass conservation for the heat kernel.** For any
initial data `u₀` and time `t`, the total mass `∑_v u₀(v)` is preserved
under heat-kernel evolution: `∑_v (heatKernel H t).mulVec u₀ v = ∑_v u₀ v`.

Composes `heatKernel_isHeatSolution` (T1) with the ODE-level
`heat_mass_conservation`. -/
theorem heatKernel_mass_conservation (H : Hypergraph V) (u₀ : V → ℝ) (t : ℝ) :
    ∑ v : V, (heatKernel H t).mulVec u₀ v = ∑ v : V, u₀ v := by
  have h_heat : HeatSolution H (fun s v => (heatKernel H s).mulVec u₀ v) :=
    heatKernel_isHeatSolution H u₀
  have h_mass := heat_mass_conservation H h_heat t
  have h_init : (fun v => (heatKernel H 0).mulVec u₀ v) = u₀ := by
    funext v
    rw [heatKernel_zero, Matrix.one_mulVec]
  rw [h_mass]
  exact congr_arg _ h_init

end Hypergraph
end InfraFormalization
