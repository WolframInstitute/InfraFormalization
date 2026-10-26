/-
Existence and forward uniqueness for the discrete heat equation.

`heat_exists` shows that `t ↦ (heatKernel H t).mulVec u₀` is a `HeatSolution H` with initial value `u₀`. `heat_unique_forward` shows that two solutions with the same initial value agree at every `t ≥ 0`, by applying `heat_L2_decay` to their difference. The module also proves mass conservation, L² decay and the semigroup law for the vector `(heatKernel H t).mulVec u₀`.
-/

import InfraFormalization.HeatKernelODE

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For any `u₀ : V → ℝ` there is a `HeatSolution H u` with `u 0 = u₀`. The witness is `t ↦ (heatKernel H t).mulVec u₀`. -/
theorem heat_exists (H : Hypergraph V) (u₀ : V → ℝ) :
    ∃ u : ℝ → V → ℝ, HeatSolution H u ∧ u 0 = u₀ := by
  refine ⟨fun t v => (heatKernel H t).mulVec u₀ v,
          heatKernel_isHeatSolution H u₀, ?_⟩
  funext v
  show (heatKernel H 0).mulVec u₀ v = u₀ v
  rw [heatKernel_zero]
  rw [Matrix.one_mulVec]

/-- The pointwise difference of two heat solutions is a heat solution. -/
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

/-- Two heat solutions with the same initial value agree at every `t ≥ 0`. The proof applies `heat_L2_decay` to their difference, which has zero initial value. -/
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

/-- For every `u₀` there is a heat solution `u` with `u 0 = u₀` such that every heat solution `u'` with `u' 0 = u₀` satisfies `u' t = u t` for all `t ≥ 0`. -/
theorem heat_exists_unique_forward (H : Hypergraph V) (u₀ : V → ℝ) :
    ∃ u : ℝ → V → ℝ,
      (HeatSolution H u ∧ u 0 = u₀) ∧
      (∀ u' : ℝ → V → ℝ, HeatSolution H u' → u' 0 = u₀ →
        ∀ t : ℝ, 0 ≤ t → u' t = u t) := by
  obtain ⟨u, h_heat, h_init⟩ := heat_exists H u₀
  refine ⟨u, ⟨h_heat, h_init⟩, ?_⟩
  intro u' h_u' h_u'_init t ht
  exact heat_unique_forward H h_u' h_heat (h_u'_init.trans h_init.symm) ht

/-- For any `u₀` and `t`, `∑_v (heatKernel H t).mulVec u₀ v = ∑_v u₀ v`. The proof combines `heatKernel_isHeatSolution` with `heat_mass_conservation`. -/
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

/-- For any `u₀` and `t ≥ 0`, `∑_v ((heatKernel H t).mulVec u₀ v)² ≤ ∑_v (u₀ v)²`. The proof combines `heatKernel_isHeatSolution` with `heat_L2_decay`. -/
theorem heatKernel_L2_decay (H : Hypergraph V) (u₀ : V → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ v : V, ((heatKernel H t).mulVec u₀ v) ^ 2) ≤ (∑ v : V, (u₀ v) ^ 2) := by
  have h_heat : HeatSolution H (fun s v => (heatKernel H s).mulVec u₀ v) :=
    heatKernel_isHeatSolution H u₀
  have h_decay := heat_L2_decay H h_heat ht
  have h_init : ∀ v, (fun s v => (heatKernel H s).mulVec u₀ v) 0 v = u₀ v := by
    intro v
    show (heatKernel H 0).mulVec u₀ v = u₀ v
    rw [heatKernel_zero, Matrix.one_mulVec]
  calc (∑ v : V, ((heatKernel H t).mulVec u₀ v) ^ 2)
      ≤ (∑ v : V, ((heatKernel H 0).mulVec u₀ v) ^ 2) := h_decay
    _ = (∑ v : V, (u₀ v) ^ 2) := by
        apply Finset.sum_congr rfl
        intros v _
        congr 1
        exact h_init v

/-- For any `u₀`, `s`, `t`, `(heatKernel H (s + t)).mulVec u₀ = (heatKernel H s).mulVec ((heatKernel H t).mulVec u₀)`. The proof uses `heatKernel_add` and `Matrix.mulVec_mulVec`. -/
theorem heatKernel_mulVec_add (H : Hypergraph V) (u₀ : V → ℝ) (s t : ℝ) :
    (heatKernel H (s + t)).mulVec u₀
    = (heatKernel H s).mulVec ((heatKernel H t).mulVec u₀) := by
  rw [heatKernel_add, ← Matrix.mulVec_mulVec]

end Hypergraph
end InfraFormalization
