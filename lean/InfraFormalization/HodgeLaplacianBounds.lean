/-
Negative semidefiniteness of the Vietoris–Rips 0-Laplacian.

This module proves `∑_v f v · vrHodge0 ε f v ≤ 0` for every `f : V → ℝ`. The proof writes the quadratic form as `−½ ∑_{(v,u) adjacent} (f v − f u)²` using the symmetry of adjacency in `vietorisRipsGraph ε`.
-/

import InfraFormalization.HodgeLaplacianSpectrum

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For every `f : V → ℝ`, `∑ v, f v * vrHodge0 ε f v ≤ 0`. The quadratic form equals `−½ ∑_{(v,u) adjacent} (f v − f u)²`. -/
theorem vrHodge0_quadratic_nonpos (H : Hypergraph V) (ε : ℕ) (f : V → ℝ) :
    ∑ v, f v * H.vrHodge0 ε f v ≤ 0 := by
  classical
  -- Expand ∑_v f v · vrHodge0 f v as a signed Dirichlet energy.
  have h_expand : ∑ v, f v * H.vrHodge0 ε f v
      = - (1 / 2) * ∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
          then (f v - f u)^2 else 0) := by
    -- LHS = ∑_v f(v) · ∑_{u: v~u} (f(u) - f(v))
    --     = ∑_{(v,u) ord adj} f(v)(f(u) - f(v))
    have h_lhs : ∑ v, f v * H.vrHodge0 ε f v
        = ∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then f v * (f u - f v) else 0) := by
      unfold vrHodge0
      simp only [Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]
    rw [h_lhs]
    -- With X(v,u) := f(v)(f(u) - f(v)), X(v,u) + X(u,v) = -(f(v) - f(u))².
    -- Swapping the summation order and using Adj.symm gives
    -- 2 · ∑_{(v,u) adjacent} X(v,u) = -∑_{(v,u) adjacent} (f v - f u)².
    have h_sym_sum :
        (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then f v * (f u - f v) else 0))
        + (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then f u * (f v - f u) else 0))
        = - (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then (f v - f u)^2 else 0)) := by
      rw [← Finset.sum_add_distrib]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [← Finset.sum_add_distrib]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases h : (H.vietorisRipsGraph ε).Adj v u
      · simp [h]; ring
      · simp [h]
    have h_swap :
        (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then f u * (f v - f u) else 0))
        = (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then f v * (f u - f v) else 0)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
      by_cases h : (H.vietorisRipsGraph ε).Adj u v
      · have h' : (H.vietorisRipsGraph ε).Adj v u := h.symm
        simp [h, h']
      · have h' : ¬ (H.vietorisRipsGraph ε).Adj v u := fun hba => h hba.symm
        simp [h, h']
    rw [h_swap] at h_sym_sum
    have h_doubled :
        2 * (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then f v * (f u - f v) else 0))
        = - (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then (f v - f u)^2 else 0)) := by
      have := h_sym_sum
      linarith
    linarith
  rw [h_expand]
  have h_dir_nonneg : 0 ≤ ∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
      then (f v - f u)^2 else 0) := by
    refine Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun u _ => ?_))
    by_cases h : (H.vietorisRipsGraph ε).Adj v u
    · rw [if_pos h]; exact sq_nonneg _
    · rw [if_neg h]
  linarith

end Hypergraph
end InfraFormalization
