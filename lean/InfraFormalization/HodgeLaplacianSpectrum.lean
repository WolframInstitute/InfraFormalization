/-
Linearity, kernel and symmetry of the Vietoris–Rips 0-Laplacian.

This module proves that `vrHodge0 ε` from `HodgeVR.lean` is additive and homogeneous, that constant functions lie in its kernel, and that it is symmetric for the ℓ² pairing `∑_v f v · g v`. The spectrum itself is not computed.
-/

import InfraFormalization.HodgeVR

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `vrHodge0 ε (f + g) v = vrHodge0 ε f v + vrHodge0 ε g v`. -/
theorem vrHodge0_add (H : Hypergraph V) (ε : ℕ) (f g : V → ℝ) (v : V) :
    H.vrHodge0 ε (fun u => f u + g u) v
      = H.vrHodge0 ε f v + H.vrHodge0 ε g v := by
  unfold vrHodge0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

/-- `vrHodge0 ε (c · f) v = c · vrHodge0 ε f v`. -/
theorem vrHodge0_smul (H : Hypergraph V) (ε : ℕ) (c : ℝ) (f : V → ℝ) (v : V) :
    H.vrHodge0 ε (fun u => c * f u) v = c * H.vrHodge0 ε f v := by
  unfold vrHodge0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

/-- For nonempty `V`, there is a nonzero `f : V → ℝ` with `vrHodge0 ε f = 0`. The witness is the constant function `1`. -/
theorem vrHodge0_has_zero_eigenvalue (H : Hypergraph V) (ε : ℕ) [Nonempty V] :
    ∃ f : V → ℝ, f ≠ 0 ∧ ∀ v, H.vrHodge0 ε f v = 0 := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv : (1 : ℝ) = 0 := congrFun h v
    exact one_ne_zero hv
  · intro v
    exact vrHodge0_const H ε 1 v

/-- For every constant `c : ℝ`, `vrHodge0 ε (fun _ => c) v = 0`. -/
theorem vrHodge0_const_in_kernel (H : Hypergraph V) (ε : ℕ) (c : ℝ) (v : V) :
    H.vrHodge0 ε (fun _ => c) v = 0 :=
  vrHodge0_const H ε c v

/-- For all `f g : V → ℝ`, `∑ v, f v * vrHodge0 ε g v = ∑ v, g v * vrHodge0 ε f v`. The proof splits each side into the cross term `∑_{(v,u) adjacent} f v · g u`, which is symmetric because adjacency is symmetric, and the diagonal term `∑_{(v,u) adjacent} f v · g v`. -/
theorem vrHodge0_symm (H : Hypergraph V) (ε : ℕ) (f g : V → ℝ) :
    ∑ v, f v * H.vrHodge0 ε g v = ∑ v, g v * H.vrHodge0 ε f v := by
  classical
  -- Rewrite each side to a ∑∑ if-form, then compare term-wise.
  have h_expand : ∀ (f g : V → ℝ),
      ∑ v, f v * H.vrHodge0 ε g v
        = ∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u
            then f v * (g u - g v) else 0) := by
    intro f g
    unfold vrHodge0
    simp only [Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]
  rw [h_expand f g, h_expand g f]
  -- Split each double sum into the cross term (f v * g u) and the
  -- diagonal term (f v * g v).
  have h_split : ∀ h₁ h₂ : V → ℝ,
      (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u then
          h₁ v * (h₂ u - h₂ v) else 0))
      = (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u then
          h₁ v * h₂ u else 0))
        - (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u then
          h₁ v * h₂ v else 0)) := by
    intro h₁ h₂
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    by_cases h : (H.vietorisRipsGraph ε).Adj v u
    · simp [h]; ring
    · simp [h]
  rw [h_split f g, h_split g f]
  have h_cross_symm :
      (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u then
          f v * g u else 0))
      = (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u then
          g v * f u else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : (H.vietorisRipsGraph ε).Adj a b
    · have h' : (H.vietorisRipsGraph ε).Adj b a := h.symm
      simp [h, h']; ring
    · have h' : ¬ (H.vietorisRipsGraph ε).Adj b a := fun hba => h hba.symm
      simp [h, h']
  have h_diag_symm :
      (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u then
          f v * g v else 0))
      = (∑ v, ∑ u, (if (H.vietorisRipsGraph ε).Adj v u then
          g v * f v else 0)) := by
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
    by_cases h : (H.vietorisRipsGraph ε).Adj v u
    · simp [h]; ring
    · simp [h]
  rw [h_cross_symm, h_diag_symm]

end Hypergraph
end InfraFormalization
