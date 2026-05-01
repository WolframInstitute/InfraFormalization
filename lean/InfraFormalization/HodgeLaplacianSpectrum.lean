/-
**Spectrum of the Hodge 0-Laplacian on a VR complex** (task IT3 / #135 partial).

PHAJEK's IT3 asks for the spectrum of the Hodge Laplacian on the
Vietoris–Rips complex of a hypergraph, as a hypergraph invariant.

This file proves the baseline structural facts about `vrHodge0` (from
`HodgeVR.lean`) that make its spectrum well-defined:

  * additivity + ℝ-scalar-homogeneity (it's a linear operator),
  * `0` is an eigenvalue, witnessed by constant functions (the 0-form
    harmonic / kernel).

Full IT3 — the spectrum as a hypergraph invariant + relationship to
persistent Betti numbers — is future work and requires the persistence
infrastructure beyond the current `PersistenceBarcode` stub.
-/

import InfraFormalization.HodgeVR

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Hodge 0-Laplacian is additive**. -/
theorem vrHodge0_add (H : Hypergraph V) (ε : ℕ) (f g : V → ℝ) (v : V) :
    H.vrHodge0 ε (fun u => f u + g u) v
      = H.vrHodge0 ε f v + H.vrHodge0 ε g v := by
  unfold vrHodge0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

/-- **Hodge 0-Laplacian is ℝ-linear in the scalar**. -/
theorem vrHodge0_smul (H : Hypergraph V) (ε : ℕ) (c : ℝ) (f : V → ℝ) (v : V) :
    H.vrHodge0 ε (fun u => c * f u) v = c * H.vrHodge0 ε f v := by
  unfold vrHodge0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

/-- **Zero is an eigenvalue of the Hodge 0-Laplacian** (structural fact
inside the IT3 spectrum). The constant function `fun _ => 1` is in the
kernel — equivalently, the 0-th Hodge-cohomology of the VR complex
contains the constants.

We demand `[Nonempty V]` so that the "constant-1" function is nonzero. -/
theorem vrHodge0_has_zero_eigenvalue (H : Hypergraph V) (ε : ℕ) [Nonempty V] :
    ∃ f : V → ℝ, f ≠ 0 ∧ ∀ v, H.vrHodge0 ε f v = 0 := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv : (1 : ℝ) = 0 := congrFun h v
    exact one_ne_zero hv
  · intro v
    exact vrHodge0_const H ε 1 v

/-- **Multiple eigenvalues come from multiple constants.** Any constant
`c : ℝ` gives a kernel element. -/
theorem vrHodge0_const_in_kernel (H : Hypergraph V) (ε : ℕ) (c : ℝ) (v : V) :
    H.vrHodge0 ε (fun _ => c) v = 0 :=
  vrHodge0_const H ε c v

/-- **Self-adjointness (ℓ² symmetry) of the Hodge 0-Laplacian.**
For all `f g : V → ℝ`,

  `∑ v, f v · (vrHodge0 g v) = ∑ v, g v · (vrHodge0 f v)`.

This is the spectral-theorem prerequisite for IT3: `vrHodge0` has a
real spectrum and an orthogonal eigenbasis (finite-dim spectral
theorem).

Proof strategy: split each side into two double sums. The
"bilinear cross term" `∑_{(v,u) adj} f(v) g(u)` has a swap-under-adj
symmetry (since `SimpleGraph.Adj` is symmetric, so the ordered pair
`(v,u)` running over adjacent pairs is in bijection with `(u,v)`
running over the same set). The "diagonal" contributions
`∑_{(v,u) adj} f(v) g(v)` collect into `∑_v deg(v) · f(v) · g(v)` —
already symmetric in `f ↔ g`. So the two sides agree. -/
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
  -- Now each side is a double sum over (v, u) pairs. Split into
  -- cross (f v * g u) and diagonal (f v * g v) contributions; the
  -- diagonal is trivially symmetric, the cross is symmetric under
  -- the adj-swap (adj v u ↔ adj u v).
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
