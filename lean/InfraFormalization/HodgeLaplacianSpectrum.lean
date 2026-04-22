/-
**Spectrum of the Hodge 0-Laplacian on a VR complex** (task IT3 / #135 partial).

Pavel Hajek's IT3 asks for the spectrum of the Hodge Laplacian on the
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

end Hypergraph
end InfraFormalization
