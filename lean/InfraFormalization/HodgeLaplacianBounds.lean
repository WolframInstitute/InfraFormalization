/-
**Hodge 0-Laplacian spectrum bounds** (IT3 extension, PHAJEK).

Extends `HodgeLaplacianSpectrum.lean` with a spectrum-sign theorem:
`⟨f, vrHodge0 f⟩ ≤ 0` for all `f`, i.e., the Hodge 0-Laplacian is
negative semi-definite. This is the sign-convention statement that
pairs with the constants-in-kernel theorem to give the full picture
of the spectrum on the nonneg half-line (under the `-vrHodge0` sign,
which is the standard convention).

Method: expand `⟨f, vrHodge0 f⟩` as a sum over ordered adjacent
pairs, then use the Adj-symmetry swap to rewrite it as
`-∑_{edges} (f u − f v)²`, which is manifestly ≤ 0.

All grounded on `Hypergraph V`.
-/

import InfraFormalization.HodgeLaplacianSpectrum

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Hodge 0-Laplacian is negative semi-definite** (sign convention).
For every `f : V → ℝ`,
  `∑ v, f v · (vrHodge0 ε f v) ≤ 0`.

Using the expansion over ordered pairs and then Adj-symmetry to
combine `(v,u)` and `(u,v)`, the quadratic form equals
`-½ · ∑_{(v,u) ord adj} (f u − f v)²`, which is `≤ 0`. -/
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
    -- Now we need: ∑∑ if Adj then f(v)(f(u)-f(v)) else 0
    --            = -(1/2) ∑∑ if Adj then (f(v)-f(u))² else 0
    -- Equivalent (multiply both sides by -2):
    --   -2 ∑∑ if Adj then f(v)(f(u)-f(v)) else 0
    --   = ∑∑ if Adj then (f(v)-f(u))² else 0
    -- Symmetry under swap: ∑_v ∑_u if Adj v u then X(v,u) else 0
    --                    = ∑_u ∑_v if Adj u v then X(v,u) else 0
    --                    = ∑_v ∑_u if Adj v u then X(u,v) else 0
    -- (using Adj.symm).
    -- Let X(v,u) := f(v)(f(u) - f(v)). Then X(v,u) + X(u,v)
    --             = f(v)f(u) - f(v)² + f(u)f(v) - f(u)²
    --             = -(f(v)-f(u))² + f(v)f(u) + f(v)f(u) - f(v)² - f(u)² + 2f(v)f(u)
    -- Hmm, let me just compute: X(v,u) + X(u,v)
    --   = f(v)f(u) - f(v)² + f(u)f(v) - f(u)² = 2f(v)f(u) - f(v)² - f(u)²
    --   = -(f(v)² - 2f(v)f(u) + f(u)²) = -(f(v) - f(u))²
    -- So summing the matrix equation LHS = ∑_{(v,u) ord} X(v,u),
    -- 2 LHS = ∑_{(v,u) ord} (X(v,u) + X(u,v)) = -∑_{ord} (f v - f u)².
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
