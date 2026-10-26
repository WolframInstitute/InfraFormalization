/-
Plateaus of the local dimension estimator.

A plateau of the estimator `localDimension v r = log V(r) / log r` is a range of radii on which it
is
nearly constant. This module defines the maximum `plateauMax` and minimum `plateauMin` of
`localDimension v r` over `r ∈ [rmin, rmax]`, the predicate `IsPlateau` that their difference is at
most `ε`, and proves that the set of values over a nonempty range is nonempty.
-/

import InfraFormalization.HypergraphDistance
import Mathlib.Algebra.Order.Group.MinMax

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Plateau statistics -/

/-- The maximum of `localDimension v r` over `r ∈ [rmin, rmax]`, for `rmin ≤ rmax`. -/
noncomputable def plateauMax (H : Hypergraph V) (v : V)
    (rmin rmax : ℕ) (h : rmin ≤ rmax) : ℝ :=
  ((Finset.Icc rmin rmax).image (fun r => H.localDimension v r)).max'
    (Finset.image_nonempty.mpr ⟨rmin, Finset.mem_Icc.mpr ⟨le_refl _, h⟩⟩)

/-- The minimum of `localDimension v r` over `r ∈ [rmin, rmax]`, for `rmin ≤ rmax`. -/
noncomputable def plateauMin (H : Hypergraph V) (v : V)
    (rmin rmax : ℕ) (h : rmin ≤ rmax) : ℝ :=
  ((Finset.Icc rmin rmax).image (fun r => H.localDimension v r)).min'
    (Finset.image_nonempty.mpr ⟨rmin, Finset.mem_Icc.mpr ⟨le_refl _, h⟩⟩)

/-- `plateauMax - plateauMin ≤ ε` on `[rmin, rmax]`. -/
def IsPlateau (H : Hypergraph V) (v : V) (rmin rmax : ℕ) (h : rmin ≤ rmax)
    (ε : ℝ) : Prop :=
  H.plateauMax v rmin rmax h - H.plateauMin v rmin rmax h ≤ ε

/-- For `rmin ≤ rmax`, the set of values of `localDimension v r` over `[rmin, rmax]` is nonempty. -/
theorem plateau_range_nonempty (H : Hypergraph V) (v : V)
    {rmin rmax : ℕ} (h : rmin ≤ rmax) :
    ((Finset.Icc rmin rmax).image (fun r => H.localDimension v r)).Nonempty :=
  Finset.image_nonempty.mpr ⟨rmin, by simp [Finset.mem_Icc, h]⟩

end Hypergraph
end InfraFormalization
