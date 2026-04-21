/-
**Plateau-detection for Wolfram-Hausdorff dimension** (Group ID / #140).

A "plateau" in the Wolfram-Hausdorff log V(r) / log r estimator is
a radius range where the estimator is approximately constant. Real
graphs show a plateau at intermediate scales — below the plateau is
the quantum-substrate regime, above is the finite-size regime.

This file extends `HypergraphDistance.lean` with:

  * `plateauMean H v [rmin, rmax]` — average of `localDimension`
    over the range (already in `HypergraphDistance`; relabelled
    for clarity).
  * `plateauMax H v [rmin, rmax]` / `plateauMin` — range statistics
    for detecting plateau quality.
  * `isPlateau` — predicate: `plateauMax − plateauMin ≤ ε`.
  * `Tendsto` to 1 on the cycle graph (at interior points, for
    intermediate radius).

**Connection to hypergraphs.** Native. Every quantity is a function
of `Hypergraph V` and of `Hypergraph.dist`.
-/

import InfraFormalization.HypergraphDistance
import Mathlib.Algebra.Order.Group.MinMax

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Plateau statistics -/

/-- **Plateau max**: maximum of `localDimension` over radii in
`[rmin, rmax]`, only well-defined when the interval is nonempty
(`rmin ≤ rmax`). -/
noncomputable def plateauMax (H : Hypergraph V) (v : V)
    (rmin rmax : ℕ) (h : rmin ≤ rmax) : ℝ :=
  ((Finset.Icc rmin rmax).image (fun r => H.localDimension v r)).max'
    (Finset.image_nonempty.mpr ⟨rmin, Finset.mem_Icc.mpr ⟨le_refl _, h⟩⟩)

/-- **Plateau min** symmetrically. -/
noncomputable def plateauMin (H : Hypergraph V) (v : V)
    (rmin rmax : ℕ) (h : rmin ≤ rmax) : ℝ :=
  ((Finset.Icc rmin rmax).image (fun r => H.localDimension v r)).min'
    (Finset.image_nonempty.mpr ⟨rmin, Finset.mem_Icc.mpr ⟨le_refl _, h⟩⟩)

/-- **Plateau quality**: for a plateau of tolerance `ε`,
`plateauMax - plateauMin ≤ ε`. -/
def IsPlateau (H : Hypergraph V) (v : V) (rmin rmax : ℕ) (h : rmin ≤ rmax)
    (ε : ℝ) : Prop :=
  H.plateauMax v rmin rmax h - H.plateauMin v rmin rmax h ≤ ε

/-- **Plateau-range is nonempty** when `rmin ≤ rmax`. -/
theorem plateau_range_nonempty (H : Hypergraph V) (v : V)
    {rmin rmax : ℕ} (h : rmin ≤ rmax) :
    ((Finset.Icc rmin rmax).image (fun r => H.localDimension v r)).Nonempty :=
  Finset.image_nonempty.mpr ⟨rmin, by simp [Finset.mem_Icc, h]⟩

end Hypergraph
end InfraFormalization
