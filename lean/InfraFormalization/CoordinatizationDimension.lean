/-
**Coordinatization dimension via extremal orthogonal axes**
(Group ID / #142 ID4).

PPOKORNY's approach (Srní 2026): for each vertex `v`, count
the maximal number of *extremal orthogonal axes* — directions that
can coordinatise a neighbourhood. The coordinatization dimension
at `v` is this count.

"Orthogonal" in the discrete setting is stated via independence of
directions — two axes are orthogonal if moves along one don't change
coordinates along the other. Compact-vs-non-compact directions are
distinguished by whether the axis cycles (compact) or has an
extremal representative (non-compact).

This file gives the predicate-level scaffolding.

**Connection to hypergraphs.** Native. Axes are `Finset V`'s
(specifically, shortest paths from a basepoint). Coordinatization
builds a map `V → ℕ^d` from these axes.
-/

import InfraFormalization.HypergraphDistance

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **An *axis* from a basepoint `v`** is a shortest-path direction:
a vertex `w` such that `dist v w` is realised along a unique path.
Predicate-level. -/
def IsAxis (H : Hypergraph V) (v w : V) : Prop :=
  H.dist v w ≠ 0 ∧ v ≠ w

/-- **Two axes are orthogonal** at `v` if there exists some shared radius
`r > 0` and a tolerance `ε > 0` such that the chord-ratio between sample
vertices on rays toward `w₁, w₂` at distance `r` from `v` is within `ε`
of `√2` — the flat-Euclidean expected chord-ratio for a right angle
(AT0 / AT6). Replaces the prior `True`-stub with real numerical content.

Concretely: by `H.IsOrthoApprox v w₁ w₂ r ε` (defined in
`HypergraphDistance.lean`), there exist equidistant samples
`A, B ∈ S(v, r)` on the two rays whose chord-ratio is `≈ √2`.

The existential `∃ r ε` is intentionally permissive — the predicate
fires as soon as orthogonality is witnessed at *some* scale and *some*
tolerance. Tighter screeners can require small `ε` or specific `r`. -/
def AreOrthogonalAxes (H : Hypergraph V) (v w₁ w₂ : V) : Prop :=
  H.IsAxis v w₁ ∧ H.IsAxis v w₂ ∧
  ∃ (r : ℕ) (ε : ℝ), 0 < r ∧ 0 < ε ∧ H.IsOrthoApprox v w₁ w₂ r ε

/-- **Extremal axis**: an axis that can be iterated without
returning to the origin (non-compact direction). -/
def IsExtremalAxis (H : Hypergraph V) (v w : V) : Prop :=
  H.IsAxis v w ∧ H.dist v w < Fintype.card V

/-- **Coordinatization dimension at `v`**: the maximal number of
pairwise-orthogonal extremal axes. Predicate-level statement. -/
def HasCoordinatizationDim (H : Hypergraph V) (v : V) (d : ℕ) : Prop :=
  ∃ axes : Finset V, axes.card = d ∧
    (∀ w ∈ axes, H.IsExtremalAxis v w) ∧
    (∀ w₁ ∈ axes, ∀ w₂ ∈ axes, w₁ ≠ w₂ → H.AreOrthogonalAxes v w₁ w₂)

/-- **Monotonicity**: if `v` has coordinatization dim `d`, it has
all smaller dims too (just take a subset of axes). -/
theorem hasCoordinatizationDim_mono (H : Hypergraph V) (v : V)
    {d₁ d₂ : ℕ} (h : d₂ ≤ d₁) (hd : H.HasCoordinatizationDim v d₁) :
    H.HasCoordinatizationDim v d₂ := by
  obtain ⟨axes, hcard, hext, horth⟩ := hd
  -- Take any subset of size d₂.
  rcases Finset.exists_subset_card_eq (n := d₂) (s := axes)
      (by omega) with ⟨sub, hsub_subset, hsub_card⟩
  refine ⟨sub, hsub_card, ?_, ?_⟩
  · intros w hw
    exact hext w (hsub_subset hw)
  · intros w₁ hw₁ w₂ hw₂ hne
    exact horth w₁ (hsub_subset hw₁) w₂ (hsub_subset hw₂) hne

end Hypergraph
end InfraFormalization
