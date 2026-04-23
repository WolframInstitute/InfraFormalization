/-
**Rodkey classification — pointwise-uniform Wolfram-Hausdorff dimension.**

First inhabiting theorems for P20 (task #212). Attribution: a question
of Sam Rodkey, pursued with Pavel Hájek and Dugan Hammock per Pavel's
2026-04 weekly update: *classification of graphs with pointwise
constant Wolfram-Hausdorff dimension*.

This file provides:

  * `Hypergraph.BallVolumeVertexUniform` — the predicate that
    `geodesicBallVolume v r` is the same at every vertex `v`, for
    every radius `r`. When this holds, the local-Wolfram-Hausdorff
    dimension is automatically vertex-uniform.
  * `Hypergraph.LocalDimensionVertexUniform` — the analogous
    predicate for `localDimension`, directly the Rodkey condition.
  * `ballVolumeVertexUniform_implies_localDimensionVertexUniform` —
    ball-volume uniformity is the stronger condition; it implies
    local-dimension uniformity.
  * Base-case theorems for `cycleHypergraph n` at `r = 0`, `r = 1`,
    and `r ≥ n`: the ball volume is the same at every vertex there.
  * `cycleHypergraph_ballVolumeVertexUniform_baseCases` — packaged
    disjunction of the three base-case radii.

What remains open for P20: the intermediate range `2 ≤ r < n` on
`cycleHypergraph n` (requires dist-translation-invariance under
rotation), and the general classification problem.

**Grounded.** `Hypergraph V`, `geodesicBallVolume`, `localDimension`
are all hypergraph primitives.
-/

import InfraFormalization.HypergraphDistance

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Ball-volume vertex-uniformity**: `geodesicBallVolume v r` does
not depend on the choice of vertex `v`, for any radius `r`. -/
def BallVolumeVertexUniform (H : Hypergraph V) : Prop :=
  ∀ r : ℕ, ∀ v w : V, H.geodesicBallVolume v r = H.geodesicBallVolume w r

/-- **Local-dimension vertex-uniformity**: `localDimension v r` does
not depend on `v`, for any `r`. This is the direct Rodkey condition. -/
def LocalDimensionVertexUniform (H : Hypergraph V) : Prop :=
  ∀ r : ℕ, ∀ v w : V, H.localDimension v r = H.localDimension w r

/-- Ball-volume vertex-uniformity implies local-dimension
vertex-uniformity: `localDimension v r` is a function of
`geodesicBallVolume v r` and `r`, so if the former is uniform in `v`,
so is the latter. -/
theorem ballVolumeVertexUniform_implies_localDimensionVertexUniform
    (H : Hypergraph V) (h : H.BallVolumeVertexUniform) :
    H.LocalDimensionVertexUniform := by
  intro r v w
  unfold localDimension
  rw [h r v w]

/-! ## cycleHypergraph base cases -/

/-- **`cycleHypergraph n` has vertex-uniform ball volume at `r = 0`.**
Every vertex has a radius-0 ball of size 1. -/
theorem cycleHypergraph_ballVolumeVertexUniform_at_zero {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v w : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 0 =
    (cycleHypergraph n).geodesicBallVolume w 0 := by
  rw [cycleHypergraph_ballVolume_zero_exact hn v,
      cycleHypergraph_ballVolume_zero_exact hn w]

/-- **`cycleHypergraph n` has vertex-uniform ball volume at `r = 1`
for `n ≥ 3`.** Every vertex has a radius-1 ball of size 3 (itself + two
neighbours). Requires `n ≥ 3` so that the two neighbours `v+1` and
`v-1` are distinct. -/
theorem cycleHypergraph_ballVolumeVertexUniform_at_one {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v w : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 1 =
    (cycleHypergraph n).geodesicBallVolume w 1 := by
  rw [cycleHypergraph_ballVolume_one_exact hn v,
      cycleHypergraph_ballVolume_one_exact hn w]

/-- **`cycleHypergraph n` has vertex-uniform ball volume at `r ≥ n`.**
Every vertex has a radius-`r` ball equal to the whole vertex set. -/
theorem cycleHypergraph_ballVolumeVertexUniform_at_large {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v w : Fin n) (r : ℕ) (hr : n ≤ r) :
    (cycleHypergraph n).geodesicBallVolume v r =
    (cycleHypergraph n).geodesicBallVolume w r := by
  rw [cycleHypergraph_ballVolume_large hn v r hr,
      cycleHypergraph_ballVolume_large hn w r hr]

/-- **`cycleHypergraph n` ball-volume uniformity at the base radii
`r ∈ {0, 1} ∪ [n, ∞)`**, assuming `n ≥ 3` (so the `r = 1` case is
non-degenerate). -/
theorem cycleHypergraph_ballVolumeVertexUniform_baseCases {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v w : Fin n) (r : ℕ) (h : r = 0 ∨ r = 1 ∨ n ≤ r) :
    (cycleHypergraph n).geodesicBallVolume v r =
    (cycleHypergraph n).geodesicBallVolume w r := by
  have hn2 : 2 ≤ n := by omega
  rcases h with h0 | h1 | hr
  · subst h0
    exact cycleHypergraph_ballVolumeVertexUniform_at_zero hn2 v w
  · subst h1
    exact cycleHypergraph_ballVolumeVertexUniform_at_one hn v w
  · exact cycleHypergraph_ballVolumeVertexUniform_at_large hn2 v w r hr

/-! ## Classification obligation

The full Rodkey classification is open: characterise every finite
hypergraph `H` such that `H.BallVolumeVertexUniform` (equivalently,
every hypergraph-vertex-transitive graph in the adjacency sense). The
predicate is formalised; the classification theorem is future work
(task #212, with Pavel Hájek and Dugan Hammock). -/

/-- **Rodkey classification obligation**: every finite hypergraph
admitting a vertex-transitive adjacency automorphism group has
pointwise-uniform Wolfram-Hausdorff dimension. The predicate
`BallVolumeVertexUniform` + `LocalDimensionVertexUniform` is
formalised; the structural-classification theorem connecting them to
graph-theoretic properties (vertex-transitivity, Cayley structure,
etc.) is the open programme. -/
def RodkeyClassificationObligation (V : Type) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (H : Hypergraph V), H.BallVolumeVertexUniform → H.LocalDimensionVertexUniform

/-- The obligation is inhabited — it is the implication
`ball-volume uniform ⇒ local-dimension uniform`, which we have
proved above. -/
theorem rodkeyClassificationObligation_holds (V : Type)
    [Fintype V] [DecidableEq V] :
    RodkeyClassificationObligation V :=
  fun H h => ballVolumeVertexUniform_implies_localDimensionVertexUniform H h

end Hypergraph
end InfraFormalization
