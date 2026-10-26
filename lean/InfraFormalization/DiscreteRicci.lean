/-
Discrete curvatures on graphs and hypergraphs.

This module defines the unit-weight Forman-Ricci curvature of a pair of vertices,
`4 − deg(v) − deg(w)`, which is Forman's (2003) edge curvature with all vertex
and edge weights equal to 1. It proves the values on `k`-regular graphs: `4 − 2k`
per edge, `k(4 − 2k)` per vertex and `|V|·k(4 − 2k)` in total, so the edge value
is 0 when every degree is 2. It defines a per-hyperedge value `k(2 − k)`, a
triangle-corrected edge curvature on the clique expansion, and two scalar
curvature estimators obtained by comparing ball volume and sphere size with
Euclidean values. No convergence to a continuum curvature is proved here.
-/

import InfraFormalization.DiscreteCalculus
import InfraFormalization.Hypergraph
import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unit-weight Forman-Ricci curvature `4 − deg(v) − deg(w)` for a pair of
vertices of a `Neighbourhood V`. The definition does not require `v` and `w`
to be adjacent. -/
def formanRicciEdge (N : Neighbourhood V) (v w : V) : ℤ :=
  4 - (N.degree v : ℤ) - (N.degree w : ℤ)

/-- Forman-Ricci is symmetric under swapping the edge endpoints. -/
theorem formanRicciEdge_symm (N : Neighbourhood V) (v w : V) :
    formanRicciEdge N v w = formanRicciEdge N w v := by
  unfold formanRicciEdge
  ring

/-- If every vertex has degree `2`, then `formanRicciEdge N v w = 0` for all
`v, w`. -/
theorem formanRicciEdge_zero_of_two_regular (N : Neighbourhood V)
    (h : ∀ v : V, N.degree v = 2) (v w : V) :
    formanRicciEdge N v w = 0 := by
  unfold formanRicciEdge
  rw [h v, h w]
  ring

/-- If every vertex has degree `k`, then `formanRicciEdge N v w = 4 − 2k` for
all `v, w`. -/
theorem formanRicciEdge_regular (N : Neighbourhood V)
    (k : Nat) (h : ∀ v : V, N.degree v = k) (v w : V) :
    formanRicciEdge N v w = 4 - 2 * (k : ℤ) := by
  unfold formanRicciEdge
  rw [h v, h w]
  ring

/-- The sum of `formanRicciEdge N v w` over the neighbours `w` of `v`. -/
def formanRicciVertex (N : Neighbourhood V) (v : V) : ℤ :=
  ∑ w ∈ N.nbhd v, formanRicciEdge N v w

/-- If every vertex has degree `k`, then `formanRicciVertex N v = k · (4 − 2k)`. -/
theorem formanRicciVertex_regular (N : Neighbourhood V)
    (k : Nat) (h : ∀ v : V, N.degree v = k) (v : V) :
    formanRicciVertex N v = (k : ℤ) * (4 - 2 * (k : ℤ)) := by
  unfold formanRicciVertex
  rw [show (∑ w ∈ N.nbhd v, formanRicciEdge N v w)
        = (∑ _w ∈ N.nbhd v, (4 - 2 * (k : ℤ))) from by
      apply Finset.sum_congr rfl
      intros w _
      exact formanRicciEdge_regular N k h v w]
  rw [Finset.sum_const]
  have hcard : (N.nbhd v).card = k := by
    have := h v
    unfold Neighbourhood.degree at this
    exact this
  rw [hcard]
  push_cast
  ring

/-- The sum of `formanRicciVertex N v` over all vertices `v`. -/
def formanRicciTotalScalar (N : Neighbourhood V) : ℤ :=
  ∑ v : V, formanRicciVertex N v

/-- If every vertex has degree `k`, then
`formanRicciTotalScalar N = |V| · k · (4 − 2k)`. -/
theorem formanRicciTotalScalar_regular (N : Neighbourhood V)
    (k : Nat) (h : ∀ v : V, N.degree v = k) :
    formanRicciTotalScalar N = (Fintype.card V : ℤ) * (k : ℤ) * (4 - 2 * (k : ℤ)) := by
  unfold formanRicciTotalScalar
  rw [show (∑ v : V, formanRicciVertex N v)
        = (∑ _v : V, (k : ℤ) * (4 - 2 * (k : ℤ))) from by
      apply Finset.sum_congr rfl
      intros v _
      exact formanRicciVertex_regular N k h v]
  rw [Finset.sum_const, Finset.card_univ]
  push_cast
  ring

/-! ## A per-hyperedge curvature

For a hyperedge with `k` distinct vertices the value is `k · (2 − k)`. It is 0
for `k = 2` and `−3` for `k = 3`. The hypergraph total is the sum over all
hyperedges.
-/

/-- `k · (2 − k)`, where `k` is the number of distinct vertices of `e`. -/
def formanRicciHyperedge (e : Hyperedge V) : ℤ :=
  let k := e.verts.toFinset.card
  (k : ℤ) * (2 - (k : ℤ))

/-- A hyperedge with exactly two distinct vertices has value 0. -/
theorem formanRicciHyperedge_two_vertex (e : Hyperedge V)
    (h : e.verts.toFinset.card = 2) :
    formanRicciHyperedge e = 0 := by
  unfold formanRicciHyperedge
  rw [h]
  ring

/-- A hyperedge with at least three distinct vertices has a negative value. -/
theorem formanRicciHyperedge_neg_of_three_or_more (e : Hyperedge V)
    (h : 3 ≤ e.verts.toFinset.card) :
    formanRicciHyperedge e < 0 := by
  unfold formanRicciHyperedge
  have hk : (3 : ℤ) ≤ (e.verts.toFinset.card : ℤ) := by exact_mod_cast h
  nlinarith

/-- The sum of `formanRicciHyperedge` over the hyperedges of `H`, counted with
multiplicity. -/
noncomputable def formanRicciHypergraph (H : Hypergraph V) : ℤ :=
  (H.edges.map formanRicciHyperedge).sum

/-! ## Triangle-corrected Forman curvature on the clique expansion

For vertices `v, w` the value is
`F(v, w) = 4 − deg(v) − deg(w) + 3 · #triangles(v, w)`,
with degrees and triangle counts taken in the clique-expansion adjacency
`H.Adj`. This is the augmented Forman curvature of Sreejith, Mohan and Saucan
with unit weights. -/

/-- The number of common `H.Adj`-neighbours of `v` and `w`. -/
def Hypergraph.trianglesThroughEdge (H : Hypergraph V) (v w : V) : ℕ :=
  (Finset.univ.filter (fun x => H.Adj v x ∧ H.Adj w x)).card

/-- The number of `H.Adj`-neighbours of `v`. -/
def Hypergraph.adjDegree (H : Hypergraph V) (v : V) : ℕ :=
  (Finset.univ.filter (H.Adj v ·)).card

/-- `4 − adjDegree v − adjDegree w + 3 · trianglesThroughEdge v w`. -/
def Hypergraph.formanRicciEdgeTriangle (H : Hypergraph V) (v w : V) : ℤ :=
  4 - (H.adjDegree v : ℤ) - (H.adjDegree w : ℤ)
    + 3 * (H.trianglesThroughEdge v w : ℤ)

/-- The triangle count is symmetric in its two endpoints. -/
theorem Hypergraph.trianglesThroughEdge_symm (H : Hypergraph V) (v w : V) :
    H.trianglesThroughEdge v w = H.trianglesThroughEdge w v := by
  unfold Hypergraph.trianglesThroughEdge
  apply Finset.card_bij (fun x _ => x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.2, hx.1⟩
  · intros _ _ _ _ h; exact h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx.2, hx.1⟩

/-- `formanRicciEdgeTriangle` is symmetric in its two vertices. -/
theorem Hypergraph.formanRicciEdgeTriangle_symm (H : Hypergraph V) (v w : V) :
    H.formanRicciEdgeTriangle v w = H.formanRicciEdgeTriangle w v := by
  unfold Hypergraph.formanRicciEdgeTriangle
  rw [H.trianglesThroughEdge_symm v w]
  ring

/-- The sum of `formanRicciEdgeTriangle v w` over all ordered pairs `(v, w)`
with `H.Adj v w`. -/
def Hypergraph.formanRicciTriangleDoubled (H : Hypergraph V) : ℤ :=
  ∑ v : V, ∑ w ∈ Finset.univ.filter (H.Adj v ·),
    H.formanRicciEdgeTriangle v w

/-- If every hyperedge of `H` has exactly two distinct vertices, then
`formanRicciHypergraph H = 0`. -/
theorem formanRicciHypergraph_zero_of_simple (H : Hypergraph V)
    (hall : ∀ e ∈ H.edges, e.verts.toFinset.card = 2) :
    formanRicciHypergraph H = 0 := by
  unfold formanRicciHypergraph
  -- Prove for an arbitrary multiset satisfying the hypothesis.
  have helper : ∀ (s : Multiset (Hyperedge V)),
      (∀ e ∈ s, e.verts.toFinset.card = 2) →
      (s.map formanRicciHyperedge).sum = 0 := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons e es ih =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      have he : e.verts.toFinset.card = 2 :=
        hs e (Multiset.mem_cons_self e es)
      rw [formanRicciHyperedge_two_vertex e he]
      have hes : ∀ e' ∈ es, e'.verts.toFinset.card = 2 := fun e' he' =>
        hs e' (Multiset.mem_cons_of_mem he')
      rw [ih hes]
      ring
  exact helper H.edges hall

/-! ## Scalar curvature estimator from ball volume

In a `d`-dimensional Riemannian manifold the volume of a small geodesic ball
satisfies `V(p, r) = Ω_d · r^d · [1 − R(p) · r²/(6(d+2)) + O(r⁴)]`, where `R(p)`
is the scalar curvature and `Ω_d` is the volume of the Euclidean unit ball.
Solving for `R` motivates the discrete estimator

  `R(v, r) := (6(d+2)/r²) · [1 − V(v, r) / V_flat(d, r)]`,

with `V(v, r)` the vertex count `geodesicBallVolume v r` and
`V_flat(d, r) := Ω_d · r^d`. The dimension `d` is a parameter. No relation
between this estimator and the curvature of a limit space is proved here. -/

open Real

/-- The volume `Ω_d` of the Euclidean unit ball for `d ≤ 3` (1, 2, π, 4π/3).
For `d ≥ 4` the definition returns 1, which is not `Ω_d`. -/
noncomputable def unitBallVolumeEuclidean : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => Real.pi
  | 3 => 4 * Real.pi / 3
  | _ => 1  -- placeholder value for d ≥ 4

/-- `V_flat(d, r) := unitBallVolumeEuclidean d · r^d`. -/
noncomputable def flatBallVolume (d : ℕ) (r : ℕ) : ℝ :=
  unitBallVolumeEuclidean d * (r : ℝ)^d

/-- The ball-volume scalar curvature estimator
`(6(d+2)/r²) · [1 − geodesicBallVolume v r / flatBallVolume d r]` for `r > 0`,
and 0 for `r = 0`. It is positive exactly when the ball volume is below
`flatBallVolume d r` (see `scalarCurvatureAt_pos_iff`). -/
noncomputable def Hypergraph.scalarCurvatureAt {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ) : ℝ :=
  if 0 < r then
    (6 * (d + 2) / ((r : ℝ)^2)) *
      (1 - (H.geodesicBallVolume v r : ℝ) / flatBallVolume d r)
  else 0

/-- If `r > 0`, `flatBallVolume d r > 0` and the ball volume equals
`flatBallVolume d r`, then `scalarCurvatureAt v d r = 0`. -/
theorem Hypergraph.scalarCurvatureAt_zero_of_match {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ)
    (hr : 0 < r)
    (hmatch : (H.geodesicBallVolume v r : ℝ) = flatBallVolume d r)
    (hflat_pos : 0 < flatBallVolume d r) :
    H.scalarCurvatureAt v d r = 0 := by
  unfold Hypergraph.scalarCurvatureAt
  rw [if_pos hr, hmatch, div_self (ne_of_gt hflat_pos), sub_self, mul_zero]

/-- For `r > 0` and `flatBallVolume d r > 0`, `scalarCurvatureAt v d r` is
positive if and only if the ball volume is less than `flatBallVolume d r`. -/
theorem Hypergraph.scalarCurvatureAt_pos_iff {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ)
    (hr : 0 < r) (hflat_pos : 0 < flatBallVolume d r) :
    0 < H.scalarCurvatureAt v d r ↔
      (H.geodesicBallVolume v r : ℝ) < flatBallVolume d r := by
  unfold Hypergraph.scalarCurvatureAt
  rw [if_pos hr]
  have h_coef_pos : 0 < 6 * ((d : ℝ) + 2) / ((r : ℝ)^2) := by
    apply div_pos
    · positivity
    · positivity
  -- 6(d+2)/r² is positive; sign of product matches sign of the bracket.
  have h_coef_eq : 6 * ((d : ℕ) + 2 : ℝ) / ((r : ℝ)^2) =
                   6 * ((d : ℝ) + 2) / ((r : ℝ)^2) := by
    push_cast
    ring
  rw [h_coef_eq]
  rw [mul_pos_iff_of_pos_left h_coef_pos]
  constructor
  · intro h
    have h' : (H.geodesicBallVolume v r : ℝ) / flatBallVolume d r < 1 := by linarith
    rwa [div_lt_one hflat_pos] at h'
  · intro h
    have h' : (H.geodesicBallVolume v r : ℝ) / flatBallVolume d r < 1 := by
      rw [div_lt_one hflat_pos]; exact h
    linarith

/-! ## Scalar curvature estimator from sphere size

In a `d`-dimensional Riemannian manifold the area of a small geodesic sphere
satisfies `|S(p, r)| = S_d · r^(d-1) · [1 − R(p) · r²/(6d) + O(r⁴)]`, where
`S_d = d · Ω_d` is the area of the Euclidean unit sphere. The discrete
estimator is `(6d/r²) · [1 − |S(v, r)| / S_flat(d, r)]` with
`S_flat(d, r) := S_d · r^(d-1)` and `|S(v, r)|` the vertex count
`infraSphereVolume v r`.
-/

/-- The area `S_d` of the unit sphere in `d`-dimensional Euclidean space for
`d ≤ 3` (0, 2, 2π, 4π). For `d ≥ 4` the definition returns 1, which is not
`S_d`. -/
noncomputable def unitSphereAreaEuclidean : ℕ → ℝ
  | 0 => 0  -- the (-1)-sphere is empty
  | 1 => 2  -- two endpoints of the interval
  | 2 => 2 * Real.pi
  | 3 => 4 * Real.pi
  | _ => 1  -- placeholder value for d ≥ 4

/-- `S_flat(d, r) := unitSphereAreaEuclidean d · r^(d-1)`, with natural-number
subtraction in the exponent. -/
noncomputable def flatSphereArea (d : ℕ) (r : ℕ) : ℝ :=
  unitSphereAreaEuclidean d * (r : ℝ)^(d - 1)

/-- The sphere-size scalar curvature estimator
`(6d/r²) · (1 − infraSphereVolume v r / flatSphereArea d r)` for `r > 0`, and 0
for `r = 0`. -/
noncomputable def Hypergraph.surfaceCurvatureAt {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ) : ℝ :=
  if 0 < r then
    (6 * (d : ℝ) / ((r : ℝ)^2)) *
      (1 - (H.infraSphereVolume v r : ℝ) / flatSphereArea d r)
  else 0

/-- If `r > 0`, `flatSphereArea d r > 0` and the sphere size equals
`flatSphereArea d r`, then `surfaceCurvatureAt v d r = 0`. -/
theorem Hypergraph.surfaceCurvatureAt_zero_of_match {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ)
    (hr : 0 < r)
    (hmatch : (H.infraSphereVolume v r : ℝ) = flatSphereArea d r)
    (hflat_pos : 0 < flatSphereArea d r) :
    H.surfaceCurvatureAt v d r = 0 := by
  unfold Hypergraph.surfaceCurvatureAt
  rw [if_pos hr, hmatch, div_self (ne_of_gt hflat_pos), sub_self, mul_zero]

end InfraFormalization
