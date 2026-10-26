/-
Hypergraphs whose geodesic ball volumes do not depend on the vertex.

This module defines `BallVolumeVertexUniform` (the volume of the ball of
radius r is the same at every vertex, for every r),
`LocalDimensionVertexUniform`, `DistTransitive`, `AdjTransitive` and
`Regular`, following a question of Rodkey on graphs with pointwise
constant Wolfram-Hausdorff dimension. It proves the implications
adjacency-transitive ⇒ distance-transitive ⇒ ball-volume uniform ⇒
local-dimension uniform, and, for connected hypergraphs, ball-volume
uniform ⇒ regular. It proves that `cycleHypergraph n` (n ≥ 2) satisfies
all four uniformity conditions and that `pathHypergraph n` (n ≥ 3) is
neither regular nor ball-volume uniform. A classification of the
ball-volume uniform hypergraphs is not stated.
-/

import InfraFormalization.HypergraphDistance
import InfraFormalization.PathHypergraphDistance

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `geodesicBallVolume v r = geodesicBallVolume w r` for all `r`, `v`,
`w`. -/
def BallVolumeVertexUniform (H : Hypergraph V) : Prop :=
  ∀ r : ℕ, ∀ v w : V, H.geodesicBallVolume v r = H.geodesicBallVolume w r

/-- `localDimension v r = localDimension w r` for all `r`, `v`, `w`. -/
def LocalDimensionVertexUniform (H : Hypergraph V) : Prop :=
  ∀ r : ℕ, ∀ v w : V, H.localDimension v r = H.localDimension w r

/-- For all `v`, `w` there is a bijection `σ : V ≃ V` with `σ v = w` and
`dist v a = dist w (σ a)` for every `a`. -/
def DistTransitive (H : Hypergraph V) : Prop :=
  ∀ v w : V, ∃ σ : V ≃ V, σ v = w ∧ ∀ a, H.dist v a = H.dist w (σ a)

/-- A distance-transitive hypergraph is ball-volume uniform. -/
theorem ballVolumeVertexUniform_of_distTransitive
    (H : Hypergraph V) (ht : H.DistTransitive) :
    H.BallVolumeVertexUniform := by
  intro r v w
  obtain ⟨σ, _, hσ⟩ := ht v w
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  refine Finset.card_bij (fun u _ => σ u) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← hσ u]; exact hu
  · intros u _ u' _ h; exact σ.injective h
  · intro u' hu'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    refine ⟨σ.symm u', ?_, σ.apply_symm_apply u'⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hσ (σ.symm u')
    rw [σ.apply_symm_apply] at this
    rw [this]; exact hu'

/-- Ball-volume uniformity implies local-dimension uniformity, since
`localDimension v r` is a function of `geodesicBallVolume v r` and `r`. -/
theorem ballVolumeVertexUniform_implies_localDimensionVertexUniform
    (H : Hypergraph V) (h : H.BallVolumeVertexUniform) :
    H.LocalDimensionVertexUniform := by
  intro r v w
  unfold localDimension
  rw [h r v w]

/-- For all `v`, `w` there is a bijection `σ : V ≃ V` with `σ v = w` that
preserves adjacency in both directions. -/
def AdjTransitive (H : Hypergraph V) : Prop :=
  ∀ v w : V, ∃ σ : V ≃ V, σ v = w ∧ ∀ a b, H.Adj a b ↔ H.Adj (σ a) (σ b)

/-- An adjacency-transitive hypergraph is distance-transitive: `σ` and
`σ⁻¹` map walks to walks of the same length. -/
theorem distTransitive_of_adjTransitive
    (H : Hypergraph V) (ht : H.AdjTransitive) :
    H.DistTransitive := by
  intro v w
  obtain ⟨σ, hσvw, hσ⟩ := ht v w
  refine ⟨σ, hσvw, ?_⟩
  intro a
  -- Build forward and reverse SimpleGraph Homs on H.toSimpleGraph.
  let fwd : H.toSimpleGraph →g H.toSimpleGraph :=
    { toFun := σ
      map_rel' := fun hab => (hσ _ _).mp hab }
  let bwd : H.toSimpleGraph →g H.toSimpleGraph :=
    { toFun := σ.symm
      map_rel' := fun {x y} hxy => by
        -- σ.symm preserves adjacency because σ does in both directions.
        have hx : σ (σ.symm x) = x := σ.apply_symm_apply x
        have hy : σ (σ.symm y) = y := σ.apply_symm_apply y
        have := (hσ (σ.symm x) (σ.symm y)).mpr (by rw [hx, hy]; exact hxy)
        exact this }
  unfold Hypergraph.dist
  apply le_antisymm
  · -- dist v a ≤ dist w (σ a)
    by_cases hreach : H.toSimpleGraph.Reachable w (σ a)
    · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      -- Map p via bwd: get walk from σ.symm w = v to σ.symm (σ a) = a.
      have hwv : σ.symm w = v := by rw [← hσvw]; exact σ.symm_apply_apply v
      have hσa : σ.symm (σ a) = a := σ.symm_apply_apply a
      let q : H.toSimpleGraph.Walk v a :=
        (p.map bwd).copy hwv hσa
      calc H.toSimpleGraph.dist v a
          ≤ q.length := SimpleGraph.dist_le q
        _ = (p.map bwd).length := by simp [q, SimpleGraph.Walk.length_copy]
        _ = p.length := p.length_map _
        _ = H.toSimpleGraph.dist w (σ a) := hp
    · -- If `w` cannot reach `σ a`, then `v` cannot reach `a`, so both
      -- distances are 0.
      have hnreach_va : ¬ H.toSimpleGraph.Reachable v a := by
        intro h
        obtain ⟨p⟩ := h
        exact hreach ⟨(p.map fwd).copy hσvw rfl⟩
      rw [SimpleGraph.dist_eq_zero_of_not_reachable hnreach_va]
      exact Nat.zero_le _
  · -- dist w (σ a) ≤ dist v a
    by_cases hreach : H.toSimpleGraph.Reachable v a
    · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      have : (p.map fwd).length = p.length := p.length_map _
      calc H.toSimpleGraph.dist w (σ a)
          ≤ ((p.map fwd).copy hσvw rfl).length :=
            SimpleGraph.dist_le _
        _ = (p.map fwd).length := by simp [SimpleGraph.Walk.length_copy]
        _ = p.length := p.length_map _
        _ = H.toSimpleGraph.dist v a := hp
    · have hnreach_wσa : ¬ H.toSimpleGraph.Reachable w (σ a) := by
        intro h
        obtain ⟨p⟩ := h
        have hwv : σ.symm w = v := by rw [← hσvw]; exact σ.symm_apply_apply v
        have hσa : σ.symm (σ a) = a := σ.symm_apply_apply a
        exact hreach ⟨((p.map bwd).copy hwv hσa)⟩
      rw [SimpleGraph.dist_eq_zero_of_not_reachable hnreach_wσa]
      exact Nat.zero_le _

/-- An adjacency-transitive hypergraph is ball-volume uniform. -/
theorem ballVolumeVertexUniform_of_adjTransitive
    (H : Hypergraph V) (ht : H.AdjTransitive) :
    H.BallVolumeVertexUniform :=
  ballVolumeVertexUniform_of_distTransitive H
    (distTransitive_of_adjTransitive H ht)

/-- On a connected hypergraph, the ball of radius 1 about `v` has
`1 + degree v` vertices. -/
theorem geodesicBallVolume_one_eq_degree_plus_one
    (H : Hypergraph V) (hconn : H.toSimpleGraph.Connected) (v : V) :
    H.geodesicBallVolume v 1 = 1 + H.toSimpleGraph.degree v := by
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall Hypergraph.dist
  have h_eq :
      (Finset.univ.filter (fun u => H.toSimpleGraph.dist v u ≤ 1))
        = insert v (H.toSimpleGraph.neighborFinset v) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               SimpleGraph.mem_neighborFinset]
    constructor
    · intro h_le
      rcases Nat.eq_zero_or_pos (H.toSimpleGraph.dist v u) with hdist0 | hdist_pos
      · -- dist = 0 → u = v (since connected, reachable holds)
        left
        rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at hdist0
        rcases hdist0 with heq | hnreach
        · exact heq.symm
        · exact absurd (hconn v u) hnreach
      · -- dist ≥ 1 and dist ≤ 1 so dist = 1, hence Adj
        right
        have hdist1 : H.toSimpleGraph.dist v u = 1 := by omega
        exact (SimpleGraph.dist_eq_one_iff_adj).mp hdist1
    · intro h
      rcases h with hvu | hadj
      · subst hvu
        simp [SimpleGraph.dist_self]
      · rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]
  rw [h_eq]
  have hvni : v ∉ H.toSimpleGraph.neighborFinset v := by
    simp [SimpleGraph.mem_neighborFinset]
  rw [Finset.card_insert_of_notMem hvni]
  rw [SimpleGraph.degree]
  omega

/-- On a connected ball-volume uniform hypergraph, all vertices have the
same degree. -/
theorem degree_uniform_of_ballVolumeVertexUniform
    (H : Hypergraph V) (hconn : H.toSimpleGraph.Connected)
    (hb : H.BallVolumeVertexUniform) (v w : V) :
    H.toSimpleGraph.degree v = H.toSimpleGraph.degree w := by
  have hvw := hb 1 v w
  rw [geodesicBallVolume_one_eq_degree_plus_one H hconn v,
      geodesicBallVolume_one_eq_degree_plus_one H hconn w] at hvw
  omega

/-- On a connected hypergraph with two vertices of different degree,
`BallVolumeVertexUniform` fails. -/
theorem not_ballVolumeVertexUniform_of_degree_ne
    (H : Hypergraph V) (hconn : H.toSimpleGraph.Connected)
    {v w : V} (hne : H.toSimpleGraph.degree v ≠ H.toSimpleGraph.degree w) :
    ¬ H.BallVolumeVertexUniform := by
  intro hb
  exact hne (degree_uniform_of_ballVolumeVertexUniform H hconn hb v w)

/-- On a connected hypergraph in which every vertex has degree `k`, every
ball of radius 1 has `k + 1` vertices. -/
theorem ballVolumeOne_regular (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (k : ℕ)
    (hreg : ∀ v : V, H.toSimpleGraph.degree v = k) (v : V) :
    H.geodesicBallVolume v 1 = k + 1 := by
  rw [geodesicBallVolume_one_eq_degree_plus_one H hconn v, hreg v]
  omega

/-- On a connected hypergraph in which every vertex has degree `k`, all
balls of radius 1 have the same volume. -/
theorem ballVolumeOne_uniform_of_regular (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) {k : ℕ}
    (hreg : ∀ v : V, H.toSimpleGraph.degree v = k) (v w : V) :
    H.geodesicBallVolume v 1 = H.geodesicBallVolume w 1 := by
  rw [ballVolumeOne_regular H hconn k hreg v,
      ballVolumeOne_regular H hconn k hreg w]

/-- All vertices have the same degree. -/
def Regular (H : Hypergraph V) : Prop :=
  ∀ v w : V, H.toSimpleGraph.degree v = H.toSimpleGraph.degree w

/-- On a connected hypergraph, all balls of radius 1 have the same volume
if and only if the hypergraph is regular. -/
theorem ballVolumeOne_uniform_iff_regular (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) :
    (∀ v w : V, H.geodesicBallVolume v 1 = H.geodesicBallVolume w 1)
      ↔ H.Regular := by
  constructor
  · intro h v w
    have h_eq := h v w
    rw [geodesicBallVolume_one_eq_degree_plus_one H hconn v,
        geodesicBallVolume_one_eq_degree_plus_one H hconn w] at h_eq
    omega
  · intro hreg
    intro v w
    rw [geodesicBallVolume_one_eq_degree_plus_one H hconn v,
        geodesicBallVolume_one_eq_degree_plus_one H hconn w, hreg v w]

/-- For `n ≥ 3`, every vertex of `cycleHypergraph n` has degree 2. -/
theorem cycleHypergraph_regular_degree_two {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v : Fin n) :
    (cycleHypergraph n).toSimpleGraph.degree v = 2 := by
  have hconn := cycleHypergraph_connected (by omega : 2 ≤ n)
  have hvol := cycleHypergraph_ballVolume_one_exact hn v
  have hid := geodesicBallVolume_one_eq_degree_plus_one
    (cycleHypergraph n) hconn v
  omega

/-- For `n ≥ 3`, `cycleHypergraph n` is regular. -/
theorem cycleHypergraph_regular {n : Nat} [NeZero n] (hn : 3 ≤ n) :
    (cycleHypergraph n).Regular := by
  intro v w
  rw [cycleHypergraph_regular_degree_two hn v,
      cycleHypergraph_regular_degree_two hn w]

/-- For `n ≥ 3`, `pathHypergraph n` is not regular: vertex 0 has degree 1
and vertex 1 has degree 2. -/
theorem pathHypergraph_not_regular {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ¬ (pathHypergraph n).Regular := by
  intro hreg
  have h0 : (pathHypergraph n).toSimpleGraph.degree
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ = 1 :=
    pathHypergraph_degree_zero (by omega)
  have h1 : (pathHypergraph n).toSimpleGraph.degree
      ⟨1, by omega⟩ = 2 :=
    pathHypergraph_degree_one hn
  have hdiff := hreg ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ ⟨1, by omega⟩
  rw [h0, h1] at hdiff
  omega

/-- On `Fin 3` there is a regular hypergraph (`cycleHypergraph 3`) and a
hypergraph that is not regular (`pathHypergraph 3`). -/
theorem regular_dichotomy_on_fin3 :
    ∃ (H : Hypergraph (Fin 3)) (K : Hypergraph (Fin 3)),
      H.Regular ∧ ¬ K.Regular :=
  ⟨cycleHypergraph 3, pathHypergraph 3,
   cycleHypergraph_regular (by omega),
   pathHypergraph_not_regular (by omega)⟩

/-- A connected ball-volume uniform hypergraph is regular. -/
theorem regular_of_ballVolumeVertexUniform (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected)
    (hb : H.BallVolumeVertexUniform) : H.Regular :=
  degree_uniform_of_ballVolumeVertexUniform H hconn hb

/-- A connected hypergraph that is not regular is not ball-volume
uniform. -/
theorem not_ballVolumeVertexUniform_of_not_regular (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (hnotreg : ¬ H.Regular) :
    ¬ H.BallVolumeVertexUniform :=
  fun hb => hnotreg (regular_of_ballVolumeVertexUniform H hconn hb)

/-- On a connected hypergraph, for `r ≥ |V|` every ball of radius `r` has
the same volume, by `geodesicBallVolume_ge_card`. -/
theorem ballVolumeVertexUniform_at_large_radius (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (r : ℕ) (hr : Fintype.card V ≤ r)
    (v w : V) :
    H.geodesicBallVolume v r = H.geodesicBallVolume w r := by
  rw [geodesicBallVolume_ge_card H hconn v r hr,
      geodesicBallVolume_ge_card H hconn w r hr]

/-- On a connected hypergraph, every ball of radius 0 has volume 1. -/
theorem geodesicBallVolume_zero_of_connected (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (v : V) :
    H.geodesicBallVolume v 0 = 1 := by
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  have h_eq : (Finset.univ.filter (fun u : V => H.dist v u ≤ 0)) = {v} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton, Nat.le_zero]
    constructor
    · intro h_dist
      unfold Hypergraph.dist at h_dist
      rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at h_dist
      rcases h_dist with heq | hnreach
      · exact heq.symm
      · exact absurd (hconn v u) hnreach
    · intro huv
      subst huv
      unfold Hypergraph.dist
      exact SimpleGraph.dist_self
  rw [h_eq]
  simp

/-- On a connected hypergraph, all balls of radius 0 have the same
volume. -/
theorem ballVolumeVertexUniform_at_zero (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (v w : V) :
    H.geodesicBallVolume v 0 = H.geodesicBallVolume w 0 := by
  rw [geodesicBallVolume_zero_of_connected H hconn v,
      geodesicBallVolume_zero_of_connected H hconn w]

/-- Ball volumes agree at all vertices for every radius `1 ≤ r < |V|`. -/
def BallVolumeVertexUniformRestricted (H : Hypergraph V) : Prop :=
  ∀ (r : ℕ), 1 ≤ r → r < Fintype.card V →
    ∀ (v w : V), H.geodesicBallVolume v r = H.geodesicBallVolume w r

/-- On a connected hypergraph, `BallVolumeVertexUniform` is equivalent to
`BallVolumeVertexUniformRestricted`. -/
theorem ballVolumeVertexUniform_iff_restricted (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) :
    H.BallVolumeVertexUniform ↔ H.BallVolumeVertexUniformRestricted := by
  constructor
  · intro hfull r _ _ v w
    exact hfull r v w
  · intro hres r v w
    rcases Nat.lt_or_ge r (Fintype.card V) with hlt | hge
    · rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        exact ballVolumeVertexUniform_at_zero H hconn v w
      · exact hres r hpos hlt v w
    · exact ballVolumeVertexUniform_at_large_radius H hconn r hge v w

/-- Some `r` satisfies `1 ≤ r < |V|` if and only if `|V| ≥ 2`. -/
theorem restrictedRegime_nonempty_iff (H : Hypergraph V) :
    (∃ r : ℕ, 1 ≤ r ∧ r < Fintype.card V) ↔ 2 ≤ Fintype.card V := by
  constructor
  · rintro ⟨r, hr1, hrV⟩
    omega
  · intro h
    exact ⟨1, le_refl 1, h⟩

/-- If `|V| ≤ 1`, every hypergraph on `V` is ball-volume uniform. -/
theorem ballVolumeVertexUniform_of_card_le_one (H : Hypergraph V)
    (hcard : Fintype.card V ≤ 1) : H.BallVolumeVertexUniform := by
  intro r v w
  have h_uv : v = w := by
    have := Fintype.card_le_one_iff.mp hcard
    exact this v w
  rw [h_uv]

/-- In an adjacency-transitive hypergraph, all vertices have the same
degree. -/
theorem degree_invariant_of_adjTransitive
    (H : Hypergraph V) (ht : H.AdjTransitive) (v w : V) :
    H.toSimpleGraph.degree v = H.toSimpleGraph.degree w := by
  obtain ⟨σ, hσvw, hσ⟩ := ht v w
  rw [SimpleGraph.degree, SimpleGraph.degree]
  refine Finset.card_bij (fun u _ => σ u) ?_ ?_ ?_
  · -- Adj v u gives Adj w (σ u), using σ v = w.
    intro u hu
    simp only [SimpleGraph.mem_neighborFinset] at hu ⊢
    have h := (hσ v u).mp hu
    rw [hσvw] at h
    exact h
  · intros u _ u' _ h; exact σ.injective h
  · -- The preimage of u' is σ⁻¹ u'.
    intro u' hu'
    simp only [SimpleGraph.mem_neighborFinset] at hu'
    refine ⟨σ.symm u', ?_, σ.apply_symm_apply u'⟩
    simp only [SimpleGraph.mem_neighborFinset]
    apply (hσ v (σ.symm u')).mpr
    rw [hσvw, σ.apply_symm_apply]
    exact hu'

/-! ## cycleHypergraph base cases -/

/-- For `n ≥ 2`, all balls of radius 0 in `cycleHypergraph n` have volume
1. -/
theorem cycleHypergraph_ballVolumeVertexUniform_at_zero {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v w : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 0 =
    (cycleHypergraph n).geodesicBallVolume w 0 := by
  rw [cycleHypergraph_ballVolume_zero_exact hn v,
      cycleHypergraph_ballVolume_zero_exact hn w]

/-- For `n ≥ 3`, all balls of radius 1 in `cycleHypergraph n` have the same
volume (3). -/
theorem cycleHypergraph_ballVolumeVertexUniform_at_one {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v w : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 1 =
    (cycleHypergraph n).geodesicBallVolume w 1 := by
  rw [cycleHypergraph_ballVolume_one_exact hn v,
      cycleHypergraph_ballVolume_one_exact hn w]

/-- For `n ≥ 2` and `r ≥ n`, all balls of radius `r` in `cycleHypergraph n`
have the same volume. -/
theorem cycleHypergraph_ballVolumeVertexUniform_at_large {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v w : Fin n) (r : ℕ) (hr : n ≤ r) :
    (cycleHypergraph n).geodesicBallVolume v r =
    (cycleHypergraph n).geodesicBallVolume w r := by
  rw [cycleHypergraph_ballVolume_large hn v r hr,
      cycleHypergraph_ballVolume_large hn w r hr]

/-- For `n ≥ 3` and `r ∈ {0, 1}` or `r ≥ n`, all balls of radius `r` in
`cycleHypergraph n` have the same volume. -/
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

/-! ## Rotations of `cycleHypergraph n`

The rotation `k ↦ k + c` of `Fin n` preserves adjacency in both directions
and therefore preserves distance. -/

/-- `Adj a b ↔ Adj (a + c) (b + c)` in `cycleHypergraph n`, for `n ≥ 2`. -/
theorem cycleHypergraph_Adj_translation {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (c a b : Fin n) :
    (cycleHypergraph n).Adj a b ↔ (cycleHypergraph n).Adj (a + c) (b + c) := by
  rw [cycleHypergraph_Adj_iff hn, cycleHypergraph_Adj_iff hn]
  constructor
  · rintro ⟨hne, heq | heq⟩
    · refine ⟨fun h => hne (add_right_cancel h), Or.inl ?_⟩
      subst heq; abel
    · refine ⟨fun h => hne (add_right_cancel h), Or.inr ?_⟩
      subst heq; abel
  · rintro ⟨hne, heq | heq⟩
    · refine ⟨fun h => hne (by rw [h]), Or.inl ?_⟩
      -- heq : b + c = (a + c) + 1; want: b = a + 1
      have h2 : (a + 1) + c = (a + c) + 1 := by abel
      have h3 : (a + 1) + c = b + c := h2.trans heq.symm
      exact (add_right_cancel h3).symm
    · refine ⟨fun h => hne (by rw [h]), Or.inr ?_⟩
      -- heq : a + c = (b + c) + 1; want: a = b + 1
      have h2 : (b + 1) + c = (b + c) + 1 := by abel
      have h3 : (b + 1) + c = a + c := h2.trans heq.symm
      exact (add_right_cancel h3).symm

/-- The rotation `k ↦ k + c` as a graph homomorphism. -/
def cycleRotHom {n : Nat} [NeZero n] (hn : 2 ≤ n) (c : Fin n) :
    (cycleHypergraph n).toSimpleGraph →g (cycleHypergraph n).toSimpleGraph where
  toFun k := k + c
  map_rel' hab :=
    (cycleHypergraph_Adj_translation hn c _ _).mp hab

/-- `dist v w = dist (v + c) (w + c)` in `cycleHypergraph n`, for
`n ≥ 2`. -/
theorem cycleHypergraph_dist_translation {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (c v w : Fin n) :
    (cycleHypergraph n).dist v w =
      (cycleHypergraph n).dist (v + c) (w + c) := by
  unfold Hypergraph.dist
  apply le_antisymm
  · -- dist v w ≤ dist (v+c) (w+c) via Walk.map with σ⁻¹ = (· + (-c))
    have hconn := cycleHypergraph_connected hn
    have hreach : (cycleHypergraph n).toSimpleGraph.Reachable (v + c) (w + c) :=
      hconn (v + c) (w + c)
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    have hvc : (cycleRotHom hn (-c)) (v + c) = v := by
      show (v + c) + (-c) = v; abel
    have hwc : (cycleRotHom hn (-c)) (w + c) = w := by
      show (w + c) + (-c) = w; abel
    let q : (cycleHypergraph n).toSimpleGraph.Walk v w :=
      (p.map (cycleRotHom hn (-c))).copy hvc hwc
    calc (cycleHypergraph n).toSimpleGraph.dist v w
        ≤ q.length := SimpleGraph.dist_le q
      _ = (p.map (cycleRotHom hn (-c))).length := by
          simp [q, SimpleGraph.Walk.length_copy]
      _ = p.length := p.length_map _
      _ = (cycleHypergraph n).toSimpleGraph.dist (v + c) (w + c) := hp
  · -- dist (v+c) (w+c) ≤ dist v w via Walk.map with σ = (· + c)
    have hconn := cycleHypergraph_connected hn
    have hreach : (cycleHypergraph n).toSimpleGraph.Reachable v w := hconn v w
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    calc (cycleHypergraph n).toSimpleGraph.dist (v + c) (w + c)
        ≤ (p.map (cycleRotHom hn c)).length := SimpleGraph.dist_le _
      _ = p.length := p.length_map _
      _ = (cycleHypergraph n).toSimpleGraph.dist v w := hp

/-- For `n ≥ 2`, `cycleHypergraph n` is ball-volume uniform. -/
theorem cycleHypergraph_ballVolumeVertexUniform {n : Nat} [NeZero n]
    (hn : 2 ≤ n) :
    (cycleHypergraph n).BallVolumeVertexUniform := by
  intro r v w
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  -- The shift σ : u ↦ u + (w - v) bijects the two ball sets.
  let c : Fin n := w - v
  have hc : v + c = w := by simp [c]
  refine Finset.card_bij (fun u _ => u + c) ?_ ?_ ?_
  · -- Membership preservation: dist v u ≤ r → dist w (u + c) ≤ r
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    have := cycleHypergraph_dist_translation hn c v u
    rw [hc] at this
    omega
  · -- Injectivity
    intros u _ u' _ h
    exact add_right_cancel h
  · -- Surjectivity: every u' in the second ball has a preimage
    intro u' hu'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
    refine ⟨u' - c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := cycleHypergraph_dist_translation hn c v (u' - c)
      have hc' : (u' - c) + c = u' := by abel
      rw [hc, hc'] at this
      omega
    · abel

/-- For `n ≥ 2`, `cycleHypergraph n` is local-dimension uniform. -/
theorem cycleHypergraph_localDimensionVertexUniform {n : Nat} [NeZero n]
    (hn : 2 ≤ n) :
    (cycleHypergraph n).LocalDimensionVertexUniform :=
  ballVolumeVertexUniform_implies_localDimensionVertexUniform _
    (cycleHypergraph_ballVolumeVertexUniform hn)

/-- For `n ≥ 2`, `cycleHypergraph n` is distance-transitive, with
`σ = (· + (w − v))`. -/
theorem cycleHypergraph_distTransitive {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (cycleHypergraph n).DistTransitive := by
  intro v w
  refine ⟨Equiv.addRight (w - v), ?_, ?_⟩
  · show v + (w - v) = w; abel
  · intro a
    have := cycleHypergraph_dist_translation hn (w - v) v a
    have hw : v + (w - v) = w := by abel
    rw [hw] at this
    exact this

/-- For `n ≥ 2`, `cycleHypergraph n` is adjacency-transitive, with
`σ = (· + (w − v))`. -/
theorem cycleHypergraph_adjTransitive {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (cycleHypergraph n).AdjTransitive := by
  intro v w
  refine ⟨Equiv.addRight (w - v), ?_, ?_⟩
  · show v + (w - v) = w; abel
  · intro a b
    exact cycleHypergraph_Adj_translation hn (w - v) a b

/-- For `n ≥ 2`, `cycleHypergraph n` is adjacency-transitive,
distance-transitive, ball-volume uniform and local-dimension uniform. -/
theorem cycleHypergraph_rodkey_chain {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (cycleHypergraph n).AdjTransitive ∧
    (cycleHypergraph n).DistTransitive ∧
    (cycleHypergraph n).BallVolumeVertexUniform ∧
    (cycleHypergraph n).LocalDimensionVertexUniform :=
  ⟨cycleHypergraph_adjTransitive hn,
   cycleHypergraph_distTransitive hn,
   cycleHypergraph_ballVolumeVertexUniform hn,
   cycleHypergraph_localDimensionVertexUniform hn⟩

/-! ## `pathHypergraph n` -/

/-- For `n ≥ 3`, `pathHypergraph n` is not ball-volume uniform: vertex 0
has degree 1 and vertex 1 has degree 2. -/
theorem pathHypergraph_not_ballVolumeVertexUniform {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) :
    ¬ (pathHypergraph n).BallVolumeVertexUniform := by
  apply not_ballVolumeVertexUniform_of_degree_ne
    (pathHypergraph n) pathHypergraph_connected
    (v := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) (w := ⟨1, by omega⟩)
  rw [pathHypergraph_degree_zero (by omega),
      pathHypergraph_degree_one hn]
  omega

/-- On `Fin 3` there is a ball-volume uniform hypergraph
(`cycleHypergraph 3`) and one that is not (`pathHypergraph 3`). -/
theorem rodkey_classification_nontrivial :
    ∃ (H : Hypergraph (Fin 3)) (K : Hypergraph (Fin 3)),
      H.BallVolumeVertexUniform ∧ ¬ K.BallVolumeVertexUniform := by
  refine ⟨cycleHypergraph 3, pathHypergraph 3, ?_, ?_⟩
  · exact cycleHypergraph_ballVolumeVertexUniform (by omega)
  · exact pathHypergraph_not_ballVolumeVertexUniform (by omega)

/-! ## The implication between the two uniformity predicates -/

/-- For `n ≥ 3`, on `Fin n` there is a ball-volume uniform hypergraph
(`cycleHypergraph n`) and one that is not (`pathHypergraph n`). -/
theorem rodkey_classification_nontrivial_for_Fin {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) :
    ∃ (H : Hypergraph (Fin n)) (K : Hypergraph (Fin n)),
      H.BallVolumeVertexUniform ∧ ¬ K.BallVolumeVertexUniform :=
  ⟨cycleHypergraph n, pathHypergraph n,
   cycleHypergraph_ballVolumeVertexUniform (by omega),
   pathHypergraph_not_ballVolumeVertexUniform hn⟩

/-- For `n ≥ 3`, on `Fin n` there is a regular hypergraph and one that is
not regular. -/
theorem regular_dichotomy_for_Fin {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ (H : Hypergraph (Fin n)) (K : Hypergraph (Fin n)),
      H.Regular ∧ ¬ K.Regular :=
  ⟨cycleHypergraph n, pathHypergraph n,
   cycleHypergraph_regular hn,
   pathHypergraph_not_regular hn⟩

/-- For `n ≥ 2`, `cycleHypergraph n` satisfies
`BallVolumeVertexUniformRestricted`. -/
theorem cycleHypergraph_ballVolumeVertexUniformRestricted
    {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (cycleHypergraph n).BallVolumeVertexUniformRestricted := by
  have hconn := cycleHypergraph_connected hn
  exact (ballVolumeVertexUniform_iff_restricted (cycleHypergraph n) hconn).mp
    (cycleHypergraph_ballVolumeVertexUniform hn)

/-- For `n ≥ 3`, `pathHypergraph n` does not satisfy
`BallVolumeVertexUniformRestricted`. -/
theorem pathHypergraph_not_ballVolumeVertexUniformRestricted
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ¬ (pathHypergraph n).BallVolumeVertexUniformRestricted := by
  intro hres
  apply pathHypergraph_not_ballVolumeVertexUniform hn
  have hconn := pathHypergraph_connected (n := n)
  exact (ballVolumeVertexUniform_iff_restricted (pathHypergraph n) hconn).mpr hres

end Hypergraph
end InfraFormalization
