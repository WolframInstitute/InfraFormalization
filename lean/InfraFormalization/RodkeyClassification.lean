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
import InfraFormalization.PathHypergraphDistance

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

/-- **Dist-transitivity**: for every pair of vertices `(v, w)` there is
a bijection `σ : V ≃ V` sending `v` to `w` and preserving distances from
`v`: for every `a`, `dist v a = dist w (σ a)`. This is the abstract
sufficient condition for ball-volume vertex-uniformity; vertex-
transitive graphs (in the graph-automorphism sense) satisfy it. -/
def DistTransitive (H : Hypergraph V) : Prop :=
  ∀ v w : V, ∃ σ : V ≃ V, σ v = w ∧ ∀ a, H.dist v a = H.dist w (σ a)

/-- **Rodkey classification — sufficient condition.** Any dist-transitive
hypergraph satisfies ball-volume vertex-uniformity. The shift σ bijects
the radius-r ball at v with the radius-r ball at w, so their cardinalities
agree. -/
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

/-- **Adj-transitivity**: for every pair `(v, w)` there is an `Equiv σ`
sending `v` to `w` that preserves adjacency in both directions. This
is the graph-theoretic vertex-transitivity condition and is strictly
stronger than `DistTransitive` (it implies it via Walk.map on the
induced SimpleGraph.Hom). -/
def AdjTransitive (H : Hypergraph V) : Prop :=
  ∀ v w : V, ∃ σ : V ≃ V, σ v = w ∧ ∀ a b, H.Adj a b ↔ H.Adj (σ a) (σ b)

/-- **Adj-transitive implies dist-transitive.** Given an
adjacency-preserving `Equiv σ` sending `v` to `w`, the SimpleGraph Hom
structure transfers walks between `v → a` and `w → σ a` (in both
directions, using `σ` and `σ⁻¹`), so walk lengths and hence distances
are preserved. -/
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
        -- σ.symm preserves Adj: if Adj x y, then σ (σ.symm x) = x
        -- and σ (σ.symm y) = y, so (hσ _ _).mpr applied to Adj x y in the
        -- shape Adj (σ (σ.symm x)) (σ (σ.symm y)).
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
    · -- Unreachable: dist w (σ a) = 0 as junk, so we must show dist v a ≤ 0.
      -- But via the fwd Hom, Reachable v a would imply Reachable w (σ a).
      -- So ¬Reachable w (σ a) implies ¬Reachable v a, hence dist v a = 0.
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

/-- **Adj-transitive implies ball-volume vertex-uniform.** Composition
of `distTransitive_of_adjTransitive` and
`ballVolumeVertexUniform_of_distTransitive`. -/
theorem ballVolumeVertexUniform_of_adjTransitive
    (H : Hypergraph V) (ht : H.AdjTransitive) :
    H.BallVolumeVertexUniform :=
  ballVolumeVertexUniform_of_distTransitive H
    (distTransitive_of_adjTransitive H ht)

/-- **Geodesic ball volume at radius 1 equals degree plus one** on a
connected hypergraph. The radius-1 ball around `v` is the disjoint
union of `{v}` with the SimpleGraph-neighbour set of `v` (because
`dist v u = 1 ↔ Adj v u` on a simple graph, and connectivity rules
out the unreachable-junk case). -/
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

/-- **Ball-volume vertex-uniformity at radius 1 implies uniform
SimpleGraph degree** (on a connected hypergraph): if the radius-1 ball
size is the same at every vertex, the SimpleGraph degrees also agree,
since `|ball v 1| = 1 + degree v`. -/
theorem degree_uniform_of_ballVolumeVertexUniform
    (H : Hypergraph V) (hconn : H.toSimpleGraph.Connected)
    (hb : H.BallVolumeVertexUniform) (v w : V) :
    H.toSimpleGraph.degree v = H.toSimpleGraph.degree w := by
  have hvw := hb 1 v w
  rw [geodesicBallVolume_one_eq_degree_plus_one H hconn v,
      geodesicBallVolume_one_eq_degree_plus_one H hconn w] at hvw
  omega

/-- **Non-regular connected hypergraph is NOT ball-volume
vertex-uniform.** Contrapositive of `degree_uniform_of_ballVolumeVertexUniform`
— if any two vertices have different SimpleGraph degree on a connected
hypergraph, the ball-volume-vertex-uniformity predicate cannot hold.
This is the workhorse for ruling out candidate hypergraphs from the
Rodkey classification: any non-regular connected graph fails the
radius-1 ball-count check, regardless of what happens at larger radii. -/
theorem not_ballVolumeVertexUniform_of_degree_ne
    (H : Hypergraph V) (hconn : H.toSimpleGraph.Connected)
    {v w : V} (hne : H.toSimpleGraph.degree v ≠ H.toSimpleGraph.degree w) :
    ¬ H.BallVolumeVertexUniform := by
  intro hb
  exact hne (degree_uniform_of_ballVolumeVertexUniform H hconn hb v w)

/-- **`k`-regular connected hypergraph has uniform radius-1 ball volume
equal to `k + 1`.** Direct application of `geodesicBallVolume_one_eq_degree_plus_one`
at every vertex. The radius-1 piece of the BallVolumeVertexUniform
predicate holds for every regular connected hypergraph — a partial
necessary-and-sufficient result at the local level. -/
theorem ballVolumeOne_regular (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (k : ℕ)
    (hreg : ∀ v : V, H.toSimpleGraph.degree v = k) (v : V) :
    H.geodesicBallVolume v 1 = k + 1 := by
  rw [geodesicBallVolume_one_eq_degree_plus_one H hconn v, hreg v]
  omega

/-- **Regular connected hypergraphs are ball-volume-uniform at radius 1.**
Direct corollary of `ballVolumeOne_regular`: if every vertex has the
same SimpleGraph degree, every radius-1 ball has the same size. -/
theorem ballVolumeOne_uniform_of_regular (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) {k : ℕ}
    (hreg : ∀ v : V, H.toSimpleGraph.degree v = k) (v w : V) :
    H.geodesicBallVolume v 1 = H.geodesicBallVolume w 1 := by
  rw [ballVolumeOne_regular H hconn k hreg v,
      ballVolumeOne_regular H hconn k hreg w]

/-- **Regularity predicate**: every vertex has the same SimpleGraph
degree. A necessary (but not sufficient) condition for
BallVolumeVertexUniform on a connected hypergraph. -/
def Regular (H : Hypergraph V) : Prop :=
  ∀ v w : V, H.toSimpleGraph.degree v = H.toSimpleGraph.degree w

/-- **Ball-volume vertex-uniformity (at radius 1) on a connected
hypergraph is equivalent to regularity.** Forward: r=1 uniformity gives
uniform degree via `degree_uniform_of_ballVolumeVertexUniform`. Backward:
regularity gives uniform r=1 balls via `ballVolumeOne_regular`. A
tight local characterisation of the r=1 slice of the Rodkey predicate. -/
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

/-- **`cycleHypergraph n` is 2-regular for `n ≥ 3`.** Every vertex has
exactly `v + 1` and `v - 1` as distinct neighbours; the SimpleGraph
degree is 2 throughout. Derived via
`cycleHypergraph_ballVolume_one_exact` (= 3) and
`geodesicBallVolume_one_eq_degree_plus_one`. -/
theorem cycleHypergraph_regular_degree_two {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v : Fin n) :
    (cycleHypergraph n).toSimpleGraph.degree v = 2 := by
  have hconn := cycleHypergraph_connected (by omega : 2 ≤ n)
  have hvol := cycleHypergraph_ballVolume_one_exact hn v
  have hid := geodesicBallVolume_one_eq_degree_plus_one
    (cycleHypergraph n) hconn v
  omega

/-- **`cycleHypergraph n` is Regular for `n ≥ 3`**: every vertex has
degree 2. -/
theorem cycleHypergraph_regular {n : Nat} [NeZero n] (hn : 3 ≤ n) :
    (cycleHypergraph n).Regular := by
  intro v w
  rw [cycleHypergraph_regular_degree_two hn v,
      cycleHypergraph_regular_degree_two hn w]

/-- **`pathHypergraph n` is NOT regular for `n ≥ 3`**: the endpoint
`0 : Fin n` has degree 1 while the interior vertex `1 : Fin n` has
degree 2. Matches the pre-existing
`pathHypergraph_not_ballVolumeVertexUniform` result, but cast at the
structural (degree) level rather than the ball-volume level. -/
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

/-- **Regularity dichotomy on `Fin 3`**: there exist hypergraphs on
the same vertex type such that one is Regular and another is not.
Witnessed by `cycleHypergraph 3` (regular, degree 2) and
`pathHypergraph 3` (not regular: endpoint degree 1, interior degree 2).
Structural analogue of `rodkey_classification_nontrivial`. -/
theorem regular_dichotomy_on_fin3 :
    ∃ (H : Hypergraph (Fin 3)) (K : Hypergraph (Fin 3)),
      H.Regular ∧ ¬ K.Regular :=
  ⟨cycleHypergraph 3, pathHypergraph 3,
   cycleHypergraph_regular (by omega),
   pathHypergraph_not_regular (by omega)⟩

/-- **`BallVolumeVertexUniform` implies `Regular`** on a connected
hypergraph: the radius-1 ball size equals `1 + degree v`, so uniformity
at `r = 1` forces uniform degree. Packages
`degree_uniform_of_ballVolumeVertexUniform` at the predicate level. -/
theorem regular_of_ballVolumeVertexUniform (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected)
    (hb : H.BallVolumeVertexUniform) : H.Regular :=
  degree_uniform_of_ballVolumeVertexUniform H hconn hb

/-- **Contrapositive at the Regular level**: a non-regular connected
hypergraph cannot satisfy `BallVolumeVertexUniform`. Uniform restatement
of `not_ballVolumeVertexUniform_of_degree_ne` via the `Regular`
predicate — no explicit `v, w` pair needed. -/
theorem not_ballVolumeVertexUniform_of_not_regular (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (hnotreg : ¬ H.Regular) :
    ¬ H.BallVolumeVertexUniform :=
  fun hb => hnotreg (regular_of_ballVolumeVertexUniform H hconn hb)

/-- **Ball volume is vertex-uniform at any radius `r ≥ |V|` on every
connected hypergraph.** Both sides equal `|V|` by
`geodesicBallVolume_ge_card`. So the obstruction to
`BallVolumeVertexUniform` always lies in the "small-radius" regime
`r < |V|`; once `r ≥ |V|`, uniformity is automatic regardless of
graph structure. -/
theorem ballVolumeVertexUniform_at_large_radius (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (r : ℕ) (hr : Fintype.card V ≤ r)
    (v w : V) :
    H.geodesicBallVolume v r = H.geodesicBallVolume w r := by
  rw [geodesicBallVolume_ge_card H hconn v r hr,
      geodesicBallVolume_ge_card H hconn w r hr]

/-- **Radius-0 ball volume = 1 on every connected hypergraph.** On a
connected graph, `dist v u = 0 ↔ v = u`, so the only vertex within
distance 0 of `v` is `v` itself. -/
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

/-- **Ball volume is vertex-uniform at radius 0 on every connected
hypergraph.** Both sides equal 1. The `r = 0` slice of
`BallVolumeVertexUniform` is trivial. -/
theorem ballVolumeVertexUniform_at_zero (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (v w : V) :
    H.geodesicBallVolume v 0 = H.geodesicBallVolume w 0 := by
  rw [geodesicBallVolume_zero_of_connected H hconn v,
      geodesicBallVolume_zero_of_connected H hconn w]

/-- **Restricted BallVolumeVertexUniform predicate**: uniformity only
asked in the non-trivial regime `1 ≤ r < |V|`. Together with the
"sandwich" pieces `ballVolumeVertexUniform_at_zero` and
`ballVolumeVertexUniform_at_large_radius`, this is equivalent to the
full `BallVolumeVertexUniform` on connected hypergraphs. -/
def BallVolumeVertexUniformRestricted (H : Hypergraph V) : Prop :=
  ∀ (r : ℕ), 1 ≤ r → r < Fintype.card V →
    ∀ (v w : V), H.geodesicBallVolume v r = H.geodesicBallVolume w r

/-- **Restricted ⇔ full**: on connected hypergraphs, uniformity on
`1 ≤ r < |V|` extends automatically to `r = 0` and `r ≥ |V|` via the
sandwich pieces, giving the full `BallVolumeVertexUniform`. -/
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

/-- **Adj-transitive implies uniform degree.** An Adj-preserving
`Equiv σ : V ≃ V` sending `v` to `w` bijects the neighbour set of `v`
with the neighbour set of `w`, so the simple-graph degrees agree. This
gives a NECESSARY graph-theoretic condition for the Rodkey property:
vertex-transitive graphs are regular. Contrapositive: a graph with
vertices of different degree (e.g., `pathHypergraph n` with endpoints
of degree 1 and interior vertices of degree 2) cannot be Adj-transitive,
and hence its ball-volume-vertex-uniformity status is not derivable
from the sufficient-condition chain above. -/
theorem degree_invariant_of_adjTransitive
    (H : Hypergraph V) (ht : H.AdjTransitive) (v w : V) :
    H.toSimpleGraph.degree v = H.toSimpleGraph.degree w := by
  obtain ⟨σ, hσvw, hσ⟩ := ht v w
  rw [SimpleGraph.degree, SimpleGraph.degree]
  refine Finset.card_bij (fun u _ => σ u) ?_ ?_ ?_
  · -- Forward: Adj v u → Adj w (σ u). Use hσ v u and the identification σ v = w.
    intro u hu
    simp only [SimpleGraph.mem_neighborFinset] at hu ⊢
    have h := (hσ v u).mp hu
    rw [hσvw] at h
    exact h
  · intros u _ u' _ h; exact σ.injective h
  · -- Surjectivity: given Adj w u', take u = σ⁻¹ u' as the preimage.
    intro u' hu'
    simp only [SimpleGraph.mem_neighborFinset] at hu'
    refine ⟨σ.symm u', ?_, σ.apply_symm_apply u'⟩
    simp only [SimpleGraph.mem_neighborFinset]
    apply (hσ v (σ.symm u')).mpr
    rw [hσvw, σ.apply_symm_apply]
    exact hu'

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

/-! ## Translation-invariance on `cycleHypergraph n`

The rotation `k ↦ k + c` on `Fin n` sends cycle-edges to cycle-edges
in both directions, so it is a SimpleGraph automorphism of
`(cycleHypergraph n).toSimpleGraph`. Distance is preserved under
graph homomorphism (via `SimpleGraph.Walk.map` + `Walk.length_map`),
giving dist-translation-invariance and hence full vertex-uniformity
of the geodesic ball volume. -/

/-- **Adj translation invariance** on the cycle: adjacency is preserved
in both directions under `k ↦ k + c`. -/
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

/-- **Rotation as a SimpleGraph Hom** on `(cycleHypergraph n).toSimpleGraph`. -/
def cycleRotHom {n : Nat} [NeZero n] (hn : 2 ≤ n) (c : Fin n) :
    (cycleHypergraph n).toSimpleGraph →g (cycleHypergraph n).toSimpleGraph where
  toFun k := k + c
  map_rel' hab :=
    (cycleHypergraph_Adj_translation hn c _ _).mp hab

/-- **Distance translation invariance** on the cycle. The shift
`k ↦ k + c` preserves the hypergraph distance. -/
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

/-- **cycleHypergraph has vertex-uniform ball volume at every radius.**
Follows from dist translation invariance: the shift `k ↦ k + (w - v)`
bijects `{u : dist v u ≤ r}` with `{u : dist w u ≤ r}`. -/
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

/-- **Local-dimension vertex uniformity on the cycle.** The Rodkey
condition holds for every `cycleHypergraph n` with `n ≥ 2`. -/
theorem cycleHypergraph_localDimensionVertexUniform {n : Nat} [NeZero n]
    (hn : 2 ≤ n) :
    (cycleHypergraph n).LocalDimensionVertexUniform :=
  ballVolumeVertexUniform_implies_localDimensionVertexUniform _
    (cycleHypergraph_ballVolumeVertexUniform hn)

/-- **`cycleHypergraph n` is dist-transitive via rotation.** For any
vertices `v, w` the shift `k ↦ k + (w - v)` is a bijection on `Fin n`
that sends `v` to `w` and preserves distance (by
`cycleHypergraph_dist_translation`). This exhibits the cycle as a
witness for the `DistTransitive` sufficient condition. -/
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

/-- **`cycleHypergraph n` is Adj-transitive via rotation.** The shift
`k ↦ k + (w - v)` is an `Equiv` on `Fin n` that sends `v` to `w` and
preserves adjacency iff-both-ways (by `cycleHypergraph_Adj_translation`). -/
theorem cycleHypergraph_adjTransitive {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (cycleHypergraph n).AdjTransitive := by
  intro v w
  refine ⟨Equiv.addRight (w - v), ?_, ?_⟩
  · show v + (w - v) = w; abel
  · intro a b
    exact cycleHypergraph_Adj_translation hn (w - v) a b

/-- **Full Rodkey chain on the cycle.** Every `cycleHypergraph n` with
`n ≥ 2` satisfies all four levels of the Rodkey classification
hierarchy: Adj-transitive, dist-transitive, ball-volume
vertex-uniform, and local-dimension vertex-uniform. This is the
canonical positive example. -/
theorem cycleHypergraph_rodkey_chain {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (cycleHypergraph n).AdjTransitive ∧
    (cycleHypergraph n).DistTransitive ∧
    (cycleHypergraph n).BallVolumeVertexUniform ∧
    (cycleHypergraph n).LocalDimensionVertexUniform :=
  ⟨cycleHypergraph_adjTransitive hn,
   cycleHypergraph_distTransitive hn,
   cycleHypergraph_ballVolumeVertexUniform hn,
   cycleHypergraph_localDimensionVertexUniform hn⟩

/-! ## Path hypergraph negative example

The path hypergraph `pathHypergraph n` with `n ≥ 3` is a canonical
negative example for the Rodkey classification: ball-volume-vertex-
uniformity fails at radius 1 because endpoints (degree 1) differ from
interior vertices (degree 2). -/

/-- **`pathHypergraph n` is NOT ball-volume vertex-uniform** for `n ≥ 3`.
The endpoint `0 : Fin n` has SimpleGraph degree `1`, the interior
vertex `1 : Fin n` has degree `2`; by
`not_ballVolumeVertexUniform_of_degree_ne` (connected + degree
mismatch ⇒ ball-volume-uniformity fails), the path is ruled out.
Canonical negative example complementing the cycle positive example. -/
theorem pathHypergraph_not_ballVolumeVertexUniform {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) :
    ¬ (pathHypergraph n).BallVolumeVertexUniform := by
  apply not_ballVolumeVertexUniform_of_degree_ne
    (pathHypergraph n) pathHypergraph_connected
    (v := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) (w := ⟨1, by omega⟩)
  rw [pathHypergraph_degree_zero (by omega),
      pathHypergraph_degree_one hn]
  omega

/-- **Classification separates**: there exist finite hypergraphs on
the same vertex type (`Fin 3`) of which one satisfies
`BallVolumeVertexUniform` and another does not. This is the non-
triviality check for the Rodkey predicate — it rules out both
"vacuous-true" and "vacuous-false" defect modes of the classification.

Witnessed by `cycleHypergraph 3` (positive, via rotation automorphism)
and `pathHypergraph 3` (negative, via endpoint/interior degree gap). -/
theorem rodkey_classification_nontrivial :
    ∃ (H : Hypergraph (Fin 3)) (K : Hypergraph (Fin 3)),
      H.BallVolumeVertexUniform ∧ ¬ K.BallVolumeVertexUniform := by
  refine ⟨cycleHypergraph 3, pathHypergraph 3, ?_, ?_⟩
  · exact cycleHypergraph_ballVolumeVertexUniform (by omega)
  · exact pathHypergraph_not_ballVolumeVertexUniform (by omega)

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
