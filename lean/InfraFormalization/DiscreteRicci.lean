/-
Discrete Ricci curvature on a graph (Forman variant) — the
hypergraph-side anchor for continuum Ricci.

**Why this file exists.** Per the grounding principle in
`BRIDGE_MACHINERY.md`, the continuum Ricci tensor in
`CurvatureLocalCoord.lean` / `CurvatureRiemann.lean` is acceptable
only as a *target* for a discrete-side construction grounded in
Wolfram physics. This file provides one such construction:
**Forman-Ricci curvature** on an edge of a finite graph.

**Definition (Forman 2003, edge form).** For a simple graph
`G = (V, E)` with vertex weights `w_v > 0` and edge weights
`w_e > 0`, the Forman-Ricci curvature of edge `e = {v, w}` is

  `Ric_F(e) := w_e · ( w_v / w_e + w_w / w_e
                       − ∑_{e' ~ v, e' ≠ e} w_v / √(w_e · w_e')
                       − ∑_{e' ~ w, e' ≠ e} w_w / √(w_e · w_e'))`.

For unit weights (`w_v = w_e = 1` everywhere) this collapses to:

  `Ric_F(e) = 2 − (deg(v) − 1) − (deg(w) − 1) = 4 − deg(v) − deg(w)`.

The unit-weight version is what we formalise here. It captures the
combinatorial Ricci: an edge has positive Forman-Ricci iff its
endpoints have low degree, negative if they have high degree.

**Connection to continuum Ricci.** On a regular lattice graph, the
unit-weight Forman-Ricci is constant per edge (since all degrees
equal `2d` for a d-dim cubic lattice). For a `Fin n` cycle with
adjacency `i ↔ i±1`, every vertex has degree 2, so `Ric_F(e) = 0` —
matching the continuum (the circle has zero Ricci curvature). This
is the first hypergraph→continuum-curvature consistency check we
can verify in Lean.

**Forman vs Ollivier.** Forman is purely combinatorial (no
Wasserstein computations); Ollivier (`Infra/OllivierStatement.lean`)
is more accurate but requires probability machinery. Forman is the
right starting anchor.

**Status.** Definition + cycle case (Ric_F ≡ 0) shipped here.
Convergence theorem (scaled Forman-Ricci → continuum Ricci on the
GH-limit manifold) is the next deliverable — see Rung 5 in
`BRIDGE_MACHINERY.md`.
-/

import InfraFormalization.DiscreteCalculus
import InfraFormalization.Hypergraph

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Unit-weight Forman-Ricci curvature on an edge** of a graph
described by a `Neighbourhood V`. For a (simple, undirected, unit-
weight) graph, this equals `4 − deg(v) − deg(w)` for an edge `(v, w)`. -/
def formanRicciEdge (N : Neighbourhood V) (v w : V) : ℤ :=
  4 - (N.degree v : ℤ) - (N.degree w : ℤ)

/-- Forman-Ricci is symmetric under swapping the edge endpoints. -/
theorem formanRicciEdge_symm (N : Neighbourhood V) (v w : V) :
    formanRicciEdge N v w = formanRicciEdge N w v := by
  unfold formanRicciEdge
  ring

/-- For a `2`-regular graph (every vertex has degree `2`), the
Forman-Ricci curvature on every edge is `0`. This matches the
continuum: a 1-dim manifold (e.g., circle) has zero Ricci. -/
theorem formanRicciEdge_zero_of_two_regular (N : Neighbourhood V)
    (h : ∀ v : V, N.degree v = 2) (v w : V) :
    formanRicciEdge N v w = 0 := by
  unfold formanRicciEdge
  rw [h v, h w]
  ring

/-- For a `k`-regular graph, the Forman-Ricci curvature on every edge
is `4 − 2k`. -/
theorem formanRicciEdge_regular (N : Neighbourhood V)
    (k : Nat) (h : ∀ v : V, N.degree v = k) (v w : V) :
    formanRicciEdge N v w = 4 - 2 * (k : ℤ) := by
  unfold formanRicciEdge
  rw [h v, h w]
  ring

/-- **Vertex-aggregated Forman-Ricci**: sum the edge curvatures
incident to a vertex. This is the analog of the Ricci tensor's trace
at a point. -/
def formanRicciVertex (N : Neighbourhood V) (v : V) : ℤ :=
  ∑ w ∈ N.nbhd v, formanRicciEdge N v w

/-- For a `k`-regular graph: vertex-aggregated Forman-Ricci is
`k · (4 − 2k) = 4k − 2k²`. -/
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

/-- **Total Forman-Ricci scalar curvature** of a graph: sum over all
vertex-aggregations. For a `k`-regular graph with `|V|` vertices:
`R_F = |V| · k · (4 − 2k)`. -/
def formanRicciTotalScalar (N : Neighbourhood V) : ℤ :=
  ∑ v : V, formanRicciVertex N v

/-- Total Forman-Ricci scalar of a `k`-regular graph. -/
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

/-! ## Forman-Ricci on hypergraphs

For a hyperedge `e = {v_1, …, v_k}` with `|e| ≥ 2`, define:

  `Ric_F(e) := |V(e)| · (2 − |V(e)|)`.

For `|e| = 2` (simple-graph edge): `2 · (2 − 2) = 0`.
For `|e| = 3`: `3 · (−1) = −3`.

This is the Saito–Kimura–Yamanoi variant. The hypergraph total is the
sum over all edges.
-/

/-- **Forman-Ricci per hyperedge**. -/
def formanRicciHyperedge (e : Hyperedge V) : ℤ :=
  let k := e.verts.toFinset.card
  (k : ℤ) * (2 - (k : ℤ))

/-- **Hyperedge Forman-Ricci vanishes for 2-vertex edges** (simple graph
case). -/
theorem formanRicciHyperedge_two_vertex (e : Hyperedge V)
    (h : e.verts.toFinset.card = 2) :
    formanRicciHyperedge e = 0 := by
  unfold formanRicciHyperedge
  rw [h]
  ring

/-- **Hyperedge Forman-Ricci is negative for ≥ 3-vertex edges**. -/
theorem formanRicciHyperedge_neg_of_three_or_more (e : Hyperedge V)
    (h : 3 ≤ e.verts.toFinset.card) :
    formanRicciHyperedge e < 0 := by
  unfold formanRicciHyperedge
  have hk : (3 : ℤ) ≤ (e.verts.toFinset.card : ℤ) := by exact_mod_cast h
  nlinarith

/-- **Hypergraph total Forman-Ricci scalar**: sum over all edges. -/
noncomputable def formanRicciHypergraph (H : Hypergraph V) : ℤ :=
  (H.edges.map formanRicciHyperedge).sum

/-- **Hypergraph Forman-Ricci vanishes on simple graphs**. -/
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

end InfraFormalization
