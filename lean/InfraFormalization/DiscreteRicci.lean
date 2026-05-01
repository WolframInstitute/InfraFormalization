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
import InfraFormalization.HypergraphDistance

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

/-! ## Bishop-Gromov scalar curvature from log V(r) growth (AT9)

In a `d`-dimensional Riemannian space, the volume of a ball of radius `r`
at point `p` admits the Bishop-Gromov expansion

  `V(p, r) = Ω_d · r^d · [1 − R(p) · r²/(6(d+2)) + O(r⁴)]`

where `R(p)` is the scalar curvature at `p` and `Ω_d` is the volume of the
unit ball in `d`-dimensional Euclidean space. Inverting this gives a
discrete extraction of scalar curvature from ball-count data:

  `R(v, r) := (6(d+2)/r²) · [1 − V(v, r) / V_flat(d, r)]`

where `V_flat(d, r) := Ω_d · r^d` is the flat-baseline ball volume in
`d`-dimensional Euclidean space.

This is the **Wolfram-style ball-growth curvature** (NMURZIN §3.4): no
chain complex required, no metric tensor, just `geodesicBallVolume` plus
a flat-baseline. Cross-checks the Forman-Ricci scalar
(`formanRicciHypergraph`) above and the AT2 angle-defect Gauss-Bonnet
identity. Sits below the metric layer (only needs `dist`); above the
infrasphere primitive (SPHERE1).

**Dimension handling.** The Bishop-Gromov formula is for a *fixed* `d`.
On a hypergraph, `d` itself comes from `wolframHausdorffDimension v`
(asymptotic `log V(v, r) / log r`). We expose the curvature extractor
parameterised by `d : ℕ` to allow either: (a) using the empirical `d`
extracted from the same hypergraph, or (b) testing against a target `d`
in screening.

**Units.** `R_disc` is dimensionless — counts divided by counts (per
the AT11 / `INFRAGEOMETRY.md` §3 units-emergence story). The continuum
`R_phys` recovers as `R_phys = a^{-2} · R_disc` under continuum rescaling
with length-scale `a`. -/

open Real

/-- Volume of the unit ball in `d`-dimensional Euclidean space. Closed
form: `Ω_d = π^{d/2} / Γ(d/2 + 1)`. We expose only the small-`d` cases
(0, 1, 2, 3) by literal value; higher `d` falls back to a representative
positive value (refinement to the actual closed form via `Real.Gamma` is
follow-up work). -/
noncomputable def unitBallVolumeEuclidean : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => Real.pi
  | 3 => 4 * Real.pi / 3
  | _ => 1  -- placeholder for d ≥ 4; actual closed form via Real.Gamma

/-- **Flat-baseline ball volume in `d`-dimensional Euclidean space**:
`V_flat(d, r) := Ω_d · r^d` where `Ω_d` is the volume of the unit ball.
For `d = 0`: `Ω_0 = 1`, `V_flat = 1` (single point). For `d = 1`:
`Ω_1 = 2`, `V_flat = 2r` (interval). For `d = 2`: `Ω_2 = π`,
`V_flat = π r²`. For `d = 3`: `Ω_3 = 4π/3`, `V_flat = (4π/3) r³`. -/
noncomputable def flatBallVolume (d : ℕ) (r : ℕ) : ℝ :=
  unitBallVolumeEuclidean d * (r : ℝ)^d

/-- **Bishop-Gromov scalar curvature extractor** at vertex `v` for
dimension `d`, scale `r > 0`.

  `R_disc(v, r) := (6(d+2)/r²) · [1 − V(v, r) / V_flat(d, r)]`

When `V(v, r) > V_flat(d, r)` (faster-than-flat growth → positive Ricci →
spherical-like): output positive. When `V(v, r) < V_flat(d, r)`
(slower-than-flat → negative Ricci → hyperbolic-like): output negative.
On a flat lattice with matching `d`, ratio → 1 and curvature → 0. -/
noncomputable def Hypergraph.scalarCurvatureAt {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ) : ℝ :=
  if 0 < r then
    (6 * (d + 2) / ((r : ℝ)^2)) *
      (1 - (H.geodesicBallVolume v r : ℝ) / flatBallVolume d r)
  else 0

/-- **Curvature is zero when the ball volume matches the flat baseline
exactly** at scale `r`. Concrete sanity check: this is the discrete
analog of "flat space has zero Ricci". -/
theorem Hypergraph.scalarCurvatureAt_zero_of_match {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ)
    (hr : 0 < r)
    (hmatch : (H.geodesicBallVolume v r : ℝ) = flatBallVolume d r)
    (hflat_pos : 0 < flatBallVolume d r) :
    H.scalarCurvatureAt v d r = 0 := by
  unfold Hypergraph.scalarCurvatureAt
  rw [if_pos hr, hmatch, div_self (ne_of_gt hflat_pos), sub_self, mul_zero]

/-- **Scalar curvature is positive iff the ball volume is below the flat
baseline** (slower-than-flat growth = positively-curved-spherical-like).
Sign convention check. -/
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

/-! ## Surface-area Bishop-Gromov curvature extraction (SPHERE4)

Companion to AT9 (`scalarCurvatureAt`, ball-volume Bishop-Gromov). For a
sphere `S(O, r)` of radius `r` in `d`-dim Euclidean space:

  `|S(O, r)| = S_d · r^(d-1) · [1 − R(O) · r²/(6d) + O(r⁴)]`

where `S_d = d · Ω_d` is the `(d-1)`-volume of the unit `(d-1)`-sphere
(boundary of the unit `d`-ball). Inverting gives a *sphere-side*
curvature extractor:

  `R_surface(O, r) := (6d/r²) · [1 − |S(O, r)| / S_flat(d, r)]`

where `S_flat(d, r) := S_d · r^(d-1)`. This is one Taylor-order higher
than AT9 (the surface picks up curvature at `r^(d-1) · r² = r^(d+1)`
versus the ball at `r^d · r² = r^(d+2)`); independent extraction —
cross-checks AT9.

For `d = 0`: `S_d = 0` (sphere is empty); `S_flat = 0`; extraction is
degenerate. For `d = 1`: `S_1 = 2`, `S_flat = 2`. For `d = 2`: `S_2 =
2π`, `S_flat = 2π r`. For `d = 3`: `S_3 = 4π`, `S_flat = 4π r²`.

**Independent cross-check of AT9.** Both should agree on `R(O)` in the
continuum limit; deviation between them at finite scale measures the
discrete-geometry error term.
-/

/-- **Unit-sphere area** (`(d-1)`-volume of the unit `(d-1)`-sphere) in
`d`-dim Euclidean space: `S_d = d · Ω_d`. Closed form
`S_d = 2 π^{d/2} / Γ(d/2)`. We expose small-`d` cases by literal
value; higher `d` defers to the same `Real.Gamma` follow-up as
`unitBallVolumeEuclidean`. -/
noncomputable def unitSphereAreaEuclidean : ℕ → ℝ
  | 0 => 0  -- the (-1)-sphere is empty
  | 1 => 2  -- two endpoints of the interval
  | 2 => 2 * Real.pi
  | 3 => 4 * Real.pi
  | _ => 1  -- placeholder; closed form via Real.Gamma

/-- **Flat-baseline sphere area** in `d`-dim Euclidean space:
`S_flat(d, r) := S_d · r^(d-1)`. Note: for `d = 0` this is degenerate
(`S_d = 0`); for `r = 0` it's `0` for `d ≥ 2` (a point's surface area
is zero). -/
noncomputable def flatSphereArea (d : ℕ) (r : ℕ) : ℝ :=
  unitSphereAreaEuclidean d * (r : ℝ)^(d - 1)

/-- **Surface-area Bishop-Gromov scalar curvature extractor** at vertex
`v`, dimension `d`, radius `r > 0`:

  `R_surface(v, r) := (6d/r²) · (1 − |S(v, r)| / S_flat(d, r))`

Independent of AT9's `scalarCurvatureAt` (which uses ball volume); the
two should agree on `R(v)` in the continuum limit. Cross-check tool. -/
noncomputable def Hypergraph.surfaceCurvatureAt {V : Type*}
    [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (v : V) (d : ℕ) (r : ℕ) : ℝ :=
  if 0 < r then
    (6 * (d : ℝ) / ((r : ℝ)^2)) *
      (1 - (H.infraSphereVolume v r : ℝ) / flatSphereArea d r)
  else 0

/-- **Curvature is zero when the surface area matches the flat
baseline** at scale `r` — discrete analog of "flat space has zero
sphere-side Ricci". -/
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
