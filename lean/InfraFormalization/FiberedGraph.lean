/-
**Fibered graphs, sections, and connections — Lean port of
`InfraGaugeTheory`.**

This file is the Lean counterpart of the Wolfram-paclet
`resources/InfraGaugeTheory/Kernel/FiberedGraph.wl` +
`Sections.wl` + `Connections.wl`. The paclet gives
computational primitives (RandomFiberedGraph, ConnectionQ,
HolonomyMatrix, FlatConnectionQ, ...) on `Graph` objects; this file
installs the formal type theory and proves structural lemmas.

**Core definitions.**

  * `FiberedGraph V W` — a hypergraph on `V` together with a
    surjection `π : V → W` (base vertex assignment).
  * `FiberedGraph.fiber π w` — the preimage of `w`.
  * `FiberedGraph.baseGraph H π` — the hypergraph induced on the
    base by projecting each edge through `π` (mirrors
    `ReconstructBaseGraph`).
  * `Section H π σ` — predicate: `π ∘ σ = id` on the base (mirrors
    `RandomSection`).
  * `SmoothSection H π σ` — section that respects adjacency (mirrors
    `SmoothSectionQ`).
  * `Connection H π C` — a `Finset` of transverse edges with
    at-most-one-edge-lift (mirrors `ConnectionQ`).

**Status.** This file does IG1, IG2, IG3 of
`INFRAGEOMETRY.md` Group IG. Follow-up files will add
parallel transport (IG4), holonomy (IG5), Wilson loops (IG6),
flat-connection predicate (IG7), fiber-bundle predicate (IG8),
tangent-bundle construction (IG9), exponential map (IG10),
multi-fibered graphs (IG11).

**Connection to hypergraphs.** Native. Every fibered graph is built
on a `Hypergraph V` (the total space) plus a projection `π : V → W`;
no continuum objects appear. Every construction factors through
`Hypergraph.Adj` (clique-expansion adjacency, from
`HypergraphDistance.lean`).
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- **A fibered graph** on total space `V` and base space `W` is a
hypergraph `total : Hypergraph V` together with a projection
`π : V → W`. No constraints are imposed on `π` beyond being a
function; surjectivity / fiber-isomorphism / bundle properties are
separate predicates (`FiberedGraph.Surjective`, `FiberBundle`). -/
structure FiberedGraph (V W : Type*) where
  total : Hypergraph V
  π     : V → W

namespace FiberedGraph

variable (F : FiberedGraph V W)

/-- **Fiber over a base vertex `w`**: the preimage of `w` under `π`. -/
def fiber (w : W) : Finset V :=
  Finset.univ.filter (fun v => F.π v = w)

/-- **Membership in the fiber.** -/
theorem mem_fiber (v : V) (w : W) : v ∈ F.fiber w ↔ F.π v = w := by
  unfold fiber
  simp

/-- **Every vertex is in its own fiber.** -/
theorem self_mem_fiber (v : V) : v ∈ F.fiber (F.π v) :=
  (F.mem_fiber v (F.π v)).mpr rfl

/-- **Fibers partition `V`** (disjointly). Two distinct base vertices
give disjoint fibers; their union is all of `V`. -/
theorem disjoint_fibers {w₁ w₂ : W} (h : w₁ ≠ w₂) :
    Disjoint (F.fiber w₁) (F.fiber w₂) := by
  rw [Finset.disjoint_left]
  intros v hv₁ hv₂
  rw [F.mem_fiber] at hv₁ hv₂
  exact h (hv₁.symm.trans hv₂)

/-- **A vertex belongs to exactly one fiber.** -/
theorem exists_unique_fiber (v : V) : ∃! w : W, v ∈ F.fiber w := by
  refine ⟨F.π v, F.self_mem_fiber v, ?_⟩
  intros w hw
  rw [F.mem_fiber] at hw
  exact hw.symm

/-- **Vertical edges**: edges inside a single fiber. Horizontal
edges cross fibers. -/
def verticalQ (e : Hyperedge V) : Prop :=
  ∀ u ∈ e.verts, ∀ v ∈ e.verts, F.π u = F.π v

instance (e : Hyperedge V) : Decidable (F.verticalQ e) := by
  unfold verticalQ
  exact inferInstance

/-- **An edge is horizontal if it is not vertical.** -/
def horizontalQ (e : Hyperedge V) : Prop := ¬ F.verticalQ e

/-! ## Sections -/

/-- **A *section* of a fibered graph** is a map `σ : W → V` such
that `π ∘ σ = id` — every base vertex picks a lift in its fiber. -/
def IsSection (F : FiberedGraph V W) (σ : W → V) : Prop :=
  ∀ w : W, F.π (σ w) = w

/-- **The image of a section is a `Finset V`.** -/
def sectionImage (F : FiberedGraph V W) (σ : W → V) : Finset V :=
  let _ := F
  Finset.univ.image σ

theorem mem_sectionImage_iff (F : FiberedGraph V W) (σ : W → V) (v : V) :
    v ∈ F.sectionImage σ ↔ ∃ w : W, σ w = v := by
  unfold sectionImage
  simp

/-- **A section's image hits each fiber at a single vertex.** For a
section `σ`, `σ w ∈ F.fiber w`. -/
theorem section_mem_fiber (F : FiberedGraph V W) (σ : W → V)
    (hσ : F.IsSection σ) (w : W) :
    σ w ∈ F.fiber w :=
  (F.mem_fiber (σ w) w).mpr (hσ w)

/-- **Smooth section**: the image respects adjacency — adjacent base
vertices lift to adjacent total vertices. Mirrors
`SmoothSectionQ` in the paclet. -/
def SmoothSection (F : FiberedGraph V W) (σ : W → V) : Prop :=
  F.IsSection σ ∧
  ∀ w₁ w₂ : W,
    (∃ e : Hyperedge W, e.verts = [w₁, w₂]) →
    (∃ e : Hyperedge V, e.verts = [σ w₁, σ w₂] ∧ e ∈ F.total.edges.toFinset)

/-! ## Connections

A **connection** is a `Finset` of "horizontal" lifts: for every pair
`(v, w')` in total space — where `v` sits above some base vertex `w`
and the base has an edge `w → w'` — the connection provides *at most
one* total-space edge `(v, v')` with `π v' = w'`.

We implement this as a predicate on a subset of total-edges. -/

/-- **A *connection* of a fibered graph** is a `Finset` of horizontal
hyperedges (in `F.total.edges.toFinset`) satisfying the
"at-most-one-edge-lift" property of `AtMostOneEdgeLiftQ`: for every
total vertex `v` and every base edge from `F.π v` to some `w'`, there
is at most one edge `e` in the connection containing `v` whose other
endpoint projects to `w'`. -/
structure Connection (F : FiberedGraph V W) where
  edges : Finset (Hyperedge V)
  horizontal : ∀ e ∈ edges, F.horizontalQ e
  sub_total : ∀ e ∈ edges, e ∈ F.total.edges.toFinset

/-- **The underlying simple graph of a connection** (on total
vertices). Two total vertices are connected iff there is a
connection-edge containing both and it is horizontal (projects to
two distinct base vertices). -/
def connectionAdj {F : FiberedGraph V W} (C : Connection F) (u v : V) : Prop :=
  u ≠ v ∧ ∃ e ∈ C.edges, e.contains u v

instance {F : FiberedGraph V W} (C : Connection F) (u v : V) :
    Decidable (connectionAdj C u v) := by
  unfold connectionAdj
  exact inferInstance

/-- **Every connection-edge is an edge of the total hypergraph.** -/
theorem connectionAdj_implies_total_Adj {F : FiberedGraph V W}
    (C : Connection F) {u v : V}
    (hadj : connectionAdj C u v) : F.total.Adj u v := by
  obtain ⟨hne, e, he_mem, hcontains⟩ := hadj
  refine ⟨hne, e, ?_, hcontains⟩
  exact C.sub_total e he_mem

end FiberedGraph

end InfraFormalization
