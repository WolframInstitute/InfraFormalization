/-
Fibered graphs, sections and connections.

This module defines `FiberedGraph V W`, a hypergraph on `V` with a function `π : V → W`, the fiber
`F.fiber w` over a base vertex, vertical and horizontal hyperedges, sections `σ : W → V` with
`π ∘ σ = id`, and `Connection`, a finite set of horizontal hyperedges of the total
hypergraph.
It proves that fibers over distinct base vertices are disjoint, that each vertex lies in exactly one
fiber, and that adjacency through a connection edge implies `Hypergraph.Adj` in the total space.
The definitions follow `FiberedGraph.wl`, `Sections.wl` and `Connections.wl` in
`resources/InfraGaugeTheory/Kernel/`.
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- A hypergraph `total` on `V` with a function `π : V → W`. No condition is imposed on `π`. -/
structure FiberedGraph (V W : Type*) where
  total : Hypergraph V
  π     : V → W

namespace FiberedGraph

variable (F : FiberedGraph V W)

/-- The preimage of `w` under `π`. -/
def fiber (w : W) : Finset V :=
  Finset.univ.filter (fun v => F.π v = w)

/-- `v ∈ F.fiber w` if and only if `F.π v = w`. -/
theorem mem_fiber (v : V) (w : W) : v ∈ F.fiber w ↔ F.π v = w := by
  unfold fiber
  simp

/-- `v ∈ F.fiber (F.π v)`. -/
theorem self_mem_fiber (v : V) : v ∈ F.fiber (F.π v) :=
  (F.mem_fiber v (F.π v)).mpr rfl

/-- Fibers over distinct base vertices are disjoint. -/
theorem disjoint_fibers {w₁ w₂ : W} (h : w₁ ≠ w₂) :
    Disjoint (F.fiber w₁) (F.fiber w₂) := by
  rw [Finset.disjoint_left]
  intros v hv₁ hv₂
  rw [F.mem_fiber] at hv₁ hv₂
  exact h (hv₁.symm.trans hv₂)

/-- Each vertex lies in the fiber of exactly one base vertex. -/
theorem exists_unique_fiber (v : V) : ∃! w : W, v ∈ F.fiber w := by
  refine ⟨F.π v, F.self_mem_fiber v, ?_⟩
  intros w hw
  rw [F.mem_fiber] at hw
  exact hw.symm

/-- All vertices of `e` have the same image under `π`. -/
def verticalQ (e : Hyperedge V) : Prop :=
  ∀ u ∈ e.verts, ∀ v ∈ e.verts, F.π u = F.π v

instance (e : Hyperedge V) : Decidable (F.verticalQ e) := by
  unfold verticalQ
  exact inferInstance

/-- `e` is not vertical. -/
def horizontalQ (e : Hyperedge V) : Prop := ¬ F.verticalQ e

/-! ## Sections -/

/-- `π (σ w) = w` for every `w : W`. -/
def IsSection (F : FiberedGraph V W) (σ : W → V) : Prop :=
  ∀ w : W, F.π (σ w) = w

/-- The image of `σ` as a `Finset V`. The value does not depend on `F`. -/
def sectionImage (F : FiberedGraph V W) (σ : W → V) : Finset V :=
  let _ := F
  Finset.univ.image σ

theorem mem_sectionImage_iff (F : FiberedGraph V W) (σ : W → V) (v : V) :
    v ∈ F.sectionImage σ ↔ ∃ w : W, σ w = v := by
  unfold sectionImage
  simp

/-- For a section `σ`, `σ w ∈ F.fiber w`. -/
theorem section_mem_fiber (F : FiberedGraph V W) (σ : W → V)
    (hσ : F.IsSection σ) (w : W) :
    σ w ∈ F.fiber w :=
  (F.mem_fiber (σ w) w).mpr (hσ w)

/-! ## Connections -/

/-- A finite set of hyperedges of the total hypergraph, each of which is horizontal. The structure
does not include an at-most-one-lift condition. -/
structure Connection (F : FiberedGraph V W) where
  edges : Finset (Hyperedge V)
  horizontal : ∀ e ∈ edges, F.horizontalQ e
  sub_total : ∀ e ∈ edges, e ∈ F.total.edges.toFinset

/-- `u ≠ v` and some edge of `C` contains both `u` and `v`. -/
def connectionAdj {F : FiberedGraph V W} (C : Connection F) (u v : V) : Prop :=
  u ≠ v ∧ ∃ e ∈ C.edges, e.contains u v

instance {F : FiberedGraph V W} (C : Connection F) (u v : V) :
    Decidable (connectionAdj C u v) := by
  unfold connectionAdj
  exact inferInstance

/-- `connectionAdj C u v` implies `F.total.Adj u v`. -/
theorem connectionAdj_implies_total_Adj {F : FiberedGraph V W}
    (C : Connection F) {u v : V}
    (hadj : connectionAdj C u v) : F.total.Adj u v := by
  obtain ⟨hne, e, he_mem, hcontains⟩ := hadj
  refine ⟨hne, e, ?_, hcontains⟩
  exact C.sub_total e he_mem

end FiberedGraph

end InfraFormalization
