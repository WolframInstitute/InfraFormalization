/-
**Knill core primitives** (#257 / IGE1 — Lean port of `Infrageometry.wl`).

First-pass Lean ports of the foundational functions from Oliver Knill's
discrete-geometry program, transcribed from
[`resources/Infrageometry/Infrageometry/Kernel/Infrageometry.wl`](../../resources/Infrageometry/Infrageometry/Kernel/Infrageometry.wl).

This module covers the **simplex / complex / weight / star / closure**
core (the first ~80 lines of the Mathematica file). Subsequent modules
(`KnillIncidence.lean`, `KnillDirac.lean`, …) will port the matrix
operators (`d`, `D = d + d*`, `H = D²`, connection `L`, Green `g = L⁻¹`)
on top of this foundation.

**Design.** A *Knill complex* is just a `Finset (Finset V)` — a set of
simplices. We do **not** bake the simplicial-closure axiom into the
type; instead `complexClosure` is the closure operation, and lemmas
about closed complexes assume `IsClosed G` separately. This matches
Mathematica's convention (`ComplexClosure` is a function, not a
constructor invariant).

Counterpart Mathematica functions (this file):

  * `ComplexClosure` → `complexClosure`
  * `SimplexDimension` → `simplexDimension`
  * `ComplexDimension` → `complexDimension`
  * `SimplexCardinality / ies` → `simplexCardinality` / `_cardinalities`
  * `SimplexWeight` → `simplexWeight` (= `-(-1)^|x|`)
  * `ComplexEulerCharacteristic` → `eulerCharacteristic`
  * `ComplexFermiCharacteristic` → `fermiCharacteristic`
  * `SimplexStar` → `simplexStar`
  * `SimplexCore` → `simplexCore`
  * `SimplexUnitSphere` → `simplexUnitSphere`
  * `IsClosed` (closure invariant for downstream proofs)

**Grounding.** Every type here is a `Finset` of `Finset V` for a
hypergraph vertex set `V`. No continuum. Anchored as the simplicial
side of `Hypergraph V` (the relationship `G = (clique-complex of H)`
is a downstream construction in `KnillVR.lean`).
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace InfraFormalization
namespace Knill

variable {V : Type*} [DecidableEq V]

/-! ## Simplex and complex types

A simplex is a `Finset V` (we take it nonempty when we need to;
the empty set is allowed as a degenerate simplex of dimension `-1`,
matching Mathematica's `SimplexDimension[{}] = -1`). A *complex*
(`SimplexSet V`) is a `Finset` of simplices. -/

/-- A *simplex* on vertex type `V`: a finset of vertices. -/
abbrev Simplex (V : Type*) := Finset V

/-- A *simplex set* / Knill complex: a finset of simplices. The
simplicial-closure axiom is left external (`IsClosed`). -/
abbrev SimplexSet (V : Type*) := Finset (Finset V)

/-! ## Dimension and cardinality -/

/-- **Simplex dimension** `dim(x) = |x| - 1`. The empty simplex has
dimension `-1`. -/
def simplexDimension (s : Simplex V) : ℤ := (s.card : ℤ) - 1

@[simp] theorem simplexDimension_empty :
    simplexDimension (∅ : Simplex V) = -1 := by
  simp [simplexDimension]

@[simp] theorem simplexDimension_singleton (v : V) :
    simplexDimension ({v} : Simplex V) = 0 := by
  simp [simplexDimension]

/-- **Complex dimension** for a nonempty complex: the maximum of
`simplexDimension` over the simplices of `G`. -/
def complexDimension (G : SimplexSet V) (h : G.Nonempty) : ℤ :=
  (G.image simplexDimension).max' (Finset.image_nonempty.mpr h)

theorem complexDimension_le (G : SimplexSet V) (h : G.Nonempty)
    (s : Simplex V) (hs : s ∈ G) :
    simplexDimension s ≤ complexDimension G h := by
  unfold complexDimension
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- **Simplex cardinality at dimension `k`**: number of `k`-simplices
(simplices with `|x| = k + 1`). -/
def simplexCardinality (G : SimplexSet V) (k : ℕ) : ℕ :=
  (G.filter (fun s => s.card = k + 1)).card

/-- **f-vector** of `G` up to maximal dimension `maxDim`: list of
`simplexCardinality G k` for `k = 0, 1, …, maxDim`. -/
def simplexCardinalities (G : SimplexSet V) (maxDim : ℕ) : List ℕ :=
  (List.range (maxDim + 1)).map (simplexCardinality G)

/-! ## Weight, Euler characteristic, Fermi characteristic -/

/-- **Knill simplex weight** `ω(x) = -(-1)^|x| = (-1)^(|x| - 1)`.
For a vertex (`|x| = 1`), `ω = 1`; for an edge (`|x| = 2`), `ω = -1`;
for a triangle (`|x| = 3`), `ω = 1`. -/
def simplexWeight (s : Simplex V) : ℤ := -(-1) ^ s.card

@[simp] theorem simplexWeight_singleton (v : V) :
    simplexWeight ({v} : Simplex V) = 1 := by
  simp [simplexWeight]

theorem simplexWeight_pair {v w : V} (hne : v ≠ w) :
    simplexWeight ({v, w} : Simplex V) = -1 := by
  have h_card : ({v, w} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simpa using hne
  simp [simplexWeight, h_card]

/-- **Euler characteristic** `χ(G) = ∑_{x ∈ G} ω(x)`. The signed sum
of simplex weights. -/
def eulerCharacteristic (G : SimplexSet V) : ℤ :=
  G.sum simplexWeight

@[simp] theorem eulerCharacteristic_empty :
    eulerCharacteristic (∅ : SimplexSet V) = 0 := by
  simp [eulerCharacteristic]

@[simp] theorem eulerCharacteristic_singleton (s : Simplex V) :
    eulerCharacteristic ({s} : SimplexSet V) = simplexWeight s := by
  simp [eulerCharacteristic]

theorem eulerCharacteristic_insert {G : SimplexSet V} {s : Simplex V}
    (h : s ∉ G) :
    eulerCharacteristic (insert s G) = simplexWeight s + eulerCharacteristic G := by
  simp [eulerCharacteristic, Finset.sum_insert h]

/-- **Fermi characteristic** `Fermi(G) = ∏_{x ∈ G} ω(x)`. -/
def fermiCharacteristic (G : SimplexSet V) : ℤ :=
  G.prod simplexWeight

@[simp] theorem fermiCharacteristic_empty :
    fermiCharacteristic (∅ : SimplexSet V) = 1 := by
  simp [fermiCharacteristic]

theorem fermiCharacteristic_insert {G : SimplexSet V} {s : Simplex V}
    (h : s ∉ G) :
    fermiCharacteristic (insert s G) = simplexWeight s * fermiCharacteristic G := by
  simp [fermiCharacteristic, Finset.prod_insert h]

/-! ## Star, core, unit sphere -/

/-- **Star** of a simplex `x` in `G`: all simplices of `G` that contain
`x` as a subset. -/
def simplexStar (G : SimplexSet V) (x : Simplex V) : SimplexSet V :=
  G.filter (fun s => x ⊆ s)

/-- **Core** of a simplex `x` in `G`: all simplices of `G` that are
subsets of `x`. -/
def simplexCore (G : SimplexSet V) (x : Simplex V) : SimplexSet V :=
  G.filter (fun s => s ⊆ x)

/-- **Unit sphere** of a simplex `x` in `G`: all simplices that contain
`x` strictly (so `simplexStar` minus `x` itself). -/
def simplexUnitSphere (G : SimplexSet V) (x : Simplex V) : SimplexSet V :=
  (simplexStar G x).erase x

@[simp] theorem mem_simplexStar (G : SimplexSet V) (x s : Simplex V) :
    s ∈ simplexStar G x ↔ s ∈ G ∧ x ⊆ s := by
  simp [simplexStar]

@[simp] theorem mem_simplexCore (G : SimplexSet V) (x s : Simplex V) :
    s ∈ simplexCore G x ↔ s ∈ G ∧ s ⊆ x := by
  simp [simplexCore]

theorem mem_simplexUnitSphere (G : SimplexSet V) (x s : Simplex V) :
    s ∈ simplexUnitSphere G x ↔ s ∈ G ∧ x ⊆ s ∧ s ≠ x := by
  simp [simplexUnitSphere, simplexStar]
  tauto

/-! ## Closure (simplicial-closure axiom)

`complexClosure facets` takes a list of facets (top-dimensional
simplices) and returns the smallest simplicial complex containing
them — i.e., the union of all nonempty subsets of each facet. -/

/-- **Complex closure** of a set of facets: union of nonempty subsets
of each facet. Matches Mathematica's `ComplexClosure`. -/
def complexClosure (facets : SimplexSet V) : SimplexSet V :=
  facets.biUnion (fun s => s.powerset.erase ∅)

/-- A simplex set `G` **is closed** under subsets (the simplicial-complex
axiom): every nonempty subset of a simplex of `G` is also in `G`. -/
def IsClosed (G : SimplexSet V) : Prop :=
  ∀ s ∈ G, ∀ t : Simplex V, t ⊆ s → t ≠ ∅ → t ∈ G

theorem mem_complexClosure {facets : SimplexSet V} {t : Simplex V} :
    t ∈ complexClosure facets ↔ ∃ s ∈ facets, t ⊆ s ∧ t ≠ ∅ := by
  simp [complexClosure, Finset.mem_biUnion, Finset.mem_erase,
        Finset.mem_powerset, and_comm]

/-- **The closure of a complex is closed.** Idempotency of subset
closure. -/
theorem complexClosure_isClosed (facets : SimplexSet V) :
    IsClosed (complexClosure facets) := by
  intro s hs t hst ht_ne
  rw [mem_complexClosure] at hs ⊢
  obtain ⟨f, hf_facets, hsf, _⟩ := hs
  exact ⟨f, hf_facets, hst.trans hsf, ht_ne⟩

/-! ## Vertex extraction -/

/-- **Vertices of a complex**: union of all simplices in `G`, viewed as
a single finset of vertices. -/
def complexVertexList (G : SimplexSet V) : Finset V :=
  G.biUnion id

@[simp] theorem mem_complexVertexList (G : SimplexSet V) (v : V) :
    v ∈ complexVertexList G ↔ ∃ s ∈ G, v ∈ s := by
  simp [complexVertexList]

/-! ## Wu characteristic (KN3 entry point)

The **Wu characteristic** generalises Euler characteristic by summing
the product of weights over m-tuples of pairwise-intersecting
simplices. For m = 1 it reduces to Euler characteristic; for m = 2 it
is the *quadratic characteristic* used in Knill 2018+.

For m = 2: `ω₂(G) = ∑_{(x, y) ∈ G × G, x ∩ y ≠ ∅} ω(x) · ω(y)`.

This is the m = 1, 2 case directly. The general
`m ≥ 3` case requires iterated `Finset.product` and is staged for a
follow-up commit closing the rest of KN3 (Wu cohomology + fusion
inequality). -/

/-- **Wu characteristic at m = 1**: equals `eulerCharacteristic`. The
single-simplex sum. -/
def wuCharacteristic₁ (G : SimplexSet V) : ℤ :=
  eulerCharacteristic G

@[simp] theorem wuCharacteristic₁_eq_euler (G : SimplexSet V) :
    wuCharacteristic₁ G = eulerCharacteristic G := rfl

/-- **Wu characteristic at m = 2** (quadratic characteristic):
`ω₂(G) = ∑_{(x, y) ∈ G × G, x ∩ y ≠ ∅} ω(x) · ω(y)`. -/
def wuCharacteristic₂ (G : SimplexSet V) : ℤ :=
  ((G.product G).filter (fun p => (p.1 ∩ p.2).Nonempty)).sum
    (fun p => simplexWeight p.1 * simplexWeight p.2)

@[simp] theorem wuCharacteristic₂_empty :
    wuCharacteristic₂ (∅ : SimplexSet V) = 0 := by
  simp [wuCharacteristic₂]

/-- **Wu characteristic at m = 2 of a singleton complex**: a single
simplex `s` with `s ∩ s = s ≠ ∅` (when `s ≠ ∅`) gives `ω(s)²`. -/
theorem wuCharacteristic₂_singleton (s : Simplex V) (hs : s.Nonempty) :
    wuCharacteristic₂ ({s} : SimplexSet V) = simplexWeight s * simplexWeight s := by
  unfold wuCharacteristic₂
  have h_inter : (s ∩ s).Nonempty := by rw [Finset.inter_self]; exact hs
  have h_filt : (({s} ×ˢ {s} : Finset (Simplex V × Simplex V)).filter
      (fun p => (p.1 ∩ p.2).Nonempty)) = {(s, s)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
               Prod.mk.injEq]
    refine ⟨fun ⟨⟨ha, hb⟩, _⟩ => ⟨ha, hb⟩, fun ⟨ha, hb⟩ => ?_⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    rw [ha, hb]; exact h_inter
  show ((({s} : SimplexSet V) ×ˢ ({s} : SimplexSet V)).filter _).sum _ = _
  rw [h_filt]
  simp

/-! ## Codim-1 face relation (incidence-matrix prerequisite)

`isFace x y` holds when `y` is a codimension-1 face of `x`: a
proper subset with one fewer vertex. This is the index-set of the
non-zero entries of the (unsigned) incidence matrix; the *signed*
boundary operator (Dirac `d`) is a follow-up commit that requires
a `LinearOrder V` to fix orientation. -/

/-- **Codim-1 face**: `y ⊆ x` with `|x| = |y| + 1`. Equivalently, `y`
is obtained from `x` by removing exactly one vertex. -/
def isFace (x y : Simplex V) : Prop :=
  y ⊆ x ∧ x.card = y.card + 1

instance (x y : Simplex V) : Decidable (isFace x y) := by
  unfold isFace; infer_instance

/-- **Removing a vertex gives a codim-1 face.** -/
theorem isFace_erase {x : Simplex V} {v : V} (hv : v ∈ x) :
    isFace x (x.erase v) := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  rw [Finset.card_erase_of_mem hv]
  have : 1 ≤ x.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- **Set difference of a codim-1 face has cardinality 1.** -/
theorem isFace_diff_card {x y : Simplex V} (h : isFace x y) :
    (x \ y).card = 1 := by
  obtain ⟨hyx, hcard⟩ := h
  have h1 : (x \ y).card + y.card = x.card :=
    Finset.card_sdiff_add_card_eq_card hyx
  omega

/-- **There exists a unique vertex `v ∈ x \ y` for any codim-1 face `y` of `x`**. -/
theorem isFace_exists_diff_vertex {x y : Simplex V} (h : isFace x y) :
    ∃ v, v ∈ x ∧ v ∉ y := by
  have hcard := isFace_diff_card h
  have hne : (x \ y).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  obtain ⟨v, hv⟩ := hne
  rw [Finset.mem_sdiff] at hv
  exact ⟨v, hv.1, hv.2⟩

/-! ## Connection matrix (#270)

Knill's **connection matrix** `L` on a simplex set `G`:

  `L(x, y) := χ(simplexCore G x ∩ simplexCore G y)`

The Euler characteristic of the set of simplices that are subsets of
both `x` and `y` (equivalently, of `x ∩ y`). Sign-free; no
orientation required. This matrix has the remarkable property
`det L = ±1` (= Knill's Fermi characteristic) for any simplicial
complex — proved in a follow-up. The Green function `g = L⁻¹` (#271)
satisfies the energy theorem `∑ g(x, y) = χ(G)`.

Counterpart Mathematica: `ConnectionMatrix[G_]` in
`Infrageometry.wl` / `QuantumCalculus.wl`. -/

/-- **Connection-matrix entry** `L(x, y) := χ(core(x) ∩ core(y))`,
the Euler characteristic of the simplices in `G` that are subsets of
both `x` and `y`. -/
def connectionEntry (G : SimplexSet V) (x y : Simplex V) : ℤ :=
  eulerCharacteristic (simplexCore G x ∩ simplexCore G y)

/-- **Symmetry**: `L(x, y) = L(y, x)`. The connection matrix is
symmetric — intersection commutes. -/
theorem connectionEntry_symm (G : SimplexSet V) (x y : Simplex V) :
    connectionEntry G x y = connectionEntry G y x := by
  unfold connectionEntry
  rw [Finset.inter_comm]

/-- **Diagonal**: `L(x, x) = χ(core(x))`. -/
theorem connectionEntry_self (G : SimplexSet V) (x : Simplex V) :
    connectionEntry G x x = eulerCharacteristic (simplexCore G x) := by
  unfold connectionEntry
  rw [Finset.inter_self]

/-- **Off-support vanishing**: if `x ∩ y = ∅` (no common vertex) and
`G` is closed (every simplex of `G` has all its vertices among the
union of the simplices of `G`), then `L(x, y) = 0` because no
simplex `s ∈ G` can satisfy `s ⊆ x ∧ s ⊆ y` (the only candidate is
`s = ∅`, which is not a valid simplex in our convention; we exclude
it via the `simplexCore` filter). Stated as: when no nonempty
simplex of `G` is contained in both `x` and `y`, the entry is 0. -/
theorem connectionEntry_eq_zero_of_no_common_subsimplex
    (G : SimplexSet V) (x y : Simplex V)
    (h : ∀ s ∈ G, ¬ (s ⊆ x ∧ s ⊆ y)) :
    connectionEntry G x y = 0 := by
  unfold connectionEntry
  have h_inter_empty : simplexCore G x ∩ simplexCore G y = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro s hs
    rw [Finset.mem_inter, mem_simplexCore, mem_simplexCore] at hs
    obtain ⟨⟨hsG, hsx⟩, _, hsy⟩ := hs
    exact h s hsG ⟨hsx, hsy⟩
  rw [h_inter_empty, eulerCharacteristic_empty]

/-- **Knill's mass identity**: for the diagonal of `L`, summing the
weighted entries gives the Euler characteristic of `G`. (Stated for
the diagonal only; the full Green-function energy theorem
`∑ g(x, y) = χ(G)` follows after Green is defined.) -/
theorem sum_simplexWeight_connectionEntry_diag (G : SimplexSet V) :
    G.sum (fun x => simplexWeight x * connectionEntry G x x)
      = G.sum (fun x => simplexWeight x * eulerCharacteristic (simplexCore G x)) := by
  apply Finset.sum_congr rfl
  intros x _
  rw [connectionEntry_self]

end Knill
end InfraFormalization
