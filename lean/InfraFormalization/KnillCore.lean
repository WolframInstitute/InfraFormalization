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

end Knill
end InfraFormalization
