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
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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

/-! ## Green function (#271)

Knill's **Green function** matrix `g`, the matrix inverse of `L`:

  `g(x, y) := ω(x) · ω(y) · χ(simplexStar G x ∩ simplexStar G y)`

with `ω` the simplex weight `-(-1)^|x|`. Two key identities:
  * `Inverse[L] = Transpose[g]` (matrix inverse of L is transpose of g)
  * **Energy theorem**: `∑_{x, y} g(x, y) = χ(G)`

Counterpart Mathematica: `GreenFunctionMatrix[G_]` /
`g[G, T]` (dynamical version) in `Infrageometry.wl` /
`QuantumCalculus.wl`. -/

/-- **Green-function entry**:
`g(x, y) := ω(x) · ω(y) · χ(star(x) ∩ star(y))`. Weighted Euler
characteristic of the simplices that contain both `x` and `y`. -/
def greenEntry (G : SimplexSet V) (x y : Simplex V) : ℤ :=
  simplexWeight x * simplexWeight y *
    eulerCharacteristic (simplexStar G x ∩ simplexStar G y)

/-- **Symmetry**: `g(x, y) = g(y, x)`. -/
theorem greenEntry_symm (G : SimplexSet V) (x y : Simplex V) :
    greenEntry G x y = greenEntry G y x := by
  unfold greenEntry
  rw [Finset.inter_comm, mul_comm (simplexWeight x) (simplexWeight y)]

/-- **Diagonal**: `g(x, x) = ω(x)² · χ(star(x))`. Note `ω(x)² = 1`
for any simplex (since `ω(x) = ±1`), so this simplifies further:
`g(x, x) = χ(star(x))`. We state the unsimplified form first. -/
theorem greenEntry_self (G : SimplexSet V) (x : Simplex V) :
    greenEntry G x x =
      simplexWeight x * simplexWeight x *
        eulerCharacteristic (simplexStar G x) := by
  unfold greenEntry
  rw [Finset.inter_self]

/-- **Off-support vanishing**: when no simplex of `G` contains both
`x` and `y` (no common super-simplex), `g(x, y) = 0`. -/
theorem greenEntry_eq_zero_of_no_common_supersimplex
    (G : SimplexSet V) (x y : Simplex V)
    (h : ∀ s ∈ G, ¬ (x ⊆ s ∧ y ⊆ s)) :
    greenEntry G x y = 0 := by
  unfold greenEntry
  have h_inter_empty : simplexStar G x ∩ simplexStar G y = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro s hs
    rw [Finset.mem_inter, mem_simplexStar, mem_simplexStar] at hs
    obtain ⟨⟨hsG, hsx⟩, _, hsy⟩ := hs
    exact h s hsG ⟨hsx, hsy⟩
  rw [h_inter_empty, eulerCharacteristic_empty]
  ring

/-- **Weight squared identity**: `ω(x)² = 1` for any simplex. -/
theorem simplexWeight_sq (s : Simplex V) :
    simplexWeight s * simplexWeight s = 1 := by
  unfold simplexWeight
  rw [neg_mul_neg, ← pow_add]
  rw [show s.card + s.card = 2 * s.card from by ring, pow_mul]
  norm_num

/-- **Diagonal simplified**: `g(x, x) = χ(star(x))`. -/
theorem greenEntry_self_simplified (G : SimplexSet V) (x : Simplex V) :
    greenEntry G x x = eulerCharacteristic (simplexStar G x) := by
  rw [greenEntry_self, simplexWeight_sq, one_mul]

/-! ## Super-trace (#273)

**Super-trace** of a simplex-indexed function: the signed sum
`Str[X] := ∑_{x ∈ G} ω(x) · X(x, x)`. The signing distinguishes
even-dimensional simplices (positive contribution) from odd-
dimensional (negative). Knill's super-symmetry between even/odd
forms (KN14) is articulated through the super-trace identity
`Str[H] = χ(G)` for the Hodge Laplacian `H = D²`.

Counterpart Mathematica: `SuperTrace[G_, X_]` in `Infrageometry.wl`
/ `QuantumCalculus.wl`.

Pseudo-determinant and super-determinant — which need eigenvalue
machinery — are staged for follow-up commits closing the rest of
#273. -/

/-- **Super-trace** of a simplex-indexed function.
`superTrace G X := ∑_{x ∈ G} ω(x) · X x x`. -/
def superTrace (G : SimplexSet V) (X : Simplex V → Simplex V → ℤ) : ℤ :=
  G.sum (fun x => simplexWeight x * X x x)

@[simp] theorem superTrace_empty (X : Simplex V → Simplex V → ℤ) :
    superTrace (∅ : SimplexSet V) X = 0 := by
  simp [superTrace]

theorem superTrace_insert {G : SimplexSet V} {s : Simplex V}
    (h : s ∉ G) (X : Simplex V → Simplex V → ℤ) :
    superTrace (insert s G) X = simplexWeight s * X s s + superTrace G X := by
  simp [superTrace, Finset.sum_insert h]

/-- **Super-trace of a sum** is additive in `X`. -/
theorem superTrace_add (G : SimplexSet V) (X Y : Simplex V → Simplex V → ℤ) :
    superTrace G (fun x y => X x y + Y x y)
      = superTrace G X + superTrace G Y := by
  unfold superTrace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros x _
  ring

/-- **Super-trace of the constant `δ_{xy}` matrix** equals
`eulerCharacteristic G` (since `X x x = 1` for all x). -/
theorem superTrace_diag_one (G : SimplexSet V) :
    superTrace G (fun _ _ => (1 : ℤ)) = eulerCharacteristic G := by
  unfold superTrace eulerCharacteristic
  apply Finset.sum_congr rfl
  intros x _
  ring

/-! ## Signed incidence operator `d` (#269)

For an ordered vertex type (`[LinearOrder V]`), each simplex acquires
a canonical orientation via the sorted list of its vertices. The
**signed incidence** `incidence x y : ℤ` is `(-1)^i` when `y` is the
codim-1 face of `x` obtained by removing the i-th vertex (in sorted
order); zero otherwise.

This is the **boundary operator** on oriented simplices. The
fundamental property `d ∘ d = 0` (cochain-complex condition) follows
from a sign-cancellation argument on codim-2 faces; staged for a
follow-up commit.

Counterpart Mathematica: `s[x_, y_]` in `Infrageometry.wl` /
`QuantumCalculus.wl`. Foundation for KN1 (wave equation), KN4
(isospectral deformation), KN8 (Dirac zeta), KN14 (McKean-Singer
supersymmetry). -/

variable [LinearOrder V]

/-- **Missing vertex of a codim-1 face**: given `isFace x y`, the
unique vertex of `x` not in `y`. Pulled out as its own definition to
keep `incidence`'s `dif_pos` body free of nested `let`/`have` proof
terms (which obstructed `congr` and `rewrite` motives). -/
def missingVertex {x y : Simplex V} (h : isFace x y) : V :=
  (x \ y).min'
    (Finset.card_pos.mp (by rw [isFace_diff_card h]; omega))

/-- **`missingVertex` lies in `x \ y`**: the extracted vertex is in
`x` and not in `y`. -/
theorem missingVertex_mem_sdiff {x y : Simplex V} (h : isFace x y) :
    missingVertex h ∈ x \ y := by
  unfold missingVertex
  exact Finset.min'_mem _ _

/-- **Singleton-extraction**: when `x \ y = {v}`, `missingVertex h = v`. -/
theorem missingVertex_eq_of_sdiff_eq_singleton
    {x y : Simplex V} (h : isFace x y) {v : V}
    (h_eq : x \ y = {v}) :
    missingVertex h = v := by
  have h_mem : missingVertex h ∈ ({v} : Finset V) := by
    rw [← h_eq]; exact missingVertex_mem_sdiff h
  exact Finset.mem_singleton.mp h_mem

/-- **`missingVertex` of `x.erase w` is `w`**: removing a vertex `w`
from `x` and asking which vertex went missing returns `w`. -/
theorem missingVertex_erase {x : Simplex V} {w : V} (hw : w ∈ x) :
    missingVertex (isFace_erase hw) = w := by
  apply missingVertex_eq_of_sdiff_eq_singleton
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨hvx, hve⟩
    by_contra hne
    exact hve ⟨hne, hvx⟩
  · rintro rfl
    exact ⟨hw, fun h => h.1 rfl⟩

/-- **Signed incidence** `d(x, y) := (-1)^i` if `y = x \ {v_i}` for
the i-th vertex of `x` in sorted order; 0 otherwise. The missing
vertex is extracted via the `missingVertex` helper above. -/
def incidence (x y : Simplex V) : ℤ :=
  if h : isFace x y then
    (-1 : ℤ) ^ (x.sort (· ≤ ·)).idxOf (missingVertex h)
  else 0

/-- **Off-support vanishing**: `d(x, y) = 0` when `y` is not a codim-1
face of `x`. -/
theorem incidence_eq_zero_of_not_isFace {x y : Simplex V}
    (h : ¬ isFace x y) :
    incidence x y = 0 := by
  unfold incidence
  rw [dif_neg h]

/-- **Self-incidence is zero**: `d(x, x) = 0` because `x` is not a
codim-1 face of itself (the cardinalities don't differ by 1). -/
theorem incidence_self (x : Simplex V) : incidence x x = 0 := by
  apply incidence_eq_zero_of_not_isFace
  intro h
  obtain ⟨_, hcard⟩ := h
  omega

/-- **Sign is a unit**: `d(x, y) ∈ {-1, 0, 1}` always. Specifically,
`(d(x, y))² = 0` if `¬ isFace x y`, else `1`. -/
theorem incidence_sq (x y : Simplex V) :
    incidence x y * incidence x y =
      if isFace x y then 1 else 0 := by
  unfold incidence
  by_cases h : isFace x y
  · rw [dif_pos h, if_pos h, ← pow_add]
    set k := (x.sort (· ≤ ·)).idxOf (missingVertex h)
    rw [show k + k = 2 * k from by ring, pow_mul]
    norm_num
  · rw [dif_neg h, if_neg h, mul_zero]

/-! ## Dirac and Hodge matrices (#272)

The **Dirac matrix** `D = d + d*` is the symmetrised sum of the
incidence operator and its transpose:

  `dirac x y := incidence x y + incidence y x`

It's self-adjoint by construction (`dirac x y = dirac y x`). The
**Hodge matrix** `H = D²` is its square; on a finite simplex set `G`
this is a matrix product indexed over `G`:

  `hodgeOnG G x y := ∑_{z ∈ G} dirac x z · dirac z y`

These are the load-bearing operators for the entire Knill spectral
program: KN1 (wave eq via `cos(D t)`), KN4 (Lax pair `D' = [B, D]`),
KN8 (Dirac zeta `str(|D|^{-s})`), KN14 (McKean-Singer supersymmetry
between even/odd-form spectra of `H`), KN9 (analytic torsion via
Hodge block determinants).

Counterpart Mathematica: `DiracHodgeMatrix[G_]` / `HodgeMatrix[G_]`
in `Infrageometry.wl`. -/

/-- **Dirac matrix entry** `D(x, y) := d(x, y) + d(y, x)`. -/
def dirac (x y : Simplex V) : ℤ :=
  incidence x y + incidence y x

/-- **Self-adjointness**: `D(x, y) = D(y, x)`. Symmetry follows from
the symmetric definition. -/
theorem dirac_symm (x y : Simplex V) : dirac x y = dirac y x := by
  unfold dirac; ring

/-- **Diagonal vanishes**: `D(x, x) = 0` since `d(x, x) = 0`. -/
@[simp] theorem dirac_self (x : Simplex V) : dirac x x = 0 := by
  unfold dirac
  rw [incidence_self]
  ring

/-- **Off-support vanishing**: `D(x, y) = 0` when `x` and `y` are
neither codim-1 faces of each other (no incidence either way). -/
theorem dirac_eq_zero_of_no_face {x y : Simplex V}
    (hxy : ¬ isFace x y) (hyx : ¬ isFace y x) :
    dirac x y = 0 := by
  unfold dirac
  rw [incidence_eq_zero_of_not_isFace hxy,
      incidence_eq_zero_of_not_isFace hyx]
  ring

/-- **Hodge Laplacian on a simplex set**:
`H(x, y) := (D · D) (x, y) = ∑_{z ∈ G} D(x, z) · D(z, y)`.

Matrix product of `D` with itself, restricted to indices in `G`. -/
def hodgeOnG (G : SimplexSet V) (x y : Simplex V) : ℤ :=
  G.sum (fun z => dirac x z * dirac z y)

/-- **Self-adjointness of Hodge**: `H(x, y) = H(y, x)` for every
finite simplex set `G`. Follows from `dirac_symm`. -/
theorem hodgeOnG_symm (G : SimplexSet V) (x y : Simplex V) :
    hodgeOnG G x y = hodgeOnG G y x := by
  unfold hodgeOnG
  apply Finset.sum_congr rfl
  intros z _
  rw [dirac_symm x z, dirac_symm z y]
  ring

/-! ## d² = 0 — cochain-complex identity (#272 follow-up)

The fundamental identity `d ∘ d = 0` makes `(C_•, d)` a chain
complex. For incidence on oriented simplices:

  `(d ∘ d)(x, z) := ∑_{y ⊆ x} incidence x y · incidence y z = 0`

Mathematically: for `|x| = |z| + 2` and `z ⊂ x`, the codim-1 faces
`y` between them are exactly `y₁ = z ∪ {a}` and `y₂ = z ∪ {b}`
where `{a, b} = x \ z`. The two contributions cancel by sign
(`(-1)^(i+j) + (-1)^(i+j-1) = 0` where `i, j` are the positions of
`a, b` in sorted `x`).

Sum is over `x.powerset` rather than the universe (the only
non-zero contributors satisfy `y ⊆ x`). Definition first; full
sign-cancellation proof staged.

Counterpart: this is the standard chain-complex axiom on oriented
simplicial complexes; foundational for KN14 McKean-Singer
supersymmetry (the Hodge `H = D²` decomposes via `D = d + d*`,
and `d² = 0` separates exact / co-exact components). -/

/-- **`d ∘ d` operator**: `(d²)(x, z) := ∑_{y ⊆ x} d(x, y) · d(y, z)`.
The sum is over `x.powerset` because non-zero contributions require
`y ⊆ x`. -/
def dSquared (x z : Simplex V) : ℤ :=
  x.powerset.sum (fun y => incidence x y * incidence y z)

/-- **Trivial cardinality vanishing**: `(d²)(x, z) = 0` when
`|x| ≠ |z| + 2`. The intermediate `y` would need `|x| = |y| + 1`
and `|y| = |z| + 1`, forcing `|x| = |z| + 2`. -/
theorem dSquared_eq_zero_of_card_ne {x z : Simplex V}
    (h_ne : x.card ≠ z.card + 2) :
    dSquared x z = 0 := by
  unfold dSquared
  apply Finset.sum_eq_zero
  intros y hy
  rw [Finset.mem_powerset] at hy
  -- For incidence x y * incidence y z ≠ 0, need isFace x y and isFace y z.
  by_cases hxy : isFace x y
  · by_cases hyz : isFace y z
    · obtain ⟨_, hcxy⟩ := hxy
      obtain ⟨_, hcyz⟩ := hyz
      exfalso; apply h_ne; omega
    · rw [incidence_eq_zero_of_not_isFace hyz, mul_zero]
  · rw [incidence_eq_zero_of_not_isFace hxy, zero_mul]

/-- **Trivial subset vanishing**: `(d²)(x, z) = 0` when `z ⊄ x`. Any
`y ∈ x.powerset` would need `z ⊆ y ⊆ x`, contradicting `z ⊄ x`. -/
theorem dSquared_eq_zero_of_not_subset {x z : Simplex V}
    (h_not_sub : ¬ z ⊆ x) :
    dSquared x z = 0 := by
  unfold dSquared
  apply Finset.sum_eq_zero
  intros y hy
  rw [Finset.mem_powerset] at hy
  by_cases hyz : isFace y z
  · obtain ⟨hzy, _⟩ := hyz
    exact absurd (hzy.trans hy) h_not_sub
  · rw [incidence_eq_zero_of_not_isFace hyz, mul_zero]

/-- **Incidence on an `erase`** (clean version): for `w ∈ x`,
`incidence x (x.erase w) = (-1)^(idxOf w in sort x)`. Trivial after
the `missingVertex` refactor — the body becomes a single `simp`. -/
theorem incidence_erase (x : Simplex V) (w : V) (hw : w ∈ x) :
    incidence x (x.erase w) = (-1 : ℤ) ^ (x.sort (· ≤ ·)).idxOf w := by
  unfold incidence
  rw [dif_pos (isFace_erase hw), missingVertex_erase hw]

/-! ### General `d ∘ d = 0` — staged

For `|x| = |z| + 2` and `z ⊆ x`, the only y's contributing non-zero
summands are the two `x.erase w` for `w ∈ x \ z`. The two
contributions cancel by sign:

  * For `w = a` (smaller of the two missing vertices, position `i`
    in sorted `x`): contribution `(-1)^i · (-1)^(j-1)` where `j` is
    the position of the larger missing vertex `b` in sorted `x`. In
    sorted `(x.erase a)`, `b` is at position `j-1` because removing
    a vertex earlier than `b` shifts `b`'s index down by 1.
  * For `w = b` (larger): contribution `(-1)^j · (-1)^i` because in
    sorted `(x.erase b)`, `a` is still at position `i` (removing a
    later vertex doesn't shift `a`).

Sum = `(-1)^(i+j-1) + (-1)^(i+j) = 0`.

**Status**: Trivial sides (`_of_card_ne` for cardinality mismatch,
`_of_not_subset` for `z ⊄ x`) are proved above. The main case
requires position-arithmetic on sorted lists (specifically, how
`Finset.sort (·≤·)` interacts with `Finset.erase`) plus the
summand-characterization argument that pins down the exactly-two
contributing y's. Both helpers are non-trivial in Lean because the
`incidence` definition uses `let`-bindings inside a `dif_pos`
branch, which `congr` does not transparently unfold.

Concrete `(d²)({0,1,2}, {i}) = 0` instances at `i = 0, 1, 2` are
already discharged by `native_decide` in `KnillExamples.lean`. Full
general proof staged for a focused follow-up commit. -/

end Knill
end InfraFormalization
