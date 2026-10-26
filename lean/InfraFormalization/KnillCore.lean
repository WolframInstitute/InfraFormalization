/-
Simplicial complexes after O. Knill.

This module ports basic functions of Knill's discrete geometry from
`resources/Infrageometry/Infrageometry/Kernel/Infrageometry.wl`. A complex is a `Finset (Finset V)`;
closure under subsets is the separate predicate `IsClosed`, and `complexClosure` computes the
closure
of a set of facets. The module defines simplex dimension, f-vector, the weight `ω(x) = -(-1)^|x|`,
the Euler and Fermi characteristics, star, core and unit sphere, the Wu characteristic for m = 1, 2,
Knill's connection and Green matrices, the super-trace, the signed incidence `d`, the Dirac matrix
`D = d + dᵀ` and the Hodge matrix `D²`, and vertex angle defects. It proves the Euler–Poincaré
formula, positive semidefiniteness of `D²`, `d ∘ d = 0` and `dᵀ ∘ dᵀ = 0`.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace InfraFormalization
namespace Knill

variable {V : Type*} [DecidableEq V]

/-! ## Simplex and complex types

A simplex is a `Finset V`. The empty set is allowed and has dimension `-1`, as
`SimplexDimension[{}]`
in the Mathematica source. A complex (`SimplexSet V`) is a `Finset` of simplices. -/

/-- A simplex on vertex type `V`: a finset of vertices. -/
abbrev Simplex (V : Type*) := Finset V

/-- A complex: a finset of simplices, with no closure condition imposed. -/
abbrev SimplexSet (V : Type*) := Finset (Finset V)

/-! ## Dimension and cardinality -/

/-- `dim(x) = |x| - 1`. The empty simplex has dimension `-1`. -/
def simplexDimension (s : Simplex V) : ℤ := (s.card : ℤ) - 1

@[simp] theorem simplexDimension_empty :
    simplexDimension (∅ : Simplex V) = -1 := by
  simp [simplexDimension]

@[simp] theorem simplexDimension_singleton (v : V) :
    simplexDimension ({v} : Simplex V) = 0 := by
  simp [simplexDimension]

/-- The maximum of `simplexDimension` over the simplices of a nonempty complex `G`. -/
def complexDimension (G : SimplexSet V) (h : G.Nonempty) : ℤ :=
  (G.image simplexDimension).max' (Finset.image_nonempty.mpr h)

theorem complexDimension_le (G : SimplexSet V) (h : G.Nonempty)
    (s : Simplex V) (hs : s ∈ G) :
    simplexDimension s ≤ complexDimension G h := by
  unfold complexDimension
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- The number of simplices of `G` with `k + 1` vertices. -/
def simplexCardinality (G : SimplexSet V) (k : ℕ) : ℕ :=
  (G.filter (fun s => s.card = k + 1)).card

/-- The f-vector of `G`: the list of `simplexCardinality G k` for `k = 0, 1, …, maxDim`. -/
def simplexCardinalities (G : SimplexSet V) (maxDim : ℕ) : List ℕ :=
  (List.range (maxDim + 1)).map (simplexCardinality G)

/-! ## Weight, Euler characteristic, Fermi characteristic -/

/-- The simplex weight `ω(x) = -(-1)^|x|`: 1 for a vertex, -1 for an edge, 1 for a triangle. -/
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

/-- The Euler characteristic `χ(G) = ∑_{x ∈ G} ω(x)`. -/
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

/-- `ω(∅) = -1`. -/
@[simp] theorem simplexWeight_empty :
    simplexWeight (∅ : Simplex V) = -1 := by
  simp [simplexWeight]

/-- If `σ.card = k + 1`, then `ω(σ) = (-1)^k`. -/
theorem simplexWeight_eq_neg_one_pow_dim {σ : Simplex V} {k : ℕ} (h : σ.card = k + 1) :
    simplexWeight σ = (-1)^k := by
  unfold simplexWeight
  rw [h, pow_succ]
  ring

/-! ## f-vector and the Euler–Poincaré formula -/

/-- The `k`-skeleton of `G`: the simplices of `G` with `k + 1` vertices. -/
def kSkeleton (G : SimplexSet V) (k : ℕ) : SimplexSet V :=
  G.filter (fun s => s.card = k + 1)

@[simp] theorem mem_kSkeleton (G : SimplexSet V) (k : ℕ) (σ : Simplex V) :
    σ ∈ kSkeleton G k ↔ σ ∈ G ∧ σ.card = k + 1 := by
  unfold kSkeleton
  simp [Finset.mem_filter]

theorem kSkeleton_subset (G : SimplexSet V) (k : ℕ) :
    kSkeleton G k ⊆ G := Finset.filter_subset _ _

/-- `simplexCardinality G k = (kSkeleton G k).card`. -/
theorem simplexCardinality_eq_kSkeleton_card (G : SimplexSet V) (k : ℕ) :
    simplexCardinality G k = (kSkeleton G k).card := rfl

/-- Euler–Poincaré formula: if `∅ ∉ G` and every simplex of `G` has at most `N` vertices, then
`χ(G) = ∑_{k < N} (-1)^k · |kSkeleton G k|`. -/
theorem eulerCharacteristic_eq_alt_sum_kSkeleton
    (G : SimplexSet V) (h_no_empty : ∅ ∉ G) (N : ℕ)
    (h_bound : ∀ σ ∈ G, σ.card < N + 1) :
    eulerCharacteristic G =
      (Finset.range N).sum (fun k => (-1 : ℤ)^k * ((kSkeleton G k).card : ℤ)) := by
  -- Step A: G partitions as biUnion of its kSkeletons (for k < N).
  have h_partition : G = (Finset.range N).biUnion (kSkeleton G) := by
    apply Finset.Subset.antisymm
    · intros σ hσ
      rw [Finset.mem_biUnion]
      have h_card_pos : σ.card ≥ 1 := by
        rcases Nat.eq_zero_or_pos σ.card with h0 | hpos
        · exact absurd (Finset.card_eq_zero.mp h0 ▸ hσ) h_no_empty
        · exact hpos
      refine ⟨σ.card - 1, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := h_bound σ hσ
        omega
      · rw [mem_kSkeleton]
        refine ⟨hσ, ?_⟩
        omega
    · intros σ hσ
      rw [Finset.mem_biUnion] at hσ
      obtain ⟨k, _, hσ_in⟩ := hσ
      exact ((mem_kSkeleton G k σ).mp hσ_in).1
  -- Step B: kSkeletons are pairwise disjoint, so sum_biUnion applies.
  have h_disj : Set.PairwiseDisjoint (↑(Finset.range N)) (kSkeleton G) := by
    intros i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intros σ h_i h_j
    rw [mem_kSkeleton] at h_i h_j
    have : i + 1 = j + 1 := h_i.2 ▸ h_j.2
    exact hij (by omega)
  -- Step C: expand the sum over the partition.
  unfold eulerCharacteristic
  conv_lhs => rw [h_partition]
  rw [Finset.sum_biUnion h_disj]
  apply Finset.sum_congr rfl
  intros k _
  rw [show (kSkeleton G k).sum simplexWeight
        = (kSkeleton G k).sum (fun _ => (-1 : ℤ)^k) from by
      apply Finset.sum_congr rfl
      intros σ hσ
      have h_card : σ.card = k + 1 := ((mem_kSkeleton G k σ).mp hσ).2
      exact simplexWeight_eq_neg_one_pow_dim h_card]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Euler–Poincaré formula for a finite vertex type, with the bound `N = Fintype.card V`. -/
theorem eulerCharacteristic_eq_alt_sum_fintype [Fintype V]
    (G : SimplexSet V) (h_no_empty : ∅ ∉ G) :
    eulerCharacteristic G =
      (Finset.range (Fintype.card V)).sum
        (fun k => (-1 : ℤ)^k * ((kSkeleton G k).card : ℤ)) := by
  apply eulerCharacteristic_eq_alt_sum_kSkeleton _ h_no_empty
  intros σ _
  have h_subset : σ ⊆ Finset.univ := σ.subset_univ
  have h_card_le : σ.card ≤ Finset.univ.card := Finset.card_le_card h_subset
  rw [Finset.card_univ] at h_card_le
  omega

/-- The Fermi characteristic `∏_{x ∈ G} ω(x)`. -/
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

/-- The star of `x` in `G`: the simplices of `G` that contain `x`. -/
def simplexStar (G : SimplexSet V) (x : Simplex V) : SimplexSet V :=
  G.filter (fun s => x ⊆ s)

/-- The core of `x` in `G`: the simplices of `G` contained in `x`. -/
def simplexCore (G : SimplexSet V) (x : Simplex V) : SimplexSet V :=
  G.filter (fun s => s ⊆ x)

/-- The unit sphere of `x` in `G`: the star of `x` with `x` removed. -/
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

/-! ## Closure

`complexClosure facets` is the set of nonempty subsets of the facets, the smallest set of nonempty
simplices that contains the facets and is closed under nonempty subsets. -/

/-- The union over the facets of their nonempty subsets, as Mathematica's `ComplexClosure`. -/
def complexClosure (facets : SimplexSet V) : SimplexSet V :=
  facets.biUnion (fun s => s.powerset.erase ∅)

/-- Every nonempty subset of a simplex of `G` lies in `G`. -/
def IsClosed (G : SimplexSet V) : Prop :=
  ∀ s ∈ G, ∀ t : Simplex V, t ⊆ s → t ≠ ∅ → t ∈ G

theorem mem_complexClosure {facets : SimplexSet V} {t : Simplex V} :
    t ∈ complexClosure facets ↔ ∃ s ∈ facets, t ⊆ s ∧ t ≠ ∅ := by
  simp [complexClosure, Finset.mem_biUnion, Finset.mem_erase,
        Finset.mem_powerset, and_comm]

/-- `complexClosure facets` satisfies `IsClosed`. -/
theorem complexClosure_isClosed (facets : SimplexSet V) :
    IsClosed (complexClosure facets) := by
  intro s hs t hst ht_ne
  rw [mem_complexClosure] at hs ⊢
  obtain ⟨f, hf_facets, hsf, _⟩ := hs
  exact ⟨f, hf_facets, hst.trans hsf, ht_ne⟩

/-! ## Vertex extraction -/

/-- The union of the simplices of `G`. -/
def complexVertexList (G : SimplexSet V) : Finset V :=
  G.biUnion id

@[simp] theorem mem_complexVertexList (G : SimplexSet V) (v : V) :
    v ∈ complexVertexList G ↔ ∃ s ∈ G, v ∈ s := by
  simp [complexVertexList]

/-! ## Wu characteristic

The Wu characteristic of order m sums the product of weights over m-tuples of pairwise intersecting
simplices. This section defines the cases m = 1 and m = 2, with
`ω₂(G) = ∑_{(x, y) ∈ G × G, x ∩ y ≠ ∅} ω(x) · ω(y)`. -/

/-- The Wu characteristic of order 1, `∑_{x ∈ G} ω(x)`. -/
def wuCharacteristic₁ (G : SimplexSet V) : ℤ :=
  eulerCharacteristic G

@[simp] theorem wuCharacteristic₁_eq_euler (G : SimplexSet V) :
    wuCharacteristic₁ G = eulerCharacteristic G := rfl

/-- The Wu characteristic of order 2, `ω₂(G) = ∑_{(x, y) ∈ G × G, x ∩ y ≠ ∅} ω(x) · ω(y)`. -/
def wuCharacteristic₂ (G : SimplexSet V) : ℤ :=
  ((G.product G).filter (fun p => (p.1 ∩ p.2).Nonempty)).sum
    (fun p => simplexWeight p.1 * simplexWeight p.2)

@[simp] theorem wuCharacteristic₂_empty :
    wuCharacteristic₂ (∅ : SimplexSet V) = 0 := by
  simp [wuCharacteristic₂]

/-- For a nonempty simplex `s`, `ω₂({s}) = ω(s) · ω(s)`. -/
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

/-- `ω₂(G) = χ(G)² - ∑_{(x, y) ∈ G × G, x ∩ y = ∅} ω(x) · ω(y)`. -/
theorem wuCharacteristic₂_eq_chi_sq_sub_disjoint (G : SimplexSet V) :
    wuCharacteristic₂ G = (eulerCharacteristic G)^2 -
      ((G.product G).filter (fun p => ¬ (p.1 ∩ p.2).Nonempty)).sum
        (fun p => simplexWeight p.1 * simplexWeight p.2) := by
  -- χ(G)² = (∑_x ω(x))² = ∑_{(x,y) ∈ G×G} ω(x) · ω(y)
  have h_sq : (eulerCharacteristic G)^2 =
      (G.product G).sum (fun p => simplexWeight p.1 * simplexWeight p.2) := by
    unfold eulerCharacteristic
    rw [sq, Finset.sum_mul_sum, Finset.product_eq_sprod, ← Finset.sum_product']
  rw [h_sq]
  -- Now: wu₂ G = (full sum) - (disjoint-pair sum)
  -- ↔ (full sum) = (intersecting sum) + (disjoint sum) = wu₂ G + (disjoint sum)
  unfold wuCharacteristic₂
  have h_split := Finset.sum_filter_add_sum_filter_not (G.product G)
    (fun p : Simplex V × Simplex V => (p.1 ∩ p.2).Nonempty)
    (fun p => simplexWeight p.1 * simplexWeight p.2)
  linarith

/-! ## Codimension-1 faces

`isFace x y` holds when `y ⊆ x` and `|x| = |y| + 1`. -/

/-- `y ⊆ x` and `|x| = |y| + 1`. -/
def isFace (x y : Simplex V) : Prop :=
  y ⊆ x ∧ x.card = y.card + 1

instance (x y : Simplex V) : Decidable (isFace x y) := by
  unfold isFace; infer_instance

/-- For `v ∈ x`, `x.erase v` is a codimension-1 face of `x`. -/
theorem isFace_erase {x : Simplex V} {v : V} (hv : v ∈ x) :
    isFace x (x.erase v) := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  rw [Finset.card_erase_of_mem hv]
  have : 1 ≤ x.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- If `isFace x y`, then `x \ y` has one element. -/
theorem isFace_diff_card {x y : Simplex V} (h : isFace x y) :
    (x \ y).card = 1 := by
  obtain ⟨hyx, hcard⟩ := h
  have h1 : (x \ y).card + y.card = x.card :=
    Finset.card_sdiff_add_card_eq_card hyx
  omega

/-- If `isFace x y`, then some vertex of `x` is not in `y`. -/
theorem isFace_exists_diff_vertex {x y : Simplex V} (h : isFace x y) :
    ∃ v, v ∈ x ∧ v ∉ y := by
  have hcard := isFace_diff_card h
  have hne : (x \ y).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  obtain ⟨v, hv⟩ := hne
  rw [Finset.mem_sdiff] at hv
  exact ⟨v, hv.1, hv.2⟩

/-! ## Connection matrix

Knill's connection matrix is `L(x, y) = χ(core(x) ∩ core(y))`, the Euler characteristic of the
simplices of `G` contained in both `x` and `y`. The Mathematica counterpart is
`ConnectionMatrix[G_]`
in `Infrageometry.wl` and `QuantumCalculus.wl`. -/

/-- `L(x, y) = χ(core(x) ∩ core(y))`. -/
def connectionEntry (G : SimplexSet V) (x y : Simplex V) : ℤ :=
  eulerCharacteristic (simplexCore G x ∩ simplexCore G y)

/-- `L(x, y) = L(y, x)`. -/
theorem connectionEntry_symm (G : SimplexSet V) (x y : Simplex V) :
    connectionEntry G x y = connectionEntry G y x := by
  unfold connectionEntry
  rw [Finset.inter_comm]

/-- `L(x, x) = χ(core(x))`. -/
theorem connectionEntry_self (G : SimplexSet V) (x : Simplex V) :
    connectionEntry G x x = eulerCharacteristic (simplexCore G x) := by
  unfold connectionEntry
  rw [Finset.inter_self]

/-- If no simplex of `G` is contained in both `x` and `y`, then `L(x, y) = 0`. -/
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

/-- `∑_{x ∈ G} ω(x) · L(x, x) = ∑_{x ∈ G} ω(x) · χ(core(x))`. -/
theorem sum_simplexWeight_connectionEntry_diag (G : SimplexSet V) :
    G.sum (fun x => simplexWeight x * connectionEntry G x x)
      = G.sum (fun x => simplexWeight x * eulerCharacteristic (simplexCore G x)) := by
  apply Finset.sum_congr rfl
  intros x _
  rw [connectionEntry_self]

/-! ## Green function

Knill's Green function matrix is `g(x, y) = ω(x) · ω(y) · χ(star(x) ∩ star(y))`. Knill states that
`L⁻¹ = gᵀ` and that `∑_{x, y} g(x, y) = χ(G)`; neither identity is proved in this module. The
Mathematica counterpart is `GreenFunctionMatrix[G_]` in `Infrageometry.wl` and `QuantumCalculus.wl`.
-/

/-- `g(x, y) = ω(x) · ω(y) · χ(star(x) ∩ star(y))`. -/
def greenEntry (G : SimplexSet V) (x y : Simplex V) : ℤ :=
  simplexWeight x * simplexWeight y *
    eulerCharacteristic (simplexStar G x ∩ simplexStar G y)

/-- `g(x, y) = g(y, x)`. -/
theorem greenEntry_symm (G : SimplexSet V) (x y : Simplex V) :
    greenEntry G x y = greenEntry G y x := by
  unfold greenEntry
  rw [Finset.inter_comm, mul_comm (simplexWeight x) (simplexWeight y)]

/-- `g(x, x) = ω(x) · ω(x) · χ(star(x))`. -/
theorem greenEntry_self (G : SimplexSet V) (x : Simplex V) :
    greenEntry G x x =
      simplexWeight x * simplexWeight x *
        eulerCharacteristic (simplexStar G x) := by
  unfold greenEntry
  rw [Finset.inter_self]

/-- If no simplex of `G` contains both `x` and `y`, then `g(x, y) = 0`. -/
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

/-- `ω(x) · ω(x) = 1`. -/
theorem simplexWeight_sq (s : Simplex V) :
    simplexWeight s * simplexWeight s = 1 := by
  unfold simplexWeight
  rw [neg_mul_neg, ← pow_add]
  rw [show s.card + s.card = 2 * s.card from by ring, pow_mul]
  norm_num

/-- `g(x, x) = χ(star(x))`. -/
theorem greenEntry_self_simplified (G : SimplexSet V) (x : Simplex V) :
    greenEntry G x x = eulerCharacteristic (simplexStar G x) := by
  rw [greenEntry_self, simplexWeight_sq, one_mul]

/-! ## Super-trace

The super-trace of a matrix `X` indexed by simplices is `Str[X] = ∑_{x ∈ G} ω(x) · X(x, x)`. The
Mathematica counterpart is `SuperTrace[G_, X_]` in `Infrageometry.wl` and `QuantumCalculus.wl`. -/

/-- `superTrace G X = ∑_{x ∈ G} ω(x) · X x x`. -/
def superTrace (G : SimplexSet V) (X : Simplex V → Simplex V → ℤ) : ℤ :=
  G.sum (fun x => simplexWeight x * X x x)

@[simp] theorem superTrace_empty (X : Simplex V → Simplex V → ℤ) :
    superTrace (∅ : SimplexSet V) X = 0 := by
  simp [superTrace]

theorem superTrace_insert {G : SimplexSet V} {s : Simplex V}
    (h : s ∉ G) (X : Simplex V → Simplex V → ℤ) :
    superTrace (insert s G) X = simplexWeight s * X s s + superTrace G X := by
  simp [superTrace, Finset.sum_insert h]

/-- The super-trace is additive in `X`. -/
theorem superTrace_add (G : SimplexSet V) (X Y : Simplex V → Simplex V → ℤ) :
    superTrace G (fun x y => X x y + Y x y)
      = superTrace G X + superTrace G Y := by
  unfold superTrace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros x _
  ring

/-- The super-trace of the constant matrix 1 equals `χ(G)`. -/
theorem superTrace_diag_one (G : SimplexSet V) :
    superTrace G (fun _ _ => (1 : ℤ)) = eulerCharacteristic G := by
  unfold superTrace eulerCharacteristic
  apply Finset.sum_congr rfl
  intros x _
  ring

/-! ## Signed incidence `d`

For a linearly ordered vertex type, `incidence x y` is `(-1)^i` when `y` is obtained from `x` by
removing its `i`-th vertex in sorted order, and 0 otherwise. The Mathematica counterpart is
`s[x_, y_]` in `Infrageometry.wl` and `QuantumCalculus.wl`. -/

variable [LinearOrder V]

/-- For `isFace x y`, the vertex of `x` not in `y`. -/
def missingVertex {x y : Simplex V} (h : isFace x y) : V :=
  (x \ y).min'
    (Finset.card_pos.mp (by rw [isFace_diff_card h]; omega))

/-- `missingVertex h ∈ x \ y`. -/
theorem missingVertex_mem_sdiff {x y : Simplex V} (h : isFace x y) :
    missingVertex h ∈ x \ y := by
  unfold missingVertex
  exact Finset.min'_mem _ _

/-- If `x \ y = {v}`, then `missingVertex h = v`. -/
theorem missingVertex_eq_of_sdiff_eq_singleton
    {x y : Simplex V} (h : isFace x y) {v : V}
    (h_eq : x \ y = {v}) :
    missingVertex h = v := by
  have h_mem : missingVertex h ∈ ({v} : Finset V) := by
    rw [← h_eq]; exact missingVertex_mem_sdiff h
  exact Finset.mem_singleton.mp h_mem

/-- For `w ∈ x`, the missing vertex of `x.erase w` is `w`. -/
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

/-- `d(x, y) = (-1)^i` if `y` is `x` with its `i`-th vertex in sorted order removed, and 0
otherwise. -/
def incidence (x y : Simplex V) : ℤ :=
  if h : isFace x y then
    (-1 : ℤ) ^ (x.sort (· ≤ ·)).idxOf (missingVertex h)
  else 0

/-- If `y` is not a codimension-1 face of `x`, then `d(x, y) = 0`. -/
theorem incidence_eq_zero_of_not_isFace {x y : Simplex V}
    (h : ¬ isFace x y) :
    incidence x y = 0 := by
  unfold incidence
  rw [dif_neg h]

/-- `d(x, x) = 0`. -/
theorem incidence_self (x : Simplex V) : incidence x x = 0 := by
  apply incidence_eq_zero_of_not_isFace
  intro h
  obtain ⟨_, hcard⟩ := h
  omega

/-- `d(x, y) ≠ 0` if and only if `isFace x y`. -/
theorem incidence_ne_zero_iff_isFace (x y : Simplex V) :
    incidence x y ≠ 0 ↔ isFace x y := by
  refine ⟨fun h_ne => ?_, fun h_isFace => ?_⟩
  · by_contra h_not
    exact h_ne (incidence_eq_zero_of_not_isFace h_not)
  · unfold incidence
    rw [dif_pos h_isFace]
    exact pow_ne_zero _ (by norm_num)

/-- `d(x, y) · d(x, y)` is 1 if `isFace x y` and 0 otherwise. -/
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

/-! ## Dirac and Hodge matrices

The Dirac matrix is `dirac x y = incidence x y + incidence y x`. On a finite simplex set `G`, the
Hodge matrix is `hodgeOnG G x y = ∑_{z ∈ G} dirac x z · dirac z y`. The Mathematica counterparts are
`DiracHodgeMatrix[G_]` and `HodgeMatrix[G_]` in `Infrageometry.wl`. -/

/-- `D(x, y) = d(x, y) + d(y, x)`. -/
def dirac (x y : Simplex V) : ℤ :=
  incidence x y + incidence y x

/-- `D(x, y) = D(y, x)`. -/
theorem dirac_symm (x y : Simplex V) : dirac x y = dirac y x := by
  unfold dirac; ring

/-- `D(x, x) = 0`. -/
@[simp] theorem dirac_self (x : Simplex V) : dirac x x = 0 := by
  unfold dirac
  rw [incidence_self]
  ring

/-- If neither of `x`, `y` is a codimension-1 face of the other, then `D(x, y) = 0`. -/
theorem dirac_eq_zero_of_no_face {x y : Simplex V}
    (hxy : ¬ isFace x y) (hyx : ¬ isFace y x) :
    dirac x y = 0 := by
  unfold dirac
  rw [incidence_eq_zero_of_not_isFace hxy,
      incidence_eq_zero_of_not_isFace hyx]
  ring

/-- `H(x, y) = ∑_{z ∈ G} D(x, z) · D(z, y)`, the square of `D` with indices in `G`. -/
def hodgeOnG (G : SimplexSet V) (x y : Simplex V) : ℤ :=
  G.sum (fun z => dirac x z * dirac z y)

/-- `H(x, y) = H(y, x)`. -/
theorem hodgeOnG_symm (G : SimplexSet V) (x y : Simplex V) :
    hodgeOnG G x y = hodgeOnG G y x := by
  unfold hodgeOnG
  apply Finset.sum_congr rfl
  intros z _
  rw [dirac_symm x z, dirac_symm z y]
  ring

/-- For `f : Simplex V → ℤ`,
`∑_{x, y ∈ G} f(x) · H(x, y) · f(y) = ∑_{z ∈ G} (∑_{x ∈ G} f(x) · D(x, z))²`. -/
theorem hodgeOnG_double_sum_eq_sum_squares (G : SimplexSet V) (f : Simplex V → ℤ) :
    G.sum (fun x => f x * G.sum (fun y => hodgeOnG G x y * f y))
      = G.sum (fun z => (G.sum (fun x => f x * dirac x z))^2) := by
    -- LHS triple sum: ∑_x f x · ∑_y H(x,y) · f y = ∑_x ∑_y ∑_z f x · D(x,z) · D(z,y) · f y
    -- Swap to put z outermost, then refactor as (∑_x ...)·(∑_y ...) and use D symmetry.
    calc G.sum (fun x => f x * G.sum (fun y => hodgeOnG G x y * f y))
        = G.sum (fun x => G.sum (fun y => G.sum (fun z =>
              f x * dirac x z * dirac z y * f y))) := by
          apply Finset.sum_congr rfl; intros x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intros y _
          unfold hodgeOnG
          rw [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl; intros z _
          ring
      _ = G.sum (fun x => G.sum (fun z => G.sum (fun y =>
              f x * dirac x z * dirac z y * f y))) := by
          apply Finset.sum_congr rfl; intros x _
          exact Finset.sum_comm
      _ = G.sum (fun z => G.sum (fun x => G.sum (fun y =>
              f x * dirac x z * dirac z y * f y))) := Finset.sum_comm
      _ = G.sum (fun z => (G.sum (fun x => f x * dirac x z))^2) := by
          apply Finset.sum_congr rfl; intros z _
          rw [sq, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intros x _
          apply Finset.sum_congr rfl; intros y _
          rw [dirac_symm z y]; ring

/-- For `f : Simplex V → ℤ`, `∑_{x, y ∈ G} f(x) · H(x, y) · f(y) ≥ 0`. -/
theorem hodgeOnG_psd (G : SimplexSet V) (f : Simplex V → ℤ) :
    0 ≤ G.sum (fun x => f x * G.sum (fun y => hodgeOnG G x y * f y)) := by
  rw [hodgeOnG_double_sum_eq_sum_squares]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- `H(x, x) = ∑_{z ∈ G} D(x, z)²`. -/
theorem hodgeOnG_diag_eq_sum_dirac_sq (G : SimplexSet V) (x : Simplex V) :
    hodgeOnG G x x = G.sum (fun z => (dirac x z)^2) := by
  unfold hodgeOnG
  apply Finset.sum_congr rfl
  intros z _
  rw [dirac_symm z x, sq]

/-- `H(x, x) ≥ 0`. -/
theorem hodgeOnG_diag_nonneg (G : SimplexSet V) (x : Simplex V) :
    0 ≤ hodgeOnG G x x := by
  rw [hodgeOnG_diag_eq_sum_dirac_sq]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- `∑_{x ∈ G} f(x) · D(x, z) = 0` for every `z ∈ G`. -/
def isDiracKernel (G : SimplexSet V) (f : Simplex V → ℤ) : Prop :=
  ∀ z ∈ G, G.sum (fun x => f x * dirac x z) = 0

/-- `∑_{x, y ∈ G} f(x) · H(x, y) · f(y) = 0` if and only if `isDiracKernel G f`. -/
theorem hodgeOnG_dirichlet_zero_iff_isDiracKernel
    (G : SimplexSet V) (f : Simplex V → ℤ) :
    G.sum (fun x => f x * G.sum (fun y => hodgeOnG G x y * f y)) = 0
      ↔ isDiracKernel G f := by
  unfold isDiracKernel
  rw [hodgeOnG_double_sum_eq_sum_squares]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  refine ⟨fun h z hz => ?_, fun h z hz => ?_⟩
  · exact sq_eq_zero_iff.mp (h z hz)
  · rw [h z hz]; ring

/-- `hodgeOnG_dirichlet_zero_iff_isDiracKernel` with `isDiracKernel` unfolded. -/
theorem hodgeOnG_dirichlet_zero_iff_dirac_kernel
    (G : SimplexSet V) (f : Simplex V → ℤ) :
    G.sum (fun x => f x * G.sum (fun y => hodgeOnG G x y * f y)) = 0
      ↔ ∀ z ∈ G, G.sum (fun x => f x * dirac x z) = 0 :=
  hodgeOnG_dirichlet_zero_iff_isDiracKernel G f

/-! ## The identity `d ∘ d = 0`

`dSquared x z = ∑_{y ⊆ x} d(x, y) · d(y, z)`. For `z ⊆ x` with `|x| = |z| + 2` and
`x \ z = {a, b}`, the two nonzero terms are those for `y = x.erase a` and `y = x.erase b` and have
opposite signs. -/

/-- `(d ∘ d)(x, z) = ∑_{y ⊆ x} d(x, y) · d(y, z)`. -/
def dSquared (x z : Simplex V) : ℤ :=
  x.powerset.sum (fun y => incidence x y * incidence y z)

/-- If `|x| ≠ |z| + 2`, then `(d ∘ d)(x, z) = 0`. -/
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

/-- If `z ⊄ x`, then `(d ∘ d)(x, z) = 0`. -/
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

/-- For `w ∈ x`, `d(x, x.erase w) = (-1)^i` where `i` is the position of `w` in `x` sorted. -/
theorem incidence_erase (x : Simplex V) (w : V) (hw : w ∈ x) :
    incidence x (x.erase w) = (-1 : ℤ) ^ (x.sort (· ≤ ·)).idxOf w := by
  unfold incidence
  rw [dif_pos (isFace_erase hw), missingVertex_erase hw]

/-! ### Sign cancellation

For `|x| = |z| + 2`, `z ⊆ x` and `x \ z = {a, b}` with `a` at position `i` and `b` at position
`j > i`
in sorted `x`, the term for `x.erase a` is `(-1)^i · (-1)^(j-1)`, since `b` is at position `j - 1`
in
sorted `x.erase a`. The term for `x.erase b` is `(-1)^j · (-1)^i`. The two terms sum to 0. -/

/-- For `z ⊆ x` and `y ⊆ x`, if `y` is not `x.erase w` for any `w ∈ x \ z`, then
`d(x, y) · d(y, z) = 0`. -/
theorem dSquared_summand_zero_unless (x z : Simplex V)
    (hsub : z ⊆ x) (y : Simplex V) (hy : y ⊆ x)
    (h_not : ¬ ∃ w, w ∈ x \ z ∧ y = x.erase w) :
    incidence x y * incidence y z = 0 := by
  by_cases hxy : isFace x y
  · by_cases hyz : isFace y z
    · -- Derive y = x.erase (missingVertex hxy), then missingVertex ∈ x \ z
      exfalso
      apply h_not
      set v := missingVertex hxy with hv_def
      have hv_mem : v ∈ x \ y := missingVertex_mem_sdiff hxy
      rw [Finset.mem_sdiff] at hv_mem
      have hv_x : v ∈ x := hv_mem.1
      have hv_ny : v ∉ y := hv_mem.2
      -- v ∉ z because z ⊆ y and v ∉ y
      have hv_nz : v ∉ z := fun hvz => hv_ny (hyz.1 hvz)
      refine ⟨v, Finset.mem_sdiff.mpr ⟨hv_x, hv_nz⟩, ?_⟩
      -- y = x.erase v: from |x \ y| = 1 + v ∈ x \ y forces x \ y = {v}
      have h_diff_card : (x \ y).card = 1 := isFace_diff_card hxy
      have h_xy_singleton : x \ y = {v} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_sdiff.mpr ⟨hv_x, hv_ny⟩, fun u hu => ?_⟩
        by_contra hne
        have h_two_subset : ({v, u} : Finset V) ⊆ x \ y := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · exact Finset.mem_sdiff.mpr ⟨hv_x, hv_ny⟩
          · rw [Finset.mem_singleton] at hw'
            subst hw'
            exact hu
        have h_card_two : ({v, u} : Finset V).card = 2 := by
          rw [Finset.card_insert_of_notMem]
          · simp
          · simpa [Finset.mem_singleton] using fun h => hne h.symm
        have h_le := Finset.card_le_card h_two_subset
        rw [h_card_two, h_diff_card] at h_le
        omega
      -- Now use h_xy_singleton to show y = x.erase v
      ext u
      simp only [Finset.mem_erase]
      constructor
      · intro hu
        refine ⟨?_, hy hu⟩
        intro huv
        subst huv
        exact hv_ny hu
      · rintro ⟨hne, hux⟩
        by_contra hny
        have h_in_diff : u ∈ x \ y := Finset.mem_sdiff.mpr ⟨hux, hny⟩
        rw [h_xy_singleton, Finset.mem_singleton] at h_in_diff
        exact hne h_in_diff
    · rw [incidence_eq_zero_of_not_isFace hyz, mul_zero]
  · rw [incidence_eq_zero_of_not_isFace hxy, zero_mul]

/-! ### Positions in sorted lists after erasing an element -/

/-- Sorting `s.erase w` gives the sorted list of `s` with `w` erased. -/
theorem Finset.sort_erase (s : Finset V) (w : V) :
    (s.erase w).sort (· ≤ ·) = (s.sort (· ≤ ·)).erase w := by
  have h_sub : List.Sublist ((s.sort (· ≤ ·)).erase w) (s.sort (· ≤ ·)) :=
    List.erase_sublist
  have h_pair_l : List.Pairwise (· ≤ ·) ((s.erase w).sort (· ≤ ·)) :=
    Finset.pairwise_sort _ _
  have h_pair_r : List.Pairwise (· ≤ ·) ((s.sort (· ≤ ·)).erase w) :=
    (Finset.pairwise_sort _ _).sublist h_sub
  have h_perm : ((s.erase w).sort (· ≤ ·)).Perm ((s.sort (· ≤ ·)).erase w) := by
    rw [← Multiset.coe_eq_coe, Finset.sort_eq, Finset.erase_val,
        ← Multiset.coe_erase, Finset.sort_eq]
  exact List.Perm.eq_of_pairwise' h_pair_l h_pair_r h_perm

/-- If `u` occurs before `w` in `l`, then erasing `w` leaves the position of `u` unchanged. -/
theorem List.idxOf_erase_of_idxOf_lt {α : Type*} [DecidableEq α]
    {l : List α} {w u : α} (h : l.idxOf u < l.idxOf w) :
    (l.erase w).idxOf u = l.idxOf u := by
  induction l with
  | nil => simp [List.idxOf] at h
  | cons head tail ih =>
    by_cases h_hu : head = u
    · subst h_hu
      have h_ne_w : head ≠ w := by
        intro he; subst he; simp at h
      have h_beq_w : (head == w) = false := beq_eq_false_iff_ne.mpr h_ne_w
      simp [List.erase_cons, h_beq_w]
    · by_cases h_hw : head = w
      · subst h_hw
        have h_beq_u : (head == u) = false := beq_eq_false_iff_ne.mpr h_hu
        simp [List.idxOf_cons, h_beq_u] at h
      · have h_beq_u : (head == u) = false := beq_eq_false_iff_ne.mpr h_hu
        have h_beq_w : (head == w) = false := beq_eq_false_iff_ne.mpr h_hw
        simp [List.erase_cons, h_beq_w, List.idxOf_cons, h_beq_u]
        simp [List.idxOf_cons, h_beq_u, h_beq_w] at h
        exact ih (by omega)

/-- If `w` occurs before `u` in `l`, then erasing `w` decreases the position of `u` by one. -/
theorem List.idxOf_erase_of_idxOf_gt {α : Type*} [DecidableEq α]
    {l : List α} {w u : α} (h : l.idxOf w < l.idxOf u) :
    (l.erase w).idxOf u + 1 = l.idxOf u := by
  induction l with
  | nil => simp [List.idxOf] at h
  | cons head tail ih =>
    by_cases h_hw : head = w
    · subst h_hw
      have h_ne_u : head ≠ u := by
        intro he; subst he; simp at h
      have h_beq_u : (head == u) = false := beq_eq_false_iff_ne.mpr h_ne_u
      simp [List.erase_cons_head, List.idxOf_cons, h_beq_u]
    · by_cases h_hu : head = u
      · subst h_hu
        have h_beq_w : (head == w) = false := beq_eq_false_iff_ne.mpr h_hw
        simp [List.idxOf_cons, h_beq_w] at h
      · have h_beq_u : (head == u) = false := beq_eq_false_iff_ne.mpr h_hu
        have h_beq_w : (head == w) = false := beq_eq_false_iff_ne.mpr h_hw
        simp [List.erase_cons, h_beq_w, List.idxOf_cons, h_beq_u]
        simp [List.idxOf_cons, h_beq_u, h_beq_w] at h
        have ih' : (tail.erase w).idxOf u + 1 = tail.idxOf u := ih (by omega)
        omega

/-! ### Restriction of the sum to `x \ z` -/

/-- For `z ⊆ x`, `(d ∘ d)(x, z) = ∑_{w ∈ x \ z} d(x, x.erase w) · d(x.erase w, z)`. -/
theorem dSquared_eq_sum_diff (x z : Simplex V) (hsub : z ⊆ x) :
    dSquared x z = (x \ z).sum
      (fun w => incidence x (x.erase w) * incidence (x.erase w) z) := by
  unfold dSquared
  have h_inj : Set.InjOn (fun w => x.erase w) (x \ z : Finset V) := by
    intro w₁ hw₁ w₂ _ heq
    by_contra hne
    have h_mem_x : w₁ ∈ x := by
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hw₁
      exact hw₁.1
    have hw₁_in : w₁ ∈ x.erase w₂ := Finset.mem_erase.mpr ⟨hne, h_mem_x⟩
    have heq' : x.erase w₁ = x.erase w₂ := heq
    rw [← heq'] at hw₁_in
    exact (Finset.notMem_erase w₁ x) hw₁_in
  have h_image_sub : (x \ z).image (fun w => x.erase w) ⊆ x.powerset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨w, _, rfl⟩ := hy
    rw [Finset.mem_powerset]
    exact Finset.erase_subset _ _
  rw [← Finset.sum_image (s := x \ z) (g := fun w => x.erase w)
        (f := fun y => incidence x y * incidence y z) h_inj]
  symm
  apply Finset.sum_subset h_image_sub
  intro y hy_pow hy_notin
  rw [Finset.mem_powerset] at hy_pow
  apply dSquared_summand_zero_unless x z hsub y hy_pow
  intro ⟨w, hw_diff, h_y_eq⟩
  apply hy_notin
  rw [Finset.mem_image]
  exact ⟨w, hw_diff, h_y_eq.symm⟩

/-! ### `d ∘ d = 0` -/

/-- `(d ∘ d)(x, z) = 0` for all simplices `x`, `z`. -/
theorem dSquared_eq_zero (x z : Simplex V) : dSquared x z = 0 := by
  by_cases hsub : z ⊆ x
  swap
  · exact dSquared_eq_zero_of_not_subset hsub
  by_cases hcard : x.card = z.card + 2
  swap
  · exact dSquared_eq_zero_of_card_ne hcard
  -- Main case: z ⊆ x and |x| = |z| + 2
  rw [dSquared_eq_sum_diff x z hsub]
  have h_diff_card : (x \ z).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard]; omega
  obtain ⟨a, b, hab, h_xz_eq⟩ := Finset.card_eq_two.mp h_diff_card
  rw [h_xz_eq, Finset.sum_pair hab]
  -- Membership facts
  have ha_mem : a ∈ x \ z := by rw [h_xz_eq]; simp
  have hb_mem : b ∈ x \ z := by rw [h_xz_eq]; simp
  have ha_x : a ∈ x := (Finset.mem_sdiff.mp ha_mem).1
  have ha_nz : a ∉ z := (Finset.mem_sdiff.mp ha_mem).2
  have hb_x : b ∈ x := (Finset.mem_sdiff.mp hb_mem).1
  have hb_nz : b ∉ z := (Finset.mem_sdiff.mp hb_mem).2
  -- isFace facts and missingVertex computations
  have h_face_a : isFace (x.erase a) z := by
    refine ⟨fun v hv => ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨fun hva => ?_, hsub hv⟩
      subst hva; exact ha_nz hv
    · rw [Finset.card_erase_of_mem ha_x, hcard]; omega
  have h_face_b : isFace (x.erase b) z := by
    refine ⟨fun v hv => ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨fun hvb => ?_, hsub hv⟩
      subst hvb; exact hb_nz hv
    · rw [Finset.card_erase_of_mem hb_x, hcard]; omega
  have h_mv_a : missingVertex h_face_a = b := by
    apply missingVertex_eq_of_sdiff_eq_singleton
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hva, hvx⟩, hvz⟩
      have hvxz : v ∈ x \ z := Finset.mem_sdiff.mpr ⟨hvx, hvz⟩
      rw [h_xz_eq] at hvxz
      rcases Finset.mem_insert.mp hvxz with rfl | hvb_eq
      · exact absurd rfl hva
      · exact Finset.mem_singleton.mp hvb_eq
    · rintro rfl
      exact ⟨⟨Ne.symm hab, hb_x⟩, hb_nz⟩
  have h_mv_b : missingVertex h_face_b = a := by
    apply missingVertex_eq_of_sdiff_eq_singleton
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hvb, hvx⟩, hvz⟩
      have hvxz : v ∈ x \ z := Finset.mem_sdiff.mpr ⟨hvx, hvz⟩
      rw [h_xz_eq] at hvxz
      rcases Finset.mem_insert.mp hvxz with rfl | hva_eq
      · rfl
      · rw [Finset.mem_singleton] at hva_eq
        subst hva_eq
        exact absurd rfl hvb
    · rintro rfl
      exact ⟨⟨hab, ha_x⟩, ha_nz⟩
  -- Compute incidence x (x.erase a/b)
  rw [incidence_erase x a ha_x, incidence_erase x b hb_x]
  -- Unfold incidence (x.erase a/b) z
  unfold incidence
  rw [dif_pos h_face_a, dif_pos h_face_b]
  rw [h_mv_a, h_mv_b]
  -- Reduce sort of erase to erase of sort
  rw [Finset.sort_erase, Finset.sort_erase]
  -- Now: (-1)^idx_x(a) * (-1)^idx_{(sort x).erase a}(b)
  --    + (-1)^idx_x(b) * (-1)^idx_{(sort x).erase b}(a) = 0
  set L := x.sort (· ≤ ·) with hL_def
  set i := L.idxOf a with hi_def
  set j := L.idxOf b with hj_def
  -- a ∈ L and b ∈ L since a, b ∈ x and L is sort x
  have hL_a : a ∈ L := by rw [hL_def, Finset.mem_sort]; exact ha_x
  have hL_b : b ∈ L := by rw [hL_def, Finset.mem_sort]; exact hb_x
  have h_inj : i ≠ j := by
    intro h_eq
    have : a = b := (List.idxOf_inj hL_a).mp (by rw [← hi_def, ← hj_def]; exact h_eq)
    exact hab this
  rcases lt_or_gt_of_ne h_inj with h_lt | h_gt
  · -- i < j: (L.erase a).idxOf b + 1 = j;  (L.erase b).idxOf a = i
    have h_b_pos : (L.erase a).idxOf b + 1 = j :=
      List.idxOf_erase_of_idxOf_gt (by rw [← hi_def, ← hj_def]; exact h_lt)
    have h_a_pos : (L.erase b).idxOf a = i :=
      List.idxOf_erase_of_idxOf_lt (by rw [← hi_def, ← hj_def]; exact h_lt)
    rw [h_a_pos]
    set p := (L.erase a).idxOf b with hp_def
    -- Goal: (-1)^i * (-1)^p + (-1)^j * (-1)^i = 0
    -- with p + 1 = j, i.e., j = p + 1
    have hj_eq : j = p + 1 := h_b_pos.symm
    rw [hj_eq]
    -- (-1)^i * (-1)^p + (-1)^(p+1) * (-1)^i
    -- = (-1)^i * (-1)^p + (-1)^p * (-1) * (-1)^i
    -- = (-1)^i * (-1)^p - (-1)^i * (-1)^p
    -- = 0
    ring
  · -- i > j: the same argument with a and b swapped.
    -- (L.erase a).idxOf b = j;  (L.erase b).idxOf a + 1 = i
    have h_b_pos : (L.erase a).idxOf b = j :=
      List.idxOf_erase_of_idxOf_lt (by rw [← hi_def, ← hj_def]; exact h_gt)
    have h_a_pos : (L.erase b).idxOf a + 1 = i :=
      List.idxOf_erase_of_idxOf_gt (by rw [← hi_def, ← hj_def]; exact h_gt)
    rw [h_b_pos]
    set q := (L.erase b).idxOf a with hq_def
    have hi_eq : i = q + 1 := h_a_pos.symm
    rw [hi_eq]
    ring

/-! ### `dᵀ ∘ dᵀ = 0`

With `dᵀ x y = d(y, x)`, the sum `∑_{y ⊆ z} d(y, x) · d(z, y)` is `(d ∘ d)(z, x)`, which is 0. -/

/-- `∑_{y ⊆ z} d(y, x) · d(z, y) = 0`. -/
theorem dStarSquared_eq_zero (x z : Simplex V) :
    (z.powerset.sum (fun y => incidence y x * incidence z y)) = 0 := by
  -- Reindex: this equals dSquared z x = 0.
  have : z.powerset.sum (fun y => incidence y x * incidence z y)
       = z.powerset.sum (fun y => incidence z y * incidence y x) := by
    apply Finset.sum_congr rfl
    intros y _
    ring
  rw [this]
  exact dSquared_eq_zero z x

/-! ## Vertex angle defect

For a vertex `x`, `T(x)` is the number of triangles of `G` containing `x`, and the integer angle
defect is `6 − T(x)`. Multiplying by `π/3` gives the angle defect `K(x) = (6 − T(x)) · π/3` of an
equilateral triangulation (Higuchi 2001, Knill 2011). This section defines these quantities and
proves two bounds. -/

/-- The simplices of `G` with three vertices that contain `x`. -/
def vertexStarTriangles (G : SimplexSet V) (x : V) : SimplexSet V :=
  G.filter (fun s => s.card = 3 ∧ x ∈ s)

/-- `T(x)`, the number of triangles of `G` containing `x`. -/
def vertexTriangleCount (G : SimplexSet V) (x : V) : ℕ :=
  (vertexStarTriangles G x).card

/-- The integer angle defect `6 − T(x)`. -/
def formanAngleDefectZ (G : SimplexSet V) (x : V) : ℤ :=
  6 - (vertexTriangleCount G x : ℤ)

/-- `s ∈ vertexStarTriangles G x` if and only if `s ∈ G`, `s` has three vertices and `x ∈ s`. -/
@[simp] theorem mem_vertexStarTriangles (G : SimplexSet V) (x : V)
    (s : Simplex V) :
    s ∈ vertexStarTriangles G x ↔ s ∈ G ∧ s.card = 3 ∧ x ∈ s := by
  simp [vertexStarTriangles]

/-- `T(x)` is at most the number of triangles of `G`. -/
theorem vertexTriangleCount_le (G : SimplexSet V) (x : V) :
    vertexTriangleCount G x ≤ simplexCardinality G 2 := by
  unfold vertexTriangleCount vertexStarTriangles simplexCardinality
  apply Finset.card_le_card
  intros s hs
  rw [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, by omega⟩

/-- `6 − T(x) ≤ 6`. -/
theorem formanAngleDefectZ_le_six (G : SimplexSet V) (x : V) :
    formanAngleDefectZ G x ≤ 6 := by
  unfold formanAngleDefectZ
  have : (0 : ℤ) ≤ (vertexTriangleCount G x : ℤ) := Int.natCast_nonneg _
  linarith

end Knill
end InfraFormalization
