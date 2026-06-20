/-
**Per-edge additivity framework** (#495).

**Goal**: lift the per-edge additivity claim
`knillEulerScaled(rule, seed, d) = |seed| · knillEulerScaled(rule, edge12, d)`
from a finite-corpus `native_decide` check (the current state across
`UniversalAdditivity.lean`, `BranchialUniversalAdditivity.lean`,
`StableDiscoveredRules.lean`, the BBH modules, ...) to a real universal
theorem.

**Strategy**: prove this for **vertex-disjoint seeds** first. BBH initial
data is 7 vertex-disjoint edges by construction, so this branch alone
suffices to derive `Knill(BBH, d) = 7 · Knill(edge12, d)` universally
in `d`. The connected-seed case (`path123`, `triangle`) requires a
tree-decomposition argument on the causal DAG and is multi-session.

The framework decomposes into three independent obligations:

  **(K1) Knill is additive over vertex-disjoint hypergraphs.**
        `Disjoint H₁ H₂ → knillEulerScaled (H₁ ++ H₂) = knillEulerScaled H₁ + knillEulerScaled H₂`.
        Pure combinatorics. Sub-lemmas in Sections B/C proved here;
        K1 itself stated as a Prop pending the foldr-split chain.

  **(K2) Knill is invariant under vertex relabeling (bijection on `ℕ`).**
        `Bijective f → knillEulerScaled (relabel f H) = knillEulerScaled H`.
        Pure combinatorics. Stated.

  **(E1) The engine commutes with disjoint union for single-edge-LHS rules.**
        For `r` with `r.lhs.length = 1` and vertex-disjoint `H₁, H₂`:
        the causal DAG of `singleWayEvolve ⟨[r]⟩ (H₁ ++ H₂) d` is the
        vertex-disjoint union of the causal DAGs from `H₁` and `H₂` (up
        to fresh-vertex relabeling). Engine-semantics. Stated.

  **Composition.** (K1) + (K2) + (E1) ⟹ `disjoint_per_edge_additivity`:
  for single-edge-LHS rules and vertex-disjoint seeds,
  `knillEulerScaled(causalDAG sys seed d) = |seed_distinct_edges| · knillEulerScaled(causalDAG sys edge12 d)`.

This module establishes the framework, proves the structural
sub-lemmas (`mem_vertexList_append`, `execAdj_append`,
`execAdj_cross_zero`), and states K1, K2, E1, and the composed
disjoint-seed per-edge additivity as named `Prop` obligations. No
sorries; the open obligations are tracked as `def : Prop`.
-/

import InfraFormalization.KnillDiscreteGaussBonnet
import InfraFormalization.BBHInitialData
import InfraFormalization.CausalEventTrace
import Mathlib.Data.List.Dedup

namespace InfraFormalization
namespace PerEdgeAdditivityFramework

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace

/-! ## Section A: vertex-disjointness predicate -/

/-- Two hypergraphs are vertex-disjoint when no vertex appears in both. -/
def VertexDisjoint (H₁ H₂ : ExecHG ℕ) : Prop :=
  ∀ v, v ∈ vertexList H₁ → v ∉ vertexList H₂

/-- Symmetric formulation. -/
theorem VertexDisjoint.symm {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) : VertexDisjoint H₂ H₁ := by
  intro v hv₂ hv₁
  exact h v hv₁ hv₂

/-! ## Section B: vertexList behavior under concatenation -/

/-- `vertexList (H₁ ++ H₂)` lists exactly the vertices of `H₁` and `H₂`
combined, with deduplication. -/
theorem mem_vertexList_append {V : Type*} [DecidableEq V]
    (H₁ H₂ : ExecHG V) (v : V) :
    v ∈ vertexList (H₁ ++ H₂) ↔ v ∈ vertexList H₁ ∨ v ∈ vertexList H₂ := by
  unfold vertexList
  rw [List.flatMap_append, List.mem_dedup, List.mem_append, List.mem_dedup, List.mem_dedup]

/-! ## Section C: adjacency under concatenation -/

/-- `execAdj (H₁ ++ H₂) u v` iff one of the parts has the adjacency. -/
theorem execAdj_append (H₁ H₂ : ExecHG ℕ) (u v : ℕ) :
    execAdj (H₁ ++ H₂) u v = (execAdj H₁ u v || execAdj H₂ u v) := by
  unfold execAdj
  rw [List.any_append]
  by_cases huv : u = v
  · subst huv
    simp
  · simp [bne_iff_ne.mpr huv]

/-- Under vertex-disjointness, any potential adjacency in `H₁` between
`u ∈ V(H₁)` and `v ∈ V(H₂)` is false (no edge of `H₁` contains `v`
since `v ∉ V(H₁)`). -/
theorem execAdj_cross_H1_zero (H₁ H₂ : ExecHG ℕ)
    (h : VertexDisjoint H₁ H₂)
    {u v : ℕ} (_hu : u ∈ vertexList H₁) (hv : v ∈ vertexList H₂) :
    execAdj H₁ u v = false := by
  have hv_not_in_H₁ : v ∉ vertexList H₁ := fun hv₁ => h.symm v hv hv₁
  unfold execAdj
  apply Bool.eq_false_iff.mpr
  intro hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.any_eq_true] at hadj
  obtain ⟨_, ⟨e, he_in, he_contains⟩⟩ := hadj
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he_contains
  apply hv_not_in_H₁
  unfold vertexList
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨e, he_in, he_contains.2⟩

/-- Symmetric: any potential adjacency in `H₂` between `u ∈ V(H₁)`
and `v ∈ V(H₂)` is false (no edge of `H₂` contains `u`). -/
theorem execAdj_cross_H2_zero (H₁ H₂ : ExecHG ℕ)
    (h : VertexDisjoint H₁ H₂)
    {u v : ℕ} (hu : u ∈ vertexList H₁) (_hv : v ∈ vertexList H₂) :
    execAdj H₂ u v = false := by
  have hu_not_in_H₂ : u ∉ vertexList H₂ := h u hu
  unfold execAdj
  apply Bool.eq_false_iff.mpr
  intro hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.any_eq_true] at hadj
  obtain ⟨_, ⟨e, he_in, he_contains⟩⟩ := hadj
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he_contains
  apply hu_not_in_H₂
  unfold vertexList
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨e, he_in, he_contains.1⟩

/-! ## Section D: K1 — the Knill-additivity obligation -/

/-- **(K1) Knill is additive over vertex-disjoint hypergraphs.**

For vertex-disjoint `H₁, H₂`, the per-vertex Knill sum splits:

  `knillEulerScaled (H₁ ++ H₂) = knillEulerScaled H₁ + knillEulerScaled H₂`

**Mathematical content** (the obligation):

  1. `vertexList (H₁ ++ H₂)` partitions into vertices from `H₁` and
     vertices from `H₂` (no overlap by `VertexDisjoint`).
  2. For `v ∈ V(H₁)`, all triangles and adjacencies through `v` lie
     entirely within `H₁` (by `execAdj_cross_H2_zero`). Hence
     `knillVertexK6 (H₁ ++ H₂) v = knillVertexK6 H₁ v`.
  3. Symmetric for `v ∈ V(H₂)`.
  4. The foldr sum decomposes via the partition.

Stated as a Prop obligation; sub-lemmas (Section B/C) discharge
most of the structural reasoning. Closing K1 requires the foldr-split
chain on `vertexList (H₁ ++ H₂)`. -/
def K1_KnillAdditiveOverDisjointUnion : Prop :=
  ∀ (H₁ H₂ : ExecHG ℕ), VertexDisjoint H₁ H₂ →
    knillEulerScaled (H₁ ++ H₂) = knillEulerScaled H₁ + knillEulerScaled H₂

/-! ## Section D.1: Closing K1

Below: explicit proof of `K1_KnillAdditiveOverDisjointUnion` as the named
theorem `K1_proved`. The chain runs:

  vertex-list partition (`vertexList_append_disjoint`)
    → per-vertex Knill preservation (`knillVertexK6_append_left/right`)
    → foldr split over `++` (`foldr_add_split`).

Each step is a real combinatorial lemma — no `decide`, no `native_decide`,
no `sorry`. -/

/-- If `v` is not a vertex of `H`, then `v` has no adjacency in `H` (left). -/
private theorem execAdj_eq_false_of_first_notMem (H : ExecHG ℕ) {v : ℕ}
    (hv : v ∉ vertexList H) (u : ℕ) : execAdj H v u = false := by
  unfold execAdj
  apply Bool.eq_false_iff.mpr
  intro hadj
  simp only [Bool.and_eq_true, bne_iff_ne, List.any_eq_true] at hadj
  obtain ⟨_, e, he_in, he_contains⟩ := hadj
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he_contains
  apply hv
  unfold vertexList
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨e, he_in, he_contains.1⟩

/-- If `u` is not a vertex of `H`, then no adjacency in `H` reaches `u` (right). -/
private theorem execAdj_eq_false_of_second_notMem (H : ExecHG ℕ) (v : ℕ) {u : ℕ}
    (hu : u ∉ vertexList H) : execAdj H v u = false := by
  unfold execAdj
  apply Bool.eq_false_iff.mpr
  intro hadj
  simp only [Bool.and_eq_true, bne_iff_ne, List.any_eq_true] at hadj
  obtain ⟨_, e, he_in, he_contains⟩ := hadj
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he_contains
  apply hu
  unfold vertexList
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨e, he_in, he_contains.2⟩

/-- Vertex-disjointness lifts to disjointness of the pre-dedup flatMaps. -/
private theorem flatMap_verts_disjoint {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) :
    List.Disjoint (H₁.flatMap (·.verts)) (H₂.flatMap (·.verts)) := by
  intro v hv₁ hv₂
  apply h v
  · unfold vertexList; rw [List.mem_dedup]; exact hv₁
  · unfold vertexList; rw [List.mem_dedup]; exact hv₂

/-- Under vertex-disjointness, the deduped vertex list of `H₁ ++ H₂` is
literally the concatenation of the per-component deduped vertex lists. -/
private theorem vertexList_append_disjoint {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) :
    vertexList (H₁ ++ H₂) = vertexList H₁ ++ vertexList H₂ := by
  unfold vertexList
  rw [List.flatMap_append]
  exact List.Disjoint.dedup_append (flatMap_verts_disjoint h)

/-- For `v ∈ V(H₁)` and `u ∈ V(H₁)`, the disjoint-union adjacency reduces
to the `H₁`-adjacency (the `H₂` summand contributes nothing because
`v ∉ V(H₂)`). -/
private theorem execAdj_append_eq_left_on_left {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₁) (u : ℕ) :
    execAdj (H₁ ++ H₂) v u = execAdj H₁ v u := by
  rw [execAdj_append, execAdj_eq_false_of_first_notMem H₂ (h v hv) u, Bool.or_false]

/-- For `v ∈ V(H₂)` and any `u`, similarly. -/
private theorem execAdj_append_eq_right_on_right {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₂) (u : ℕ) :
    execAdj (H₁ ++ H₂) v u = execAdj H₂ v u := by
  rw [execAdj_append, execAdj_eq_false_of_first_notMem H₁ (h.symm v hv) u, Bool.false_or]

/-- Cross-component adjacency in the disjoint union is always false. -/
private theorem execAdj_append_cross_left {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₁)
    {u : ℕ} (hu : u ∈ vertexList H₂) :
    execAdj (H₁ ++ H₂) v u = false := by
  rw [execAdj_append,
      execAdj_eq_false_of_second_notMem H₁ v (fun hu1 => h u hu1 hu),
      execAdj_eq_false_of_first_notMem H₂ (h v hv) u]
  rfl

/-- Cross-component adjacency in the disjoint union is always false (sym.). -/
private theorem execAdj_append_cross_right {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₂)
    {u : ℕ} (hu : u ∈ vertexList H₁) :
    execAdj (H₁ ++ H₂) v u = false := by
  rw [execAdj_append,
      execAdj_eq_false_of_first_notMem H₁ (h.symm v hv) u,
      execAdj_eq_false_of_second_notMem H₂ v (h u hu)]
  rfl

/-- Pointwise foldr congruence: if two foldr bodies agree pointwise on the
elements of the list and any accumulator, the foldrs are equal. -/
private lemma foldr_pointwise_congr {α β : Type*} (l : List α)
    {f g : α → β → β} (k : β) (h : ∀ a ∈ l, ∀ b, f a b = g a b) :
    l.foldr f k = l.foldr g k := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : ∀ b, f a b = g a b := h a List.mem_cons_self
    have htail : ∀ a' ∈ l, ∀ b, f a' b = g a' b :=
      fun a' ha' b => h a' (List.mem_cons_of_mem _ ha') b
    simp only [List.foldr]
    rw [ha, ih htail]

/-- For `v ∈ V(H₁)`, the `H₁ ++ H₂` adjacency degree of `v` equals its
`H₁`-degree (the `V(H₂)` part of the filter contributes no neighbors). -/
private theorem execAdjDegree_append_left {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₁) :
    execAdjDegree (H₁ ++ H₂) v = execAdjDegree H₁ v := by
  unfold execAdjDegree
  rw [vertexList_append_disjoint h, List.filter_append, List.length_append]
  -- Right filter is empty: every `u ∈ V(H₂)` is cross-component.
  have h_right : (vertexList H₂).filter (fun u => execAdj (H₁ ++ H₂) v u) = [] := by
    have hconst : (vertexList H₂).filter (fun u => execAdj (H₁ ++ H₂) v u) =
                  (vertexList H₂).filter (fun _ => false) := by
      apply List.filter_congr
      intro u hu
      exact execAdj_append_cross_left h hv hu
    rw [hconst]; simp
  -- Left filter agrees with the `H₁`-only filter via `execAdj_append_eq_left_on_left`.
  have h_left : (vertexList H₁).filter (fun u => execAdj (H₁ ++ H₂) v u) =
                (vertexList H₁).filter (fun u => execAdj H₁ v u) := by
    apply List.filter_congr
    intro u _
    exact execAdj_append_eq_left_on_left h hv u
  rw [h_right, h_left]
  simp

/-- Symmetric: for `v ∈ V(H₂)`. -/
private theorem execAdjDegree_append_right {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₂) :
    execAdjDegree (H₁ ++ H₂) v = execAdjDegree H₂ v := by
  unfold execAdjDegree
  rw [vertexList_append_disjoint h, List.filter_append, List.length_append]
  have h_left : (vertexList H₁).filter (fun u => execAdj (H₁ ++ H₂) v u) = [] := by
    have hconst : (vertexList H₁).filter (fun u => execAdj (H₁ ++ H₂) v u) =
                  (vertexList H₁).filter (fun _ => false) := by
      apply List.filter_congr
      intro u hu
      exact execAdj_append_cross_right h hv hu
    rw [hconst]; simp
  have h_right : (vertexList H₂).filter (fun u => execAdj (H₁ ++ H₂) v u) =
                 (vertexList H₂).filter (fun u => execAdj H₂ v u) := by
    apply List.filter_congr
    intro u _
    exact execAdj_append_eq_right_on_right h hv u
  rw [h_left, h_right]
  simp

/-- For `v ∈ V(H₁)`, the triangle count through `v` is computed identically
on `H₁` and on `H₁ ++ H₂`: the `v`-neighbor set in the disjoint union is
exactly the `H₁`-neighbor set, and the inner adjacency-check between
two `V(H₁)` vertices reduces to the `H₁`-only check. -/
private theorem execTriangleCountAtVertex_append_left {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₁) :
    execTriangleCountAtVertex (H₁ ++ H₂) v = execTriangleCountAtVertex H₁ v := by
  -- Step 1: the `v`-neighbor sets coincide.
  have h_nbrs :
      (vertexList (H₁ ++ H₂)).filter
        (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) =
      (vertexList H₁).filter (fun x => decide (x ≠ v) && execAdj H₁ v x) := by
    rw [vertexList_append_disjoint h, List.filter_append]
    have h_left : (vertexList H₁).filter
                    (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) =
                  (vertexList H₁).filter
                    (fun x => decide (x ≠ v) && execAdj H₁ v x) := by
      apply List.filter_congr
      intro x _
      rw [execAdj_append_eq_left_on_left h hv x]
    have h_right : (vertexList H₂).filter
                      (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) = [] := by
      have hconst : (vertexList H₂).filter
                        (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) =
                    (vertexList H₂).filter (fun _ => false) := by
        apply List.filter_congr
        intro x hx
        rw [execAdj_append_cross_left h hv hx]
        simp
      rw [hconst]; simp
    rw [h_left, h_right, List.append_nil]
  -- Step 2: rewrite the body of `execTriangleCountAtVertex` using `h_nbrs`
  -- and the inner adjacency rewrite (both endpoints in `V(H₁)`).
  unfold execTriangleCountAtVertex
  simp only
  rw [h_nbrs]
  -- The two foldrs now share the same `nbrs` list. Show their per-step
  -- bodies agree pointwise.
  set nbrs := (vertexList H₁).filter (fun x => decide (x ≠ v) && execAdj H₁ v x)
    with hnbrs_def
  have nbrs_subset_V₁ : ∀ x ∈ nbrs, x ∈ vertexList H₁ := by
    intro x hx
    rw [hnbrs_def, List.mem_filter] at hx
    exact hx.1
  -- Pointwise body equality on `nbrs`.
  apply foldr_pointwise_congr
  intro x hx acc
  congr 1
  -- Inner filter: rewrite adjacency on (x, y) for x, y ∈ V(H₁).
  have h_inner_filter : nbrs.filter (fun y => x < y && execAdj (H₁ ++ H₂) x y) =
                        nbrs.filter (fun y => x < y && execAdj H₁ x y) := by
    apply List.filter_congr
    intro y _
    have hx₁ : x ∈ vertexList H₁ := nbrs_subset_V₁ x hx
    rw [execAdj_append_eq_left_on_left h hx₁ y]
  rw [h_inner_filter]

/-- Symmetric for `v ∈ V(H₂)`. -/
private theorem execTriangleCountAtVertex_append_right {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₂) :
    execTriangleCountAtVertex (H₁ ++ H₂) v = execTriangleCountAtVertex H₂ v := by
  have h_nbrs :
      (vertexList (H₁ ++ H₂)).filter
        (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) =
      (vertexList H₂).filter (fun x => decide (x ≠ v) && execAdj H₂ v x) := by
    rw [vertexList_append_disjoint h, List.filter_append]
    have h_right : (vertexList H₂).filter
                    (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) =
                  (vertexList H₂).filter
                    (fun x => decide (x ≠ v) && execAdj H₂ v x) := by
      apply List.filter_congr
      intro x _
      rw [execAdj_append_eq_right_on_right h hv x]
    have h_left : (vertexList H₁).filter
                      (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) = [] := by
      have hconst : (vertexList H₁).filter
                        (fun x => decide (x ≠ v) && execAdj (H₁ ++ H₂) v x) =
                    (vertexList H₁).filter (fun _ => false) := by
        apply List.filter_congr
        intro x hx
        rw [execAdj_append_cross_right h hv hx]
        simp
      rw [hconst]; simp
    rw [h_left, h_right, List.nil_append]
  unfold execTriangleCountAtVertex
  simp only
  rw [h_nbrs]
  set nbrs := (vertexList H₂).filter (fun x => decide (x ≠ v) && execAdj H₂ v x)
    with hnbrs_def
  have nbrs_subset_V₂ : ∀ x ∈ nbrs, x ∈ vertexList H₂ := by
    intro x hx
    rw [hnbrs_def, List.mem_filter] at hx
    exact hx.1
  apply foldr_pointwise_congr
  intro x hx acc
  congr 1
  have h_inner_filter : nbrs.filter (fun y => x < y && execAdj (H₁ ++ H₂) x y) =
                        nbrs.filter (fun y => x < y && execAdj H₂ x y) := by
    apply List.filter_congr
    intro y _
    have hx₂ : x ∈ vertexList H₂ := nbrs_subset_V₂ x hx
    rw [execAdj_append_eq_right_on_right h hx₂ y]
  rw [h_inner_filter]

/-- For `v ∈ V(H₁)`, the per-vertex scaled Knill defect on the disjoint
union equals the one on `H₁`. Combines the degree- and triangle-count
preservation lemmas. -/
private theorem knillVertexK6_append_left {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₁) :
    knillVertexK6 (H₁ ++ H₂) v = knillVertexK6 H₁ v := by
  unfold knillVertexK6
  rw [execAdjDegree_append_left h hv, execTriangleCountAtVertex_append_left h hv]

/-- Symmetric: for `v ∈ V(H₂)`. -/
private theorem knillVertexK6_append_right {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) {v : ℕ} (hv : v ∈ vertexList H₂) :
    knillVertexK6 (H₁ ++ H₂) v = knillVertexK6 H₂ v := by
  unfold knillVertexK6
  rw [execAdjDegree_append_right h hv, execTriangleCountAtVertex_append_right h hv]

/-- Foldr-accumulator factoring for the integer-sum body
`fun v acc => acc + f v`: the starting accumulator can be pulled out. -/
private lemma foldr_add_acc_factor {α : Type*} (l : List α) (f : α → ℤ) :
    ∀ k : ℤ,
      l.foldr (fun v acc => acc + f v) k =
        l.foldr (fun v acc => acc + f v) 0 + k := by
  induction l with
  | nil => intro k; simp
  | cons v l ih =>
    intro k
    simp only [List.foldr]
    rw [ih k, ih 0]
    ring

/-- The integer-sum foldr splits over `++`. -/
private lemma foldr_add_split {α : Type*} (l₁ l₂ : List α) (f : α → ℤ) :
    (l₁ ++ l₂).foldr (fun v acc => acc + f v) 0 =
      l₁.foldr (fun v acc => acc + f v) 0 +
      l₂.foldr (fun v acc => acc + f v) 0 := by
  rw [List.foldr_append, foldr_add_acc_factor]

/-- Foldr congruence for the integer-sum body when the summand depends only
on each element (pointwise on the list). -/
private lemma foldr_add_pointwise_congr {α : Type*} (l : List α)
    (f g : α → ℤ) (h : ∀ a ∈ l, f a = g a) :
    l.foldr (fun v acc => acc + f v) 0 =
      l.foldr (fun v acc => acc + g v) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : f a = g a := h a List.mem_cons_self
    have htail : ∀ b ∈ l, f b = g b :=
      fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.foldr]
    rw [ih htail, ha]

/-- **(K1) — proved.** Knill's scaled Euler characteristic is additive over
vertex-disjoint unions of executable hypergraphs.

This closes the K1 obligation `K1_KnillAdditiveOverDisjointUnion` with a
real combinatorial proof: vertex-list partition, per-vertex Knill
preservation, and a foldr-split over the partition. No `decide`, no
`native_decide`, no `sorry`. -/
theorem K1_proved (H₁ H₂ : ExecHG ℕ) (h : VertexDisjoint H₁ H₂) :
    knillEulerScaled (H₁ ++ H₂) = knillEulerScaled H₁ + knillEulerScaled H₂ := by
  unfold knillEulerScaled
  rw [vertexList_append_disjoint h, foldr_add_split]
  congr 1
  · -- Sum over `vertexList H₁`: rewrite `knillVertexK6 (H₁++H₂)` to `knillVertexK6 H₁`.
    apply foldr_add_pointwise_congr
    intro v hv
    exact knillVertexK6_append_left h hv
  · -- Sum over `vertexList H₂`: rewrite to `knillVertexK6 H₂`.
    apply foldr_add_pointwise_congr
    intro v hv
    exact knillVertexK6_append_right h hv

/-- Composition with the framework's stated K1 obligation. -/
theorem K1_proved_satisfies_K1 : K1_KnillAdditiveOverDisjointUnion := K1_proved

/-! ## Section E: K2 — vertex-relabeling invariance -/

/-- Vertex-relabeling: apply a bijection on `ℕ` to every vertex. -/
def relabel (f : ℕ → ℕ) (H : ExecHG ℕ) : ExecHG ℕ :=
  H.map (Hyperedge.map f)

/-- **(K2) Knill is invariant under vertex relabeling.**

For any bijection `f : ℕ → ℕ`, `knillEulerScaled (relabel f H) = knillEulerScaled H`.

The proof is structural: `K6(v)` depends only on the local clique
structure, which is preserved by bijection.

Stated as a Prop obligation. -/
def K2_KnillRelabelingInvariant : Prop :=
  ∀ (f : ℕ → ℕ) (_h : Function.Bijective f) (H : ExecHG ℕ),
    knillEulerScaled (relabel f H) = knillEulerScaled H

/-! ## Section F: single-edge-LHS predicate -/

/-- Predicate for a rule with a single LHS edge. -/
def SingleEdgeLHS (r : ExecRule) : Prop := r.lhs.length = 1

/-! ## Section G: E1 — the engine-decomposition obligation -/

/-- **(E1) Engine commutes with disjoint union for single-edge-LHS rules.**

For a single-edge-LHS rule `r` and vertex-disjoint seeds `H₁, H₂`,
the Knill of the causal DAG of evolution on the disjoint union splits:

  `knillEulerScaled (causalDAG sys (H₁ ++ H₂) d)`
    `= knillEulerScaled (causalDAG sys H₁ d) + knillEulerScaled (causalDAG sys H₂ d)`

Mathematical content (the obligation):

  (a) `allMatches r (H₁ ++ H₂) = allMatches r H₁ ++ allMatches r H₂`
      (no cross-component matches because LHS has only one edge and
      vertex-disjointness prevents cross-component edges).
  (b) Fresh-vertex offsets, when allocated globally for `H₁ ++ H₂`,
      can be rebased to local offsets per component without altering
      the causal-DAG Knill (just relabeling — closes via K2).
  (c) Per-step state on the disjoint union decomposes accordingly.

Engine-semantics obligation; similar in scope to the H9 step lemma.
Stated as a Prop. -/
def E1_EngineCommutesWithDisjointUnion : Prop :=
  ∀ (r : ExecRule) (_h : SingleEdgeLHS r) (H₁ H₂ : ExecHG ℕ)
    (_hd : VertexDisjoint H₁ H₂) (d : Nat),
    knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ (H₁ ++ H₂) d)
      = knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ H₁ d)
      + knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ H₂ d)

/-! ## Section H: composition — disjoint-seed per-edge additivity -/

/-- A "two-disjoint-edge" seed is a hypergraph that is the disjoint
union of two single-edge hypergraphs. -/
structure TwoDisjointEdges where
  e₁ : ExecHG ℕ
  e₂ : ExecHG ℕ
  e₁_single : e₁.length = 1
  e₂_single : e₂.length = 1
  disjoint : VertexDisjoint e₁ e₂

/-- The combined seed. -/
def TwoDisjointEdges.seed (t : TwoDisjointEdges) : ExecHG ℕ := t.e₁ ++ t.e₂

/-- **Per-edge additivity for two-disjoint-edge seeds**, derived from
the engine-decomposition obligation (E1) plus the K2 relabeling
invariance.

Given E1 and K2, for any single-edge-LHS rule, the Knill of the
causal-DAG evolution on a two-disjoint-edge seed equals the sum of
the per-component evolutions. -/
theorem two_disjoint_edge_per_edge_additivity
    (engine_decomp : E1_EngineCommutesWithDisjointUnion) :
    ∀ (r : ExecRule) (h : SingleEdgeLHS r) (t : TwoDisjointEdges) (d : Nat),
      knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ t.seed d)
        = knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ t.e₁ d)
        + knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ t.e₂ d) := by
  intro r h t d
  exact engine_decomp r h t.e₁ t.e₂ t.disjoint d

/-! ## Section I: BBH target

BBH initial data is constructed as 7 disjoint edges; once E1 is
proved, the `7×` BBH multiplier becomes a real theorem instead of
finite native_decide.

The actual BBH seed lives in `BBHInitialData.lean`. Its disjointness
characterization (currently empirical) would feed into this framework.
-/

/-- **Target universal theorem for BBH** (conditional on E1 + BBH
disjointness characterization).

Once `EngineCommutesWithDisjointUnion` is proved AND the BBH seed
is shown to be 7-disjoint-edge, this universal-in-d theorem replaces
the finite `native_decide` verifications across `BBHCurvatureEvolution.lean`,
`BBHDeepEvolution.lean`, `BBHMetricTensor.lean`, etc. -/
def BBH_per_edge_universal_target : Prop :=
  ∀ (r : ExecRule) (_h : SingleEdgeLHS r) (d : Nat) (single_edge : ExecHG ℕ)
    (_hsingle : single_edge.length = 1),
    -- Once BBH disjointness is established:
    -- knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ BBHseed d)
    --   = 7 * knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ single_edge d)
    True  -- Placeholder pending BBH disjointness link

/-! ## What this delivers

**Proved unconditionally in this module:**

  * `VertexDisjoint` predicate + symmetry.
  * `mem_vertexList_append`: vertexList membership decomposes over `++`.
  * `execAdj_append`: adjacency in `H₁ ++ H₂` is the OR of adjacencies
    in the components.
  * `execAdj_cross_H1_zero` / `execAdj_cross_H2_zero`: under vertex-
    disjointness, cross-component adjacencies are false. These are the
    structural sub-lemmas needed for K1.

**Stated as named Prop obligations (no sorry, no decide):**

  * `K1_KnillAdditiveOverDisjointUnion`: Knill additivity on disjoint
    union. Combinatorial; closing it requires the foldr-split chain
    over `vertexList`.
  * `K2_KnillRelabelingInvariant`: Knill invariance under vertex
    bijection.
  * `E1_EngineCommutesWithDisjointUnion`: engine commutes with disjoint
    union for single-edge-LHS rules. Engine-semantics.

**Conditional theorem proved here:**

  * `two_disjoint_edge_per_edge_additivity`: given E1, the two-disjoint-
    edge per-edge additivity is immediate.

**Path to closure:**

  1. Close K1 (combinatorial): ~100-200 lines Lean, well-scoped.
  2. Close K2 (relabeling invariance): ~50 lines, structural.
  3. Close E1 (engine-decomposition): multi-session, similar scope to
     the H9 step lemma.
  4. Establish BBH disjointness link: characterize `bbhInitial` as
     `IsKDisjointEdges 7`.

With K1 + K2 + E1 + BBH-disjointness, the universal `7×` BBH multiplier
follows, replacing all finite native_decide checks across the BBH
modules. The framework here makes the dependency chain explicit.
-/

/-! ## Section K2-PROOF: K2 — vertex-relabeling invariance, proved

A real combinatorial proof of K2_KnillRelabelingInvariant:
relabeling vertices by a bijection preserves the scaled Knill Euler
characteristic. The structure mirrors K1:

  * `vertexList_relabel`  : vertex list commutes with relabel (injective).
  * `execAdj_relabel`     : adjacency commutes with relabel.
  * `nbrs_relabel`        : the v-neighbour set commutes (map-of-filter).
  * `execAdjDegree_relabel`     : per-vertex degree commutes.
  * `execTriangleCountAtVertex_relabel` : per-vertex triangle count
    commutes — proved via the doubled-count trick (the triangle count
    times two equals the order-independent ordered-pair count, which is
    trivially bijection-invariant). Closes the order-dependent `x < y`
    obstruction without rewriting the existing `execTriangleCountAtVertex`.
  * `knillVertexK6_relabel` : per-vertex Knill defect commutes.
  * `K2_proved`           : foldr over `vertexList H.map f` factors via
    `foldr_map` and the per-vertex equality.
-/

/-- For an injection `f` on `ℕ`, list-membership of `f u` in `L.map f` is
equivalent to membership of `u` in `L`. -/
private lemma map_contains_iff (f : ℕ → ℕ) (hf : Function.Injective f)
    (L : List ℕ) (u : ℕ) :
    (L.map f).contains (f u) = L.contains u := by
  by_cases h : u ∈ L
  · have hfu : f u ∈ L.map f := List.mem_map_of_mem h
    rw [show ((L.map f).contains (f u)) = true from List.contains_iff_mem.mpr hfu,
        show (L.contains u) = true from List.contains_iff_mem.mpr h]
  · have hfu : f u ∉ L.map f := by
      intro hin
      rcases List.mem_map.mp hin with ⟨a, ha, hfa⟩
      exact h (hf hfa ▸ ha)
    have h1 : (L.map f).contains (f u) = false := by
      apply Bool.eq_false_iff.mpr
      intro c; exact hfu (List.contains_iff_mem.mp c)
    have h2 : L.contains u = false := by
      apply Bool.eq_false_iff.mpr
      intro c; exact h (List.contains_iff_mem.mp c)
    rw [h1, h2]

/-- `vertexList` commutes with `relabel f` when `f` is injective. -/
private lemma vertexList_relabel (f : ℕ → ℕ) (hf : Function.Injective f)
    (H : ExecHG ℕ) :
    vertexList (relabel f H) = (vertexList H).map f := by
  unfold vertexList relabel
  rw [List.flatMap_map]
  show (H.flatMap (fun a => (a.verts).map f)).dedup
       = ((H.flatMap (·.verts)).dedup).map f
  rw [← List.map_flatMap, List.dedup_map_of_injective hf]

/-- Boolean inequality commutes with an injection. -/
private lemma bne_map (f : ℕ → ℕ) (hf : Function.Injective f) (u v : ℕ) :
    (f u != f v) = (u != v) := by
  rcases eq_or_ne u v with h | h
  · subst h; simp
  · have hne : f u ≠ f v := fun ha => h (hf ha)
    rw [bne_iff_ne.mpr hne, bne_iff_ne.mpr h]

/-- `execAdj` commutes with `relabel f` for any injection `f`. -/
private lemma execAdj_relabel (f : ℕ → ℕ) (hf : Function.Injective f)
    (H : ExecHG ℕ) (u v : ℕ) :
    execAdj (relabel f H) (f u) (f v) = execAdj H u v := by
  unfold execAdj relabel
  rw [List.any_map, bne_map f hf]
  congr 1
  apply List.any_congr rfl
  intro e
  show ((Hyperedge.map f e).verts.contains (f u) && (Hyperedge.map f e).verts.contains (f v))
     = (e.verts.contains u && e.verts.contains v)
  change ((e.verts.map f).contains (f u) && (e.verts.map f).contains (f v))
       = (e.verts.contains u && e.verts.contains v)
  rw [map_contains_iff f hf e.verts u, map_contains_iff f hf e.verts v]

/-- `execAdj` is symmetric. -/
private lemma execAdj_symm (H : ExecHG ℕ) (u v : ℕ) :
    execAdj H u v = execAdj H v u := by
  unfold execAdj
  rw [bne_comm]
  congr 1
  apply List.any_congr rfl
  intro e
  exact Bool.and_comm _ _

/-- `execAdj` is irreflexive. -/
private lemma execAdj_irrefl (H : ExecHG ℕ) (u : ℕ) :
    execAdj H u u = false := by
  unfold execAdj
  simp

/-- `execAdj = true` implies the endpoints differ. -/
private lemma execAdj_ne_of_true (H : ExecHG ℕ) {u v : ℕ}
    (h : execAdj H u v = true) : u ≠ v := by
  intro hev
  rw [hev, execAdj_irrefl] at h
  exact Bool.noConfusion h

/-- The `v`-neighbour set in `relabel f H` (at vertex `f v`) is the
`f`-image of the `v`-neighbour set in `H`. -/
private lemma nbrs_relabel (f : ℕ → ℕ) (hf : Function.Injective f)
    (H : ExecHG ℕ) (v : ℕ) :
    (vertexList (relabel f H)).filter
        (fun x => decide (x ≠ f v) && execAdj (relabel f H) (f v) x)
      = ((vertexList H).filter
          (fun x => decide (x ≠ v) && execAdj H v x)).map f := by
  rw [vertexList_relabel f hf, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply]
  rw [execAdj_relabel f hf H v x]
  have h_eq : (f x ≠ f v) ↔ (x ≠ v) :=
    ⟨fun h hxv => h (by rw [hxv]), fun h hfxv => h (hf hfxv)⟩
  simp [h_eq]

/-- `execAdjDegree` commutes with `relabel f` (under bijection: injectivity
on the filter + length preserved by `map`). -/
private lemma execAdjDegree_relabel (f : ℕ → ℕ) (hf : Function.Injective f)
    (H : ExecHG ℕ) (v : ℕ) :
    execAdjDegree (relabel f H) (f v) = execAdjDegree H v := by
  unfold execAdjDegree
  rw [vertexList_relabel f hf, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro x _
  show execAdj (relabel f H) (f v) (f x) = execAdj H v x
  exact execAdj_relabel f hf H v x

/-! ### Helper arithmetic on `Nat` foldrs and filters

These mirror the integer-typed `foldr_add_*` helpers used for K1 but
target `Nat`, which is what the triangle count needs. -/

private lemma length_filter_cons {α : Type*} (x : α) (rest : List α)
    (p : α → Bool) :
    ((x :: rest).filter p).length
      = (if p x then 1 else 0) + (rest.filter p).length := by
  by_cases h : p x = true
  · simp [List.filter_cons, h]
    omega
  · have h' : p x = false := by
      cases hx : p x with
      | true => exact (h hx).elim
      | false => rfl
    simp [List.filter_cons, h']

private lemma nat_foldr_add_acc_factor {α : Type*} (l : List α) (f : α → ℕ) :
    ∀ k : ℕ,
      l.foldr (fun v acc => acc + f v) k =
        l.foldr (fun v acc => acc + f v) 0 + k := by
  induction l with
  | nil => intro k; simp
  | cons v l ih =>
    intro k
    simp only [List.foldr]
    rw [ih k, ih 0]; omega

private lemma nat_foldr_add_split {α : Type*} (l : List α) (g h : α → ℕ) :
    l.foldr (fun v acc => acc + (g v + h v)) 0 =
      l.foldr (fun v acc => acc + g v) 0 +
      l.foldr (fun v acc => acc + h v) 0 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.foldr]
    rw [ih]; omega

private lemma foldr_const_zero {α : Type*} (l : List α) :
    l.foldr (fun (_ : α) (acc : ℕ) => acc + 0) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [List.foldr, ih]

private lemma foldr_ite_eq_countP (L : List ℕ) (p : ℕ → Bool) :
    L.foldr (fun y acc => acc + (if p y then 1 else 0)) 0
      = (L.filter p).length := by
  induction L with
  | nil => rfl
  | cons y l ih =>
    simp only [List.foldr]
    rw [ih]
    by_cases h : p y = true
    · simp [List.filter_cons, h]
    · have h' : p y = false := by
        cases hx : p y with
        | true => exact (h hx).elim
        | false => rfl
      simp [List.filter_cons, h']

/-- Swap-fubini for double `foldr`-sum on filtered counts. -/
private lemma swap_fubini_filter (L₁ L₂ : List ℕ) (Q : ℕ → ℕ → Bool) :
    L₁.foldr (fun x acc => acc + (L₂.filter (Q x)).length) 0
      = L₂.foldr (fun y acc => acc + (L₁.filter (fun x => Q x y)).length) 0 := by
  induction L₁ with
  | nil =>
    simp only [List.foldr_nil, List.filter_nil, List.length_nil]
    exact (foldr_const_zero L₂).symm
  | cons x rest ih =>
    simp only [List.foldr]
    rw [ih]
    have h_body : ∀ y, ((x :: rest).filter (fun x' => Q x' y)).length
                       = (if Q x y then 1 else 0)
                         + (rest.filter (fun x' => Q x' y)).length :=
      fun y => length_filter_cons x rest (fun x' => Q x' y)
    have h_eq : L₂.foldr (fun y acc =>
                    acc + ((x :: rest).filter (fun x' => Q x' y)).length) 0
              = L₂.foldr (fun y acc =>
                    acc + ((if Q x y then 1 else 0)
                          + (rest.filter (fun x' => Q x' y)).length)) 0 := by
      apply foldr_pointwise_congr L₂ 0
      intro y _ acc
      rw [h_body y]
    rw [h_eq, nat_foldr_add_split, foldr_ite_eq_countP]
    omega

/-- For any `α` and pair of mutually-exclusive predicates `Q₁, Q₂`
on `L`, the filter under `Q₁ ∨ Q₂` decomposes by length-addition. -/
private lemma length_filter_or_disjoint (L : List ℕ) (Q₁ Q₂ : ℕ → Bool)
    (h_excl : ∀ y ∈ L, ¬(Q₁ y = true ∧ Q₂ y = true)) :
    (L.filter (fun y => Q₁ y || Q₂ y)).length
      = (L.filter Q₁).length + (L.filter Q₂).length := by
  induction L with
  | nil => rfl
  | cons y l ih =>
    have h_tail_excl : ∀ y' ∈ l, ¬(Q₁ y' = true ∧ Q₂ y' = true) :=
      fun y' hy' => h_excl y' (List.mem_cons_of_mem _ hy')
    have h_y : ¬(Q₁ y = true ∧ Q₂ y = true) := h_excl y List.mem_cons_self
    simp only [List.filter_cons]
    by_cases h1 : Q₁ y = true
    · have h2 : Q₂ y ≠ true := fun ha => h_y ⟨h1, ha⟩
      have h2' : Q₂ y = false := by
        cases hx : Q₂ y with
        | true => exact (h2 hx).elim
        | false => rfl
      simp [h1, h2', ih h_tail_excl]
      omega
    · have h1' : Q₁ y = false := by
        cases hx : Q₁ y with
        | true => exact (h1 hx).elim
        | false => rfl
      by_cases h2 : Q₂ y = true
      · simp [h1', h2, ih h_tail_excl]
        omega
      · have h2' : Q₂ y = false := by
          cases hx : Q₂ y with
          | true => exact (h2 hx).elim
          | false => rfl
        simp [h1', h2', ih h_tail_excl]

/-! ### Doubled-triangle-count trick

For any irreflexive symmetric `P` and any injection `f` on `ℕ`, the
ordered-pair count (no `<` condition) equals twice the "ordered by `f`"
count. Both the identity case (`f = id`) and the bijection case follow
the same scheme, with the order condition replaced by trichotomy. -/

/-- For each `x` and a pair of "less-than"-like predicates `lt₁ x ·, lt₂ x ·`
that are mutually exclusive and whose disjunction agrees with `(≠ x)` on
the support of `P x ·`, the count under `P` partitions as the sum of the
two ordered-by-lt counts. -/
private lemma length_filter_lt_partition (L : List ℕ) (P : ℕ → Bool)
    (lt₁ lt₂ : ℕ → Bool)
    (h_excl : ∀ y ∈ L, ¬(lt₁ y = true ∧ lt₂ y = true))
    (h_cover : ∀ y ∈ L, P y = true → (lt₁ y = true ∨ lt₂ y = true)) :
    (L.filter P).length
      = (L.filter (fun y => lt₁ y && P y)).length
        + (L.filter (fun y => lt₂ y && P y)).length := by
  -- Rewrite (L.filter P) as a filter under (lt₁ ∨ lt₂) ∧ P, then split.
  have h_eq : (L.filter P).length
            = (L.filter (fun y => (lt₁ y || lt₂ y) && P y)).length := by
    congr 1
    apply List.filter_congr
    intro y hy
    by_cases hP : P y = true
    · rcases h_cover y hy hP with h1 | h2
      · simp [hP, h1]
      · simp [hP, h2]
    · have hP' : P y = false := by
        cases hx : P y with
        | true => exact (hP hx).elim
        | false => rfl
      simp [hP']
  rw [h_eq]
  have h_distrib :
      (fun y => (lt₁ y || lt₂ y) && P y) = (fun y => (lt₁ y && P y) || (lt₂ y && P y)) := by
    funext y; cases lt₁ y <;> cases lt₂ y <;> cases P y <;> rfl
  rw [h_distrib]
  apply length_filter_or_disjoint
  intro y hy ⟨h1, h2⟩
  simp only [Bool.and_eq_true] at h1 h2
  exact h_excl y hy ⟨h1.1, h2.1⟩

/-- Per-`x` partition into the ordered halves, for an injection `f` with
trichotomy on `f`-images, and `P` irreflexive in the sense `P y = true → y ≠ x`. -/
private lemma length_filter_lt_partition_inj (L : List ℕ) (x : ℕ) (f : ℕ → ℕ)
    (hf : Function.Injective f) (P : ℕ → Bool) (hP_irr : ∀ y, P y = true → y ≠ x) :
    (L.filter P).length
      = (L.filter (fun y => decide (f x < f y) && P y)).length
        + (L.filter (fun y => decide (f y < f x) && P y)).length := by
  apply length_filter_lt_partition L P (fun y => decide (f x < f y)) (fun y => decide (f y < f x))
  · intro y _ ⟨h1, h2⟩
    have h1' : f x < f y := of_decide_eq_true h1
    have h2' : f y < f x := of_decide_eq_true h2
    exact Nat.lt_asymm h1' h2'
  · intro y _ hPy
    have hyx : y ≠ x := hP_irr y hPy
    have hfyx : f y ≠ f x := fun ha => hyx (hf ha)
    rcases Nat.lt_or_gt_of_ne hfyx with h | h
    · right; exact decide_eq_true h
    · left; exact decide_eq_true h

/-- Special case of the partition for `f = id`. -/
private lemma length_filter_lt_partition_id (L : List ℕ) (x : ℕ) (P : ℕ → Bool)
    (hP_irr : ∀ y, P y = true → y ≠ x) :
    (L.filter P).length
      = (L.filter (fun y => decide (x < y) && P y)).length
        + (L.filter (fun y => decide (y < x) && P y)).length := by
  have := length_filter_lt_partition_inj L x id Function.injective_id P hP_irr
  simpa using this

/-- The "doubled count" identity, identity-ordering case.
For a list `L` and a symmetric Boolean predicate `P : ℕ → ℕ → Bool`
that is irreflexive in the strong sense (`P x y = true → x ≠ y`),
twice the "less-than" ordered count equals the all-pairs ordered count. -/
private lemma triLT_doubled_id
    (L : List ℕ) (P : ℕ → ℕ → Bool)
    (hP_symm : ∀ x y, P x y = P y x)
    (hP_irr : ∀ x y, P x y = true → x ≠ y) :
    2 * L.foldr (fun x acc => acc
            + (L.filter (fun y => decide (x < y) && P x y)).length) 0
      = L.foldr (fun x acc => acc
            + (L.filter (fun y => P x y)).length) 0 := by
  -- Set DLT = "less-than" count, DGT = "greater-than" count
  set DLT := L.foldr (fun x acc => acc
                + (L.filter (fun y => decide (x < y) && P x y)).length) 0
    with hDLT
  set DGT := L.foldr (fun x acc => acc
                + (L.filter (fun y => decide (y < x) && P x y)).length) 0
    with hDGT
  -- Step 1: per-x partition, then sum:
  -- ∑_x (L.filter (P x)).length = DLT + DGT.
  have h_sum :
      L.foldr (fun x acc => acc + (L.filter (fun y => P x y)).length) 0 = DLT + DGT := by
    have h_body : ∀ x ∈ L, ∀ acc,
        acc + (L.filter (fun y => P x y)).length
          = acc + ((L.filter (fun y => decide (x < y) && P x y)).length
                  + (L.filter (fun y => decide (y < x) && P x y)).length) := by
      intro x _ acc
      rw [length_filter_lt_partition_id L x (P x)
            (fun y h => (hP_irr x y h).symm)]
    rw [foldr_pointwise_congr L 0 h_body]
    -- The body splits via nat_foldr_add_split
    rw [nat_foldr_add_split]
  -- Step 2: DLT = DGT, using swap-fubini and symmetry of P.
  have h_DLT_eq_DGT : DLT = DGT := by
    rw [hDLT, hDGT]
    -- DLT = ∑_x #{y : x < y ∧ P x y}; DGT = ∑_x #{y : y < x ∧ P x y}
    -- Apply swap-fubini to DGT (swaps outer/inner iteration).
    rw [swap_fubini_filter L L (fun x y => decide (y < x) && P x y)]
    -- After swap, both sides are foldrs over L with bodies that match
    -- under filter_congr via the symmetry of P.
    apply foldr_pointwise_congr L 0
    intro a _ b
    -- Goal: b + (L.filter (fun y => decide (a < y) && P a y)).length
    --     = b + (L.filter (fun y => decide (a < y) && P y a)).length
    have hfilter :
        (L.filter (fun y => decide (a < y) && P a y))
          = (L.filter (fun y => decide (a < y) && P y a)) := by
      apply List.filter_congr
      intro y _
      rw [hP_symm a y]
    rw [hfilter]
  rw [h_sum, h_DLT_eq_DGT]
  omega

/-- The "doubled count" identity, injection-ordering case.
The structure mirrors `triLT_doubled_id`: per-`x` partition into the two
ordered halves (via `length_filter_lt_partition_inj` and trichotomy on
`f`-images), then the two halves are equal via swap-fubini and
symmetry of `P`. -/
private lemma triLT_doubled_inj
    (L : List ℕ) (f : ℕ → ℕ) (hf : Function.Injective f)
    (P : ℕ → ℕ → Bool) (hP_symm : ∀ x y, P x y = P y x)
    (hP_irr : ∀ x y, P x y = true → x ≠ y) :
    2 * L.foldr (fun x acc => acc
            + (L.filter (fun y => decide (f x < f y) && P x y)).length) 0
      = L.foldr (fun x acc => acc
            + (L.filter (fun y => P x y)).length) 0 := by
  set DLT := L.foldr (fun x acc => acc
                + (L.filter (fun y => decide (f x < f y) && P x y)).length) 0
    with hDLT
  set DGT := L.foldr (fun x acc => acc
                + (L.filter (fun y => decide (f y < f x) && P x y)).length) 0
    with hDGT
  have h_sum :
      L.foldr (fun x acc => acc + (L.filter (fun y => P x y)).length) 0 = DLT + DGT := by
    have h_body : ∀ x ∈ L, ∀ acc,
        acc + (L.filter (fun y => P x y)).length
          = acc + ((L.filter (fun y => decide (f x < f y) && P x y)).length
                  + (L.filter (fun y => decide (f y < f x) && P x y)).length) := by
      intro x _ acc
      rw [length_filter_lt_partition_inj L x f hf (P x)
            (fun y h => (hP_irr x y h).symm)]
    rw [foldr_pointwise_congr L 0 h_body]
    rw [nat_foldr_add_split]
  have h_DLT_eq_DGT : DLT = DGT := by
    rw [hDLT, hDGT]
    rw [swap_fubini_filter L L (fun x y => decide (f y < f x) && P x y)]
    apply foldr_pointwise_congr L 0
    intro a _ b
    have hfilter :
        (L.filter (fun y => decide (f a < f y) && P a y))
          = (L.filter (fun y => decide (f a < f y) && P y a)) := by
      apply List.filter_congr
      intro y _
      rw [hP_symm a y]
    rw [hfilter]
  rw [h_sum, h_DLT_eq_DGT]
  omega

/-- **(K2 sub-lemma) `execTriangleCountAtVertex` commutes with `relabel`.**

The proof avoids the order-dependent `x < y` obstruction by going through
the doubled count: both `2 * execTriangleCountAtVertex (relabel f H) (f v)`
and `2 * execTriangleCountAtVertex H v` equal the order-independent
ordered-pair count `∑_x #{y ∈ nbrs : execAdj H x y}`. Then cancel `2`. -/
private lemma execTriangleCountAtVertex_relabel
    (f : ℕ → ℕ) (hf : Function.Bijective f) (H : ExecHG ℕ) (v : ℕ) :
    execTriangleCountAtVertex (relabel f H) (f v) = execTriangleCountAtVertex H v := by
  have hinj : Function.Injective f := hf.injective
  unfold execTriangleCountAtVertex
  simp only
  set nbrs := (vertexList H).filter
                (fun x => decide (x ≠ v) && execAdj H v x) with hnbrs_def
  -- Step 1: the v-neighbour list in (relabel f H, f v) is `nbrs.map f`.
  rw [show (vertexList (relabel f H)).filter
         (fun x => decide (x ≠ f v) && execAdj (relabel f H) (f v) x)
         = nbrs.map f from nbrs_relabel f hinj H v]
  -- Step 2: pull `map f` out of the outer foldr.
  rw [List.foldr_map]
  -- Step 3: push `map f` through the inner filter and rewrite `execAdj`.
  have h_inner : ∀ x ∈ nbrs, ∀ acc,
      acc + ((nbrs.map f).filter
              (fun y => decide (f x < y) && execAdj (relabel f H) (f x) y)).length
        = acc + (nbrs.filter
              (fun y => decide (f x < f y) && execAdj H x y)).length := by
    intro x _ acc
    have h_eq : ((nbrs.map f).filter
                  (fun y => decide (f x < y) && execAdj (relabel f H) (f x) y)).length
              = (nbrs.filter
                  (fun y => decide (f x < f y) && execAdj H x y)).length := by
      rw [List.filter_map, List.length_map]
      congr 1
      apply List.filter_congr
      intro y _
      simp only [Function.comp_apply]
      rw [execAdj_relabel f hinj H x y]
    rw [h_eq]
  rw [foldr_pointwise_congr nbrs 0 h_inner]
  -- Step 4: cancel 2 via the doubled-count identities (id vs f-image).
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by decide)
  rw [triLT_doubled_inj nbrs f hinj (execAdj H) (execAdj_symm H)
        (fun x y h => execAdj_ne_of_true H h)]
  rw [triLT_doubled_id nbrs (execAdj H) (execAdj_symm H)
        (fun x y h => execAdj_ne_of_true H h)]

/-- **(K2 sub-lemma) Per-vertex scaled Knill defect commutes with relabel. -/
private lemma knillVertexK6_relabel
    (f : ℕ → ℕ) (hf : Function.Bijective f) (H : ExecHG ℕ) (v : ℕ) :
    knillVertexK6 (relabel f H) (f v) = knillVertexK6 H v := by
  unfold knillVertexK6
  rw [execAdjDegree_relabel f hf.injective,
      execTriangleCountAtVertex_relabel f hf]

/-- **(K2) — proved.** Knill's scaled Euler characteristic is invariant
under any bijective relabeling of vertices.

This closes `K2_KnillRelabelingInvariant` with real combinatorics:
vertex-list / adjacency / triangle-count are each bijection-equivariant
on a per-vertex basis (using `Hyperedge.map`-distributivity, list-
`dedup`/`filter`/`map` interaction, and the doubled-count trick for
the order-dependent `<` condition in the triangle count). The foldr
over `vertexList` factors via `foldr_map` and the per-vertex equality. -/
theorem K2_proved (f : ℕ → ℕ) (hf : Function.Bijective f) (H : ExecHG ℕ) :
    knillEulerScaled (relabel f H) = knillEulerScaled H := by
  unfold knillEulerScaled
  rw [vertexList_relabel f hf.injective, List.foldr_map]
  apply foldr_pointwise_congr (vertexList H) 0
  intro v _ acc
  rw [knillVertexK6_relabel f hf]

/-- Composition with the framework's stated K2 obligation. -/
theorem K2_proved_satisfies_K2 : K2_KnillRelabelingInvariant := K2_proved

end PerEdgeAdditivityFramework
end InfraFormalization
