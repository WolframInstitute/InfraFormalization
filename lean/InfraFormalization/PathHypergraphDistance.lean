/-
Adjacency, connectivity and degrees in the path hypergraph.

For `pathHypergraph n`, this module proves that the Laplacian matrix annihilates constants and has
zero row sums, that the heat kernel fixes constant functions, that two vertices are adjacent if and
only if their values differ by 1, that the graph is connected for `n ≥ 1`, and that vertex 0 has
degree 1 for `n ≥ 2` and vertex 1 has degree 2 for `n ≥ 3`.
-/

import InfraFormalization.PathHypergraph
import InfraFormalization.HypergraphDistance
import InfraFormalization.LaplacianMatrix
import InfraFormalization.ExpEigenvector

namespace InfraFormalization

open Hypergraph

/-- `(laplacianMatrix (pathHypergraph n)).mulVec (fun _ => c) v = 0`. -/
theorem pathHypergraph_laplacianMatrix_mulVec_const (n : ℕ) (c : ℝ) (v : Fin n) :
    (Hypergraph.laplacianMatrix (pathHypergraph n)).mulVec (fun _ => c) v = 0 :=
  laplacianMatrix_mulVec_const (pathHypergraph n) c v

/-- `heatKernel (pathHypergraph n) t` maps the constant function `c` to itself. -/
theorem heatKernel_pathHypergraph_const_invariant (n : ℕ) (c : ℝ) (t : ℝ) :
    (Hypergraph.heatKernel (pathHypergraph n) t).mulVec (fun _ => c)
      = (fun _ => c) :=
  heatKernel_mulVec_const (pathHypergraph n) c t

/-- The rows of `laplacianMatrix (pathHypergraph n)` sum to 0. -/
theorem pathHypergraph_laplacianMatrix_row_sum_zero (n : ℕ) (v : Fin n) :
    ∑ w : Fin n, Hypergraph.laplacianMatrix (pathHypergraph n) v w = 0 :=
  laplacianMatrix_row_sum (pathHypergraph n) v

/-- `heatKernel (pathHypergraph n) t` applied to the constant function `c` takes the value `c` at
every vertex. -/
theorem pathHypergraph_heatKernel_preserves_const_at (n : ℕ) (c : ℝ) (t : ℝ)
    (v : Fin n) :
    ((Hypergraph.heatKernel (pathHypergraph n) t).mulVec (fun _ => c)) v = c := by
  rw [heatKernel_pathHypergraph_const_invariant n c t]

/-- `i` and `j` are adjacent in `pathHypergraph n` if and only if `i ≠ j` and their values differ by
1.
Vertex `0` is not adjacent to `n - 1` for `n ≥ 3`. -/
theorem pathHypergraph_Adj_iff (n : ℕ) (i j : Fin n) :
    (pathHypergraph n).Adj i j ↔ i ≠ j ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  constructor
  · rintro ⟨hne, e, he, hcontains⟩
    refine ⟨hne, ?_⟩
    rw [Multiset.mem_toFinset] at he
    unfold pathHypergraph at he
    simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map,
               Finset.mem_val, Finset.mem_univ, true_and] at he
    obtain ⟨k, hk⟩ := he
    subst hk
    obtain ⟨hi, hj⟩ := hcontains
    have hverts : (pathEdge n k).verts =
        [⟨k.val, by have h : k.val < n - 1 := k.isLt; omega⟩,
         ⟨k.val + 1, by have h : k.val < n - 1 := k.isLt; omega⟩] := rfl
    rw [hverts] at hi hj
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
               or_false] at hi hj
    rcases hi with hi_eq | hi_eq <;> rcases hj with hj_eq | hj_eq
    · subst hi_eq; subst hj_eq; exact absurd rfl hne
    · left
      have hi_val : i.val = k.val := by rw [hi_eq]
      have hj_val : j.val = k.val + 1 := by rw [hj_eq]
      omega
    · right
      have hi_val : i.val = k.val + 1 := by rw [hi_eq]
      have hj_val : j.val = k.val := by rw [hj_eq]
      omega
    · subst hi_eq; subst hj_eq; exact absurd rfl hne
  · rintro ⟨hne, hcases⟩
    have hmem_univ_val : ∀ (x : Fin (n - 1)),
        x ∈ (Finset.univ : Finset (Fin (n - 1))).val :=
      fun x => Finset.mem_val.mpr (Finset.mem_univ x)
    cases hcases with
    | inl hij =>
      -- i.val + 1 = j.val, so i.val < n - 1 (since j.val < n)
      have hi_lt : i.val < n - 1 := by
        have hj_lt := j.isLt
        omega
      let k : Fin (n - 1) := ⟨i.val, hi_lt⟩
      refine ⟨hne, pathEdge n k, ?_, ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        unfold pathHypergraph
        simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map,
                   Finset.mem_val, Finset.mem_univ, true_and]
        exact ⟨k, rfl⟩
      · show i ∈ (pathEdge n k).verts
        have : (pathEdge n k).verts =
            [⟨k.val, by have h : k.val < n - 1 := k.isLt; omega⟩,
             ⟨k.val + 1, by have h : k.val < n - 1 := k.isLt; omega⟩] := rfl
        rw [this]
        simp only [List.mem_cons, List.mem_singleton]
        left
        exact Fin.ext rfl
      · show j ∈ (pathEdge n k).verts
        have : (pathEdge n k).verts =
            [⟨k.val, by have h : k.val < n - 1 := k.isLt; omega⟩,
             ⟨k.val + 1, by have h : k.val < n - 1 := k.isLt; omega⟩] := rfl
        rw [this]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                   or_false]
        right
        apply Fin.ext
        show j.val = k.val + 1
        have hk_val : k.val = i.val := rfl
        omega
    | inr hji =>
      -- j.val + 1 = i.val, symmetric case
      have hj_lt : j.val < n - 1 := by
        have hi_lt := i.isLt
        omega
      let k : Fin (n - 1) := ⟨j.val, hj_lt⟩
      refine ⟨hne, pathEdge n k, ?_, ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        unfold pathHypergraph
        simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map,
                   Finset.mem_val, Finset.mem_univ, true_and]
        exact ⟨k, rfl⟩
      · show i ∈ (pathEdge n k).verts
        have : (pathEdge n k).verts =
            [⟨k.val, by have h : k.val < n - 1 := k.isLt; omega⟩,
             ⟨k.val + 1, by have h : k.val < n - 1 := k.isLt; omega⟩] := rfl
        rw [this]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                   or_false]
        right
        apply Fin.ext
        show i.val = k.val + 1
        have hk_val : k.val = j.val := rfl
        omega
      · show j ∈ (pathEdge n k).verts
        have : (pathEdge n k).verts =
            [⟨k.val, by have h : k.val < n - 1 := k.isLt; omega⟩,
             ⟨k.val + 1, by have h : k.val < n - 1 := k.isLt; omega⟩] := rfl
        rw [this]
        simp only [List.mem_cons, List.mem_singleton]
        left
        exact Fin.ext rfl

/-- For `n ≥ 1`, every vertex of `pathHypergraph n` is reachable from `0`. -/
theorem pathHypergraph_reachable_zero {n : ℕ} [NeZero n] (k : Fin n) :
    (pathHypergraph n).toSimpleGraph.Reachable
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ k := by
  rcases k with ⟨kv, hkv⟩
  induction kv with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    have hk_lt : k < n := by omega
    have ih' := ih hk_lt
    have hadj : (pathHypergraph n).toSimpleGraph.Adj
        ⟨k, hk_lt⟩ ⟨k + 1, hkv⟩ := by
      show (pathHypergraph n).Adj ⟨k, hk_lt⟩ ⟨k + 1, hkv⟩
      rw [pathHypergraph_Adj_iff]
      refine ⟨?_, Or.inl rfl⟩
      intro h
      have hval : (⟨k, hk_lt⟩ : Fin n).val = (⟨k + 1, hkv⟩ : Fin n).val := by
        rw [h]
      simp at hval
    exact ih'.trans hadj.reachable

/-- For `n ≥ 1`, `pathHypergraph n` is connected. -/
theorem pathHypergraph_connected {n : ℕ} [NeZero n] :
    (pathHypergraph n).toSimpleGraph.Connected := by
  refine SimpleGraph.Connected.mk ?_
  intro u v
  have hu := pathHypergraph_reachable_zero u
  have hv := pathHypergraph_reachable_zero v
  exact hu.symm.trans hv

/-- For `n ≥ 2`, vertex `0` of `pathHypergraph n` has degree 1. -/
theorem pathHypergraph_degree_zero {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (pathHypergraph n).toSimpleGraph.degree
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ = 1 := by
  have h0lt : (0 : ℕ) < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h1lt : (1 : ℕ) < n := hn
  have hne : (⟨0, h0lt⟩ : Fin n) ≠ ⟨1, h1lt⟩ := by
    intro h
    have hval : (⟨0, h0lt⟩ : Fin n).val = (⟨1, h1lt⟩ : Fin n).val := by rw [h]
    simp at hval
  have hneigh : (pathHypergraph n).toSimpleGraph.neighborFinset
      ⟨0, h0lt⟩ = ({⟨1, h1lt⟩} : Finset (Fin n)) := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro hadj
      have h := (pathHypergraph_Adj_iff n ⟨0, h0lt⟩ j).mp hadj
      obtain ⟨_, hcases⟩ := h
      rcases hcases with hij | hji
      · apply Fin.ext
        show j.val = 1
        have : (⟨0, h0lt⟩ : Fin n).val + 1 = j.val := hij
        simpa using this.symm
      · exfalso
        have : j.val + 1 = (⟨0, h0lt⟩ : Fin n).val := hji
        simp at this
    · intro hj
      subst hj
      show (pathHypergraph n).Adj ⟨0, h0lt⟩ ⟨1, h1lt⟩
      rw [pathHypergraph_Adj_iff]
      refine ⟨hne, Or.inl ?_⟩
      rfl
  rw [SimpleGraph.degree, hneigh]
  simp

/-- For `n ≥ 3`, vertex `1` of `pathHypergraph n` has degree 2. -/
theorem pathHypergraph_degree_one {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    (pathHypergraph n).toSimpleGraph.degree ⟨1, by omega⟩ = 2 := by
  have h0lt : (0 : ℕ) < n := by omega
  have h1lt : (1 : ℕ) < n := by omega
  have h2lt : (2 : ℕ) < n := by omega
  have hne_01 : (⟨1, h1lt⟩ : Fin n) ≠ ⟨0, h0lt⟩ := by
    intro h
    have hval : (⟨1, h1lt⟩ : Fin n).val = (⟨0, h0lt⟩ : Fin n).val := by rw [h]
    simp at hval
  have hne_12 : (⟨1, h1lt⟩ : Fin n) ≠ ⟨2, h2lt⟩ := by
    intro h
    have hval : (⟨1, h1lt⟩ : Fin n).val = (⟨2, h2lt⟩ : Fin n).val := by rw [h]
    simp at hval
  have hne_02 : (⟨0, h0lt⟩ : Fin n) ≠ ⟨2, h2lt⟩ := by
    intro h
    have hval : (⟨0, h0lt⟩ : Fin n).val = (⟨2, h2lt⟩ : Fin n).val := by rw [h]
    simp at hval
  have hneigh : (pathHypergraph n).toSimpleGraph.neighborFinset
      ⟨1, h1lt⟩ =
        ({⟨0, h0lt⟩, ⟨2, h2lt⟩} : Finset (Fin n)) := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
               Finset.mem_singleton]
    constructor
    · intro hadj
      have h := (pathHypergraph_Adj_iff n ⟨1, h1lt⟩ j).mp hadj
      obtain ⟨_, hcases⟩ := h
      rcases hcases with hij | hji
      · right
        apply Fin.ext
        show j.val = 2
        have : (⟨1, h1lt⟩ : Fin n).val + 1 = j.val := hij
        simpa using this.symm
      · left
        apply Fin.ext
        show j.val = 0
        have : j.val + 1 = (⟨1, h1lt⟩ : Fin n).val := hji
        simpa using this
    · intro hj
      rcases hj with h0 | h2
      · subst h0
        show (pathHypergraph n).Adj ⟨1, h1lt⟩ ⟨0, h0lt⟩
        rw [pathHypergraph_Adj_iff]
        refine ⟨hne_01, Or.inr ?_⟩
        rfl
      · subst h2
        show (pathHypergraph n).Adj ⟨1, h1lt⟩ ⟨2, h2lt⟩
        rw [pathHypergraph_Adj_iff]
        refine ⟨hne_12, Or.inl ?_⟩
        rfl
  rw [SimpleGraph.degree, hneigh]
  rw [Finset.card_insert_of_notMem]
  · simp
  · simp only [Finset.mem_singleton]
    exact hne_02

end InfraFormalization
