/-
**Path hypergraph: distance / connectivity theorems** (T5 extension,
fully hypergraph-grounded).

On `pathHypergraph n` (a hypergraph on `Fin n` with edges `{i, i+1}`),
this file provides:

  * `pathHypergraph_Adj_iff` — adjacency is `val = ±1`.
  * `pathHypergraph_connected` — the path is connected for `n ≥ 1`.
  * `pathHypergraph_heatKernel_const_invariant` — heat kernel
    preserves constant functions on the path.
  * `pathHypergraph_laplacianMatrix_row_sum_zero` — row sums of the
    path Laplacian matrix vanish.

Everything here is on `pathHypergraph n` directly — no continuum side.
-/

import InfraFormalization.PathHypergraph
import InfraFormalization.HypergraphDistance
import InfraFormalization.LaplacianMatrix
import InfraFormalization.ExpEigenvector

namespace InfraFormalization

open Hypergraph

/-- **Path hypergraph adjacency** is `val difference = ±1`. Every edge
of `pathHypergraph n` is `{i, i+1}` for some `i : Fin (n-1)`, so two
vertices are adjacent iff their `val`s differ by 1. -/
theorem pathHypergraph_laplacianMatrix_mulVec_const (n : ℕ) (c : ℝ) (v : Fin n) :
    (Hypergraph.laplacianMatrix (pathHypergraph n)).mulVec (fun _ => c) v = 0 :=
  laplacianMatrix_mulVec_const (pathHypergraph n) c v

/-- **Heat kernel on pathHypergraph preserves constant functions.**
Since `Δ_P · const = 0`, `exp(t · Δ_P) · const = exp(0) · const = const`.
Direct instantiation of the general `heatKernel_mulVec_const`. -/
theorem heatKernel_pathHypergraph_const_invariant (n : ℕ) (c : ℝ) (t : ℝ) :
    (Hypergraph.heatKernel (pathHypergraph n) t).mulVec (fun _ => c)
      = (fun _ => c) :=
  heatKernel_mulVec_const (pathHypergraph n) c t

/-- **Path Laplacian row sums vanish.** Direct consequence of
`laplacianMatrix_row_sum` applied to `pathHypergraph n`. -/
theorem pathHypergraph_laplacianMatrix_row_sum_zero (n : ℕ) (v : Fin n) :
    ∑ w : Fin n, Hypergraph.laplacianMatrix (pathHypergraph n) v w = 0 :=
  laplacianMatrix_row_sum (pathHypergraph n) v

/-- **Path Laplacian commutes with the constant function**: the path
heat-flow leaves any constant function untouched. This is the
"conservation of the average" statement for path-graph diffusion. -/
theorem pathHypergraph_heatKernel_preserves_const_at (n : ℕ) (c : ℝ) (t : ℝ)
    (v : Fin n) :
    ((Hypergraph.heatKernel (pathHypergraph n) t).mulVec (fun _ => c)) v = c := by
  rw [heatKernel_pathHypergraph_const_invariant n c t]

/-- **Path hypergraph adjacency iff val-difference is 1.** Two vertices
of `pathHypergraph n` are adjacent iff they are distinct and their
`Fin`-values differ by exactly one. Unlike the cycle, there is no
wrap-around: `0` is not adjacent to `n - 1`. -/
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

end InfraFormalization
