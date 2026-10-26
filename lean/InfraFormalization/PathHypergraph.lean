/-
The path hypergraph and its Laplacian.

This module defines `pathHypergraph n` on `Fin n`, with the `n - 1` edges `{i, i+1}`, and proves
that
it has `n - 1` edges. It defines the free-path eigenvalues `−4 sin²(kπ/(2n))` and eigenvectors
`cos(kπ(j + 1/2)/n)`, and proves that the eigenvalues are non-positive, that the `k = 0` eigenvalue
is
0 with constant eigenvector, that the Laplacian annihilates constants, and that the `k = 1`
eigenvalue is negative for `n ≥ 2`. The eigenvalue equation for `k ≥ 1` is not proved.
-/

import InfraFormalization.Hypergraph
import InfraFormalization.HypergraphLaplacian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace InfraFormalization

/-- The edge `{i, i+1}` of the path on `Fin n`, for `i : Fin (n - 1)`. -/
def pathEdge (n : ℕ) (i : Fin (n - 1)) : Hyperedge (Fin n) where
  verts := [⟨i.val, by
    have h : i.val < n - 1 := i.isLt
    omega⟩,
    ⟨i.val + 1, by
    have h : i.val < n - 1 := i.isLt
    omega⟩]
  nonempty := List.cons_ne_nil _ _

/-- The hypergraph on `Fin n` with the edges `pathEdge n i` for `i : Fin (n - 1)`. -/
noncomputable def pathHypergraph (n : ℕ) : Hypergraph (Fin n) where
  edges := ((Finset.univ : Finset (Fin (n - 1))).image (pathEdge n)).val

/-- `pathHypergraph n` has at most `n - 1` edges. -/
theorem pathHypergraph_edges_card_le (n : ℕ) :
    Multiset.card (pathHypergraph n).edges ≤ n - 1 := by
  unfold pathHypergraph
  have h1 : Multiset.card
      (((Finset.univ : Finset (Fin (n - 1))).image (pathEdge n)).val)
      ≤ ((Finset.univ : Finset (Fin (n - 1))).image (pathEdge n)).card := by
    exact le_of_eq rfl
  refine le_trans h1 ?_
  refine le_trans Finset.card_image_le ?_
  simp

/-- `pathEdge n` is injective. -/
theorem pathEdge_injective (n : ℕ) :
    Function.Injective (pathEdge n) := by
  intro i j hij
  have h_verts : (pathEdge n i).verts = (pathEdge n j).verts :=
    congrArg Hyperedge.verts hij
  unfold pathEdge at h_verts
  simp only [List.cons.injEq] at h_verts
  have h_first : (⟨i.val, by have h := i.isLt; omega⟩ : Fin n)
      = ⟨j.val, by have h := j.isLt; omega⟩ := h_verts.1
  have h_val : i.val = j.val := Fin.mk.injEq .. |>.mp h_first
  exact Fin.ext h_val

/-- `pathHypergraph n` has `n - 1` edges. -/
theorem pathHypergraph_size (n : ℕ) :
    (pathHypergraph n).size = n - 1 := by
  show Multiset.card (pathHypergraph n).edges = n - 1
  unfold pathHypergraph
  rw [show Multiset.card
      (((Finset.univ : Finset (Fin (n - 1))).image (pathEdge n)).val)
      = ((Finset.univ : Finset (Fin (n - 1))).image (pathEdge n)).card from rfl]
  rw [Finset.card_image_of_injective _ (pathEdge_injective n)]
  simp

/-- `pathEigenvalue n k = −4 sin²(kπ/(2n)) = −(2 − 2 cos(kπ/n))`, the `k`-th eigenvalue of the
Laplacian of the free path on `n` vertices. That it is an eigenvalue of the Laplacian of
`pathHypergraph n` is proved here only for `k = 0`. -/
noncomputable def pathEigenvalue (n k : ℕ) : ℝ :=
  -4 * (Real.sin (Real.pi * k / (2 * n)))^2

/-- `pathEigenvector n k j = cos(kπ(j + 1/2)/n)`, the `k`-th eigenvector of the Laplacian of the
free
path on `n` vertices. That it is an eigenvector of the Laplacian of `pathHypergraph n` is proved
here only for `k = 0`. -/
noncomputable def pathEigenvector (n k : ℕ) (j : Fin n) : ℝ :=
  Real.cos (Real.pi * k * (2 * j.val + 1) / (2 * n))

/-- `pathEigenvalue n k ≤ 0`. -/
theorem pathEigenvalue_nonpos (n k : ℕ) : pathEigenvalue n k ≤ 0 := by
  unfold pathEigenvalue
  have h_sq : (0 : ℝ) ≤ (Real.sin (Real.pi * k / (2 * n)))^2 :=
    sq_nonneg _
  nlinarith

/-- `pathEigenvalue n 0 = 0`. -/
theorem pathEigenvalue_ground_zero (n : ℕ) : pathEigenvalue n 0 = 0 := by
  unfold pathEigenvalue
  simp

/-- `pathEigenvector n 0 j = 1` for every `j`. -/
theorem pathEigenvector_zero_eq_one (n : ℕ) (j : Fin n) :
    pathEigenvector n 0 j = 1 := by
  unfold pathEigenvector
  simp

/-- `laplacianHyper (pathHypergraph n) (fun _ => c) v = 0`. -/
theorem pathLaplacian_of_const (n : ℕ) (c : ℝ) (v : Fin n) :
    Hypergraph.laplacianHyper (pathHypergraph n) (fun _ => c) v = 0 := by
  unfold Hypergraph.laplacianHyper
  have h_inner : ∀ e : Hyperedge (Fin n),
      ∑ w ∈ e.others v, ((fun _ => c) w - (fun _ => c) v) = 0 := by
    intro e
    refine Finset.sum_eq_zero (fun w _ => ?_)
    simp
  have h_map : (pathHypergraph n).edges.map
      (fun e => ∑ w ∈ e.others v, ((fun _ => c) w - (fun _ => c) v))
      = (pathHypergraph n).edges.map (fun _ => (0 : ℝ)) :=
    Multiset.map_congr rfl (fun e _ => h_inner e)
  rw [h_map]
  simp

/-- `laplacianHyper (pathHypergraph n) (pathEigenvector n 0) v = 0`. -/
theorem pathLaplacian_eigen_zero (n : ℕ) (v : Fin n) :
    Hypergraph.laplacianHyper (pathHypergraph n)
      (fun j => pathEigenvector n 0 j) v = 0 := by
  have h_const : (fun j : Fin n => pathEigenvector n 0 j) = fun _ => (1 : ℝ) :=
    funext (fun j => pathEigenvector_zero_eq_one n j)
  rw [h_const]
  exact pathLaplacian_of_const n 1 v

/-- For `n ≥ 2`, `pathEigenvalue n 1 < 0`. -/
theorem pathEigenvalue_one_neg {n : ℕ} (hn : 2 ≤ n) :
    pathEigenvalue n 1 < 0 := by
  unfold pathEigenvalue
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have h_two_n_pos : (0 : ℝ) < 2 * n := by linarith
  have h_pos : (0 : ℝ) < Real.pi * 1 / (2 * n) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have h_lt : Real.pi * 1 / (2 * n) < Real.pi := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hn_real : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ h_two_n_pos]
    calc Real.pi * 1 = Real.pi := by ring
      _ < Real.pi * (2 * n) := by nlinarith
  have h_sin_pos : 0 < Real.sin (Real.pi * 1 / (2 * n)) :=
    Real.sin_pos_of_pos_of_lt_pi h_pos h_lt
  have h_sq_pos : 0 < (Real.sin (Real.pi * 1 / (2 * n)))^2 := by positivity
  have h_sq_pos' : 0 < (Real.sin (Real.pi * ↑(1 : ℕ) / (2 * ↑n)))^2 := by
    push_cast; exact h_sq_pos
  nlinarith [h_sq_pos']

end InfraFormalization
