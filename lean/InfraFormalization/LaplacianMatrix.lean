/-
The hypergraph Laplacian as a matrix, and the heat kernel.

For a hypergraph on a finite vertex type, this module defines the matrix `laplacianMatrix H` of the
linear map `laplacianHyper H` and the heat kernel `heatKernel H t = exp(t · laplacianMatrix H)`,
using Mathlib's matrix exponential. It proves that the matrix acts as `laplacianHyper`, is
symmetric, and has zero row sums, and that the heat kernel equals the identity at `t = 0`, satisfies
`heatKernel H (s + t) = heatKernel H s * heatKernel H t`, is symmetric, and has inverse
`heatKernel H (-t)`.
-/

import InfraFormalization.HypergraphLaplacian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Laplacian matrix of a single edge `e`: the entry at `(v, u)` is 1 if `u ≠ v` and
`u ∈ e.others v`, `−|e.others v|` if `u = v`, and 0 otherwise. -/
noncomputable def laplacianMatrixEdge (e : Hyperedge V) : Matrix V V ℝ :=
  fun v u =>
    (if u ∈ e.others v then (1 : ℝ) else 0)
    - (if u = v then ((e.others v).card : ℝ) else 0)

/-- The sum of `laplacianMatrixEdge e` over the edges of `H`. -/
noncomputable def laplacianMatrix (H : Hypergraph V) : Matrix V V ℝ :=
  (H.edges.map laplacianMatrixEdge).sum

/-- `(laplacianMatrixEdge e).mulVec f v = ∑_{w ∈ e.others v} (f w − f v)`. -/
theorem laplacianMatrixEdge_mulVec (e : Hyperedge V) (f : V → ℝ) (v : V) :
    (laplacianMatrixEdge e).mulVec f v = ∑ w ∈ e.others v, (f w - f v) := by
  unfold laplacianMatrixEdge Matrix.mulVec
  simp only [dotProduct]
  -- First split the sum (A - B) into (sum A) - (sum B).
  have hsplit :
      ∑ u, ((if u ∈ e.others v then (1 : ℝ) else 0)
            - (if u = v then ((e.others v).card : ℝ) else 0)) * f u
      = (∑ u, (if u ∈ e.others v then (1 : ℝ) else 0) * f u)
        - (∑ u, (if u = v then ((e.others v).card : ℝ) else 0) * f u) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intros; ring
  rw [hsplit]
  -- First piece: ∑ u, 1[u ∈ e.others v] · f u = ∑ u ∈ e.others v, f u.
  have h1 : ∑ u, (if u ∈ e.others v then (1 : ℝ) else 0) * f u
          = ∑ u ∈ e.others v, f u := by
    have : ∀ u ∈ (Finset.univ : Finset V),
        (if u ∈ e.others v then (1 : ℝ) else 0) * f u
        = if u ∈ e.others v then f u else 0 := by
      intros u _; split_ifs <;> simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext u; simp
  rw [h1]
  -- Second piece: ∑ u, 1[u = v] · card · f u = card · f v.
  have h2 : ∑ u, (if u = v then ((e.others v).card : ℝ) else 0) * f u
          = ((e.others v).card : ℝ) * f v := by
    rw [Finset.sum_eq_single v]
    · simp
    · intros u _ hu; rw [if_neg hu, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h2]
  -- RHS: ∑ w ∈ e.others v, (f w - f v) = ∑ w, f w - card · f v.
  rw [Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_comm]

/-- `(laplacianMatrix H).mulVec f v = laplacianHyper H f v`. -/
theorem laplacianMatrix_mulVec (H : Hypergraph V) (f : V → ℝ) (v : V) :
    (laplacianMatrix H).mulVec f v = laplacianHyper H f v := by
  unfold laplacianMatrix laplacianHyper
  -- mulVec distributes over multiset sum of matrices.
  induction H.edges using Multiset.induction_on with
  | empty =>
    simp [Matrix.mulVec]
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [Matrix.add_mulVec, Pi.add_apply, ih, laplacianMatrixEdge_mulVec]

/-! ## Heat kernel -/

/-- `heatKernel H t = exp(t · laplacianMatrix H)`. With the sign convention of `laplacianHyper`
(negative semidefinite), `u(t) = heatKernel H t · u(0)` solves `∂_t u = Δ u`. -/
noncomputable def heatKernel (H : Hypergraph V) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp (t • laplacianMatrix H)

/-- `heatKernel H 0 = 1`. -/
theorem heatKernel_zero (H : Hypergraph V) :
    heatKernel H 0 = 1 := by
  unfold heatKernel
  simp [NormedSpace.exp_zero]

/-- `(heatKernel H 0).mulVec v = v`. -/
theorem heatKernel_zero_mulVec (H : Hypergraph V) (v : V → ℝ) :
    (heatKernel H 0).mulVec v = v := by
  rw [heatKernel_zero, Matrix.one_mulVec]

/-- `heatKernel H (s + t) = heatKernel H s * heatKernel H t`. The proof applies `exp_add_of_commute`
to the commuting matrices `s • L` and `t • L`. -/
theorem heatKernel_add (H : Hypergraph V) (s t : ℝ) :
    heatKernel H (s + t) = heatKernel H s * heatKernel H t := by
  unfold heatKernel
  have hcommute : Commute (s • laplacianMatrix H) (t • laplacianMatrix H) := by
    unfold Commute SemiconjBy
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm s t]
  rw [show ((s + t) • laplacianMatrix H)
          = (s • laplacianMatrix H) + (t • laplacianMatrix H) by
        rw [add_smul]]
  exact Matrix.exp_add_of_commute _ _ hcommute

/-- `(laplacianMatrix H).mulVec (fun _ => c) v = 0`. -/
theorem laplacianMatrix_mulVec_const (H : Hypergraph V) (c : ℝ) (v : V) :
    (laplacianMatrix H).mulVec (fun _ => c) v = 0 := by
  rw [laplacianMatrix_mulVec]
  exact laplacianHyper_const H c v

/-- `∑ u, laplacianMatrix H v u = 0` for every `v`. -/
theorem laplacianMatrix_row_sum (H : Hypergraph V) (v : V) :
    ∑ u, laplacianMatrix H v u = 0 := by
  have h := laplacianMatrix_mulVec_const H 1 v
  unfold Matrix.mulVec at h
  simp only [dotProduct, mul_one] at h
  exact h

/-- `laplacianMatrixEdge e v u = laplacianMatrixEdge e u v`. -/
theorem laplacianMatrixEdge_symm (e : Hyperedge V) (v u : V) :
    laplacianMatrixEdge e v u = laplacianMatrixEdge e u v := by
  unfold laplacianMatrixEdge
  by_cases huv : u = v
  · subst huv; rfl
  · have huv' : v ≠ u := fun h => huv h.symm
    rw [if_neg huv, if_neg huv']
    simp only [sub_zero]
    -- u ∈ e.others v iff v ∈ e.others u (both mean u,v both ∈ e.verts and u ≠ v).
    have h_iff : (u ∈ e.others v) ↔ (v ∈ e.others u) := by
      unfold Hyperedge.others
      constructor
      · intro h
        split_ifs at h with hv
        · rw [Finset.mem_erase] at h
          rw [if_pos h.2, Finset.mem_erase]
          exact ⟨huv', hv⟩
        · exact absurd h (Finset.notMem_empty u)
      · intro h
        split_ifs at h with hu
        · rw [Finset.mem_erase] at h
          rw [if_pos h.2, Finset.mem_erase]
          exact ⟨huv, hu⟩
        · exact absurd h (Finset.notMem_empty v)
    by_cases h : u ∈ e.others v
    · rw [if_pos h, if_pos (h_iff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (h_iff.mpr h'))]

/-- `laplacianMatrix H` is symmetric. -/
theorem laplacianMatrix_symm (H : Hypergraph V) :
    (laplacianMatrix H).IsSymm := by
  unfold Matrix.IsSymm laplacianMatrix
  funext u v
  simp only [Matrix.transpose_apply]
  -- Sum of matrices at (u, v) vs (v, u).
  show (H.edges.map laplacianMatrixEdge).sum v u
     = (H.edges.map laplacianMatrixEdge).sum u v
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Matrix.add_apply]
    rw [ih, laplacianMatrixEdge_symm e u v]

/-- `heatKernel H t` is symmetric. -/
theorem heatKernel_symm (H : Hypergraph V) (t : ℝ) :
    (heatKernel H t).IsSymm := by
  unfold heatKernel
  have h_sym : (t • laplacianMatrix H).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_smul, (laplacianMatrix_symm H).eq]
  exact h_sym.exp

/-- `heatKernel H (-t) = (heatKernel H t)⁻¹`. -/
theorem heatKernel_neg (H : Hypergraph V) (t : ℝ) :
    heatKernel H (-t) = (heatKernel H t)⁻¹ := by
  unfold heatKernel
  rw [neg_smul, Matrix.exp_neg]

/-- `heatKernel H t * heatKernel H (-t) = 1`. -/
theorem heatKernel_mul_heatKernel_neg (H : Hypergraph V) (t : ℝ) :
    heatKernel H t * heatKernel H (-t) = 1 := by
  rw [← heatKernel_add, add_neg_cancel, heatKernel_zero]

/-! ## Heat kernel trace -/

/-- The trace of `heatKernel H t`. Its behaviour `C · t^{−d_s/2}` for small `t` defines the spectral
dimension `d_s`. -/
noncomputable def heatTrace (H : Hypergraph V) (t : ℝ) : ℝ :=
  (heatKernel H t).trace

/-- `heatTrace H 0` equals the number of vertices. -/
theorem heatTrace_zero (H : Hypergraph V) :
    heatTrace H 0 = (Fintype.card V : ℝ) := by
  unfold heatTrace
  rw [heatKernel_zero, Matrix.trace_one]

end Hypergraph
end InfraFormalization
