/-
**Hypergraph Laplacian as a matrix, and heat kernel via `Matrix.exp`** (task R2 / #177).

For a finite-vertex hypergraph `H : Hypergraph V` (`[Fintype V]`,
`[DecidableEq V]`), the Laplacian operator `laplacianHyper H` is a
linear map `(V → ℝ) → (V → ℝ)`, hence representable as a matrix
`Matrix V V ℝ`.

  * `laplacianMatrixEdge e`: the per-edge matrix contribution.
  * `laplacianMatrix H`: the full Laplacian matrix.
  * `laplacianMatrix_mulVec`: matrix action equals `laplacianHyper` action.
  * `heatKernel H t := exp(-t · Δ_H)`: heat propagator via Mathlib's
    matrix exponential.
  * `heatKernel_zero`, `heatKernel_add`: identity at `t = 0` and
    semigroup property.

This is Rung-3 of the bridge ladder: the heat equation now has a
closed-form propagator for finite hypergraphs.
-/

import InfraFormalization.HypergraphLaplacian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Per-edge matrix contribution** to the Laplacian.

For edge `e` and vertices `v, u : V`:
  * off-diagonal (`u ≠ v`): `1` if `u ∈ e.others v`, else `0`.
  * diagonal (`u = v`): `−|e.others v|`.

Satisfies `(laplacianMatrixEdge e).mulVec f v = ∑_{w ∈ e.others v} (f w − f v)`. -/
noncomputable def laplacianMatrixEdge (e : Hyperedge V) : Matrix V V ℝ :=
  fun v u =>
    (if u ∈ e.others v then (1 : ℝ) else 0)
    - (if u = v then ((e.others v).card : ℝ) else 0)

/-- **Full Laplacian matrix**: sum of per-edge matrices over `H.edges`. -/
noncomputable def laplacianMatrix (H : Hypergraph V) : Matrix V V ℝ :=
  (H.edges.map laplacianMatrixEdge).sum

/-- Matrix action of a per-edge Laplacian matches the per-edge Laplacian. -/
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

/-- **Matrix action = Laplacian action**: for any `f : V → ℝ`,
`(laplacianMatrix H).mulVec f v = laplacianHyper H f v`. -/
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

/-! ## Heat kernel via `Matrix.exp` -/

/-- **Heat kernel on a hypergraph**. Since `laplacianHyper H` is
negative-semidefinite (eigenvalues `≤ 0`) under our convention
(cycle gives `−4 sin²(π k / n)`), the heat equation `∂_t u = Δ u`
has solution `u(t) = exp(t · Δ) · u(0)`. The propagator is

  `heatKernel H t := exp(t · laplacianMatrix H) : Matrix V V ℝ`

(Mathlib's matrix exponential). -/
noncomputable def heatKernel (H : Hypergraph V) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp (t • laplacianMatrix H)

/-- **Heat kernel at `t = 0` is the identity.** -/
theorem heatKernel_zero (H : Hypergraph V) :
    heatKernel H 0 = 1 := by
  unfold heatKernel
  simp [NormedSpace.exp_zero]

/-- **Heat kernel at `t = 0` acts as identity on any initial data**.
For every vector `v : V → ℝ`, `(heatKernel H 0).mulVec v = v`. -/
theorem heatKernel_zero_mulVec (H : Hypergraph V) (v : V → ℝ) :
    (heatKernel H 0).mulVec v = v := by
  rw [heatKernel_zero, Matrix.one_mulVec]

/-- **Heat kernel semigroup**: `exp((s + t) Δ) = exp(s Δ) · exp(t Δ)`.

Both factors are matrix exponentials of commuting matrices (scalar
multiples of the same matrix), so the standard `exp_add_of_commute`
gives the result. -/
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

/-- **Laplacian matrix annihilates constants**: for any `c : ℝ`,
`(laplacianMatrix H).mulVec (fun _ => c) v = 0`. -/
theorem laplacianMatrix_mulVec_const (H : Hypergraph V) (c : ℝ) (v : V) :
    (laplacianMatrix H).mulVec (fun _ => c) v = 0 := by
  rw [laplacianMatrix_mulVec]
  exact laplacianHyper_const H c v

/-- **Laplacian matrix row-sum is zero**: for each `v : V`,
`∑ u, laplacianMatrix H v u = 0`. This is the matrix-level statement
of "the Laplacian kills constants," and implies that the all-ones
vector `fun _ => 1` lies in the kernel of `laplacianMatrix H`. -/
theorem laplacianMatrix_row_sum (H : Hypergraph V) (v : V) :
    ∑ u, laplacianMatrix H v u = 0 := by
  have h := laplacianMatrix_mulVec_const H 1 v
  unfold Matrix.mulVec at h
  simp only [dotProduct, mul_one] at h
  exact h

/-- **Per-edge Laplacian matrix is symmetric**: for each edge `e`,
`laplacianMatrixEdge e v u = laplacianMatrixEdge e u v` because
membership `u ∈ e.others v` is symmetric in `(u, v)` when `u ≠ v`,
and the diagonal `u = v` case reduces to `-|e.others v|` on both
sides. -/
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

/-- **Full Laplacian matrix is symmetric**: sum of symmetric
per-edge matrices is symmetric. -/
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

/-- **Heat kernel is symmetric.** Since `laplacianMatrix H` is symmetric,
`t • laplacianMatrix H` is symmetric, and `Matrix.exp` of a symmetric
matrix is symmetric (via `Matrix.IsSymm.exp`). -/
theorem heatKernel_symm (H : Hypergraph V) (t : ℝ) :
    (heatKernel H t).IsSymm := by
  unfold heatKernel
  have h_sym : (t • laplacianMatrix H).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_smul, (laplacianMatrix_symm H).eq]
  exact h_sym.exp

/-- **Heat kernel at `−t` is the inverse of heat kernel at `t`.**
Backward heat flow is the formal inverse of forward heat flow. -/
theorem heatKernel_neg (H : Hypergraph V) (t : ℝ) :
    heatKernel H (-t) = (heatKernel H t)⁻¹ := by
  unfold heatKernel
  rw [neg_smul, Matrix.exp_neg]

/-- **Heat kernel composed with its time-reversal is the identity**:
`heatKernel H t * heatKernel H (-t) = 1`. Direct consequence of
`heatKernel_add` at `s = t, t = -t` plus `heatKernel_zero`. -/
theorem heatKernel_mul_heatKernel_neg (H : Hypergraph V) (t : ℝ) :
    heatKernel H t * heatKernel H (-t) = 1 := by
  rw [← heatKernel_add, add_neg_cancel, heatKernel_zero]

/-! ## Heat kernel trace -/

/-- **Heat trace** `Tr(exp(−t Δ_H))`: the fundamental object whose
small-`t` asymptotics `Tr(exp(−t Δ)) ~ C · t^{−d_s/2}` defines the
**spectral dimension** of a hypergraph (task ID7). -/
noncomputable def heatTrace (H : Hypergraph V) (t : ℝ) : ℝ :=
  (heatKernel H t).trace

/-- **Heat trace at `t = 0`** equals the number of vertices: the
heat kernel at zero time is the identity matrix, whose trace is `|V|`. -/
theorem heatTrace_zero (H : Hypergraph V) :
    heatTrace H 0 = (Fintype.card V : ℝ) := by
  unfold heatTrace
  rw [heatKernel_zero, Matrix.trace_one]

end Hypergraph
end InfraFormalization
