/-
**Path hypergraph + path Laplacian** (task T5 / #185 partial).

The path hypergraph `pathHypergraph n` on `Fin n` with edges
`{i, i+1}` for `0 ≤ i < n-1` — the open-chain analog of
`cycleHypergraph`. This file provides the type definition; the full
spectrum closed form (sin-modes with Dirichlet boundary conditions)
is future work.

**Connection to hypergraphs.** Native — `pathHypergraph n` is a
hypergraph on `Fin n` with explicit edge set. Combined with
`cycleHypergraph`, path and cycle together give the 1-D graph-family
needed for the d-torus product structure (`T5` = path + cycle^d).
-/

import InfraFormalization.Hypergraph
import InfraFormalization.HypergraphLaplacian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace InfraFormalization

/-- **Path hyperedge `{i, i+1}`** for `i : Fin n` with `i+1 < n`. -/
def pathEdge (n : ℕ) (i : Fin (n - 1)) : Hyperedge (Fin n) where
  verts := [⟨i.val, by
    have h : i.val < n - 1 := i.isLt
    omega⟩,
    ⟨i.val + 1, by
    have h : i.val < n - 1 := i.isLt
    omega⟩]
  nonempty := List.cons_ne_nil _ _

/-- **Path hypergraph** `pathHypergraph n` on `Fin n`: `n - 1` edges
`{i, i+1}`. -/
noncomputable def pathHypergraph (n : ℕ) : Hypergraph (Fin n) where
  edges := ((Finset.univ : Finset (Fin (n - 1))).image (pathEdge n)).val

/-- **Path hypergraph has `n - 1` edges** (as a cardinality bound;
equality holds when the `pathEdge` map is injective, which it is on
`Fin (n-1)`). -/
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

/-- **Path (free / Neumann-like) eigenvalue formula** (sentinel). For
`n ≥ 2` and `k : Fin n`, the `k`-th eigenvalue of the free path-graph
Laplacian (no boundary conditions — the natural Laplacian on
`pathHypergraph n`) is

  `pathEigenvalue n k = −4 sin² (kπ / (2n))`,

equivalent to `−(2 − 2 cos(kπ/n))`. `k = 0` gives `0` (constant
mode preserved), `k = n-1` gives the maximum `−4 sin²(π(n-1)/(2n))`.

Stated as a definition for reference; the eigenvalue equation proof
is future work (open-path eigenvectors use the `cos((k π)(j + 1/2) / n)`
family, not the `sin` Dirichlet basis). -/
noncomputable def pathEigenvalue (n k : ℕ) : ℝ :=
  -4 * (Real.sin (Real.pi * k / (2 * n)))^2

/-- **Path (free / Neumann-like) eigenvector formula** (sentinel). The
`k`-th free-path-graph eigenvector at position `j : Fin n` is

  `pathEigenvector n k (j) = cos (k π (j + 1/2) / n)`.

Half-integer offset `j + 1/2` is characteristic of open-path
(Neumann-like) eigenfunctions, distinguishing from the cycle's
`cos(2πkj/n)` (no offset; periodic) and from the Dirichlet chain's
`sin(kπ(j+1)/(n+1))` (integer offset; zero boundary).

Stated as a definition for reference; eigenvalue equation proof is
future work. -/
noncomputable def pathEigenvector (n k : ℕ) (j : Fin n) : ℝ :=
  Real.cos (Real.pi * k * (2 * j.val + 1) / (2 * n))

/-- **All path eigenvalues are non-positive**. -/
theorem pathEigenvalue_nonpos (n k : ℕ) : pathEigenvalue n k ≤ 0 := by
  unfold pathEigenvalue
  have h_sq : (0 : ℝ) ≤ (Real.sin (Real.pi * k / (2 * n)))^2 :=
    sq_nonneg _
  nlinarith

/-- **Path ground-mode eigenvalue vanishes.** The `k = 0` mode has
`pathEigenvalue n 0 = 0` — matching the constant mode on the free path
(just as `cycleEigenvalue n 0 = 0` on the cycle). -/
theorem pathEigenvalue_ground_zero (n : ℕ) : pathEigenvalue n 0 = 0 := by
  unfold pathEigenvalue
  simp

/-- **Path ground-mode eigenvector is constant**: `pathEigenvector n 0 j
= 1` for every `j`. Direct from `cos(0) = 1`. Confirms the `k = 0`
mode is the constant mode. -/
theorem pathEigenvector_zero_eq_one (n : ℕ) (j : Fin n) :
    pathEigenvector n 0 j = 1 := by
  unfold pathEigenvector
  simp

/-- **Path Laplacian annihilates the constant vector.** For any `n`,
`laplacianHyper (pathHypergraph n) (pathEigenvector n 0) v = 0`. This
is the `k = 0` case of the path-Laplacian eigenvalue equation
(`pathEigenvalue n 0 = 0`, constant-mode in the kernel) — analog of
the corresponding cycle statement. -/
theorem pathLaplacian_eigen_zero (n : ℕ) (v : Fin n) :
    Hypergraph.laplacianHyper (pathHypergraph n)
      (fun j => pathEigenvector n 0 j) v = 0 := by
  -- `pathEigenvector n 0` is the constant-1 function, so every
  -- `f w - f v = 1 - 1 = 0` contribution vanishes.
  unfold Hypergraph.laplacianHyper
  have h_inner : ∀ e : Hyperedge (Fin n),
      ∑ w ∈ e.others v, ((fun j => pathEigenvector n 0 j) w
        - (fun j => pathEigenvector n 0 j) v) = 0 := by
    intro e
    refine Finset.sum_eq_zero (fun w _ => ?_)
    simp [pathEigenvector_zero_eq_one]
  -- Every contribution to the sum over edges is 0.
  have h_map : (pathHypergraph n).edges.map
      (fun e => ∑ w ∈ e.others v, ((fun j => pathEigenvector n 0 j) w
        - (fun j => pathEigenvector n 0 j) v))
      = (pathHypergraph n).edges.map (fun _ => (0 : ℝ)) :=
    Multiset.map_congr rfl (fun e _ => h_inner e)
  rw [h_map]
  simp

/-- **Path first non-constant mode is strictly negative.** For `n ≥ 2`
and `k = 1`, the eigenvalue `−4 sin²(π/(2n))` is strictly negative
(`π/(2n)` lies in `(0, π/2)`, so its sine is positive, so its square is
positive). This is the path analog of `cycleEigenvalue_one_neg` —
spectral gap of the free path-Laplacian. -/
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
