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

/-- **Path-Dirichlet eigenvalue formula** (sentinel). For `n ≥ 2` and
`k : Fin n`, the `k`-th Dirichlet-boundary path-Laplacian eigenvalue is

  `pathEigenvalue n k = −4 sin² (π(k+1) / (2(n+1)))`.

Stated as a definition for reference; the eigenvalue equation proof
is future work. -/
noncomputable def pathEigenvalue (n k : ℕ) : ℝ :=
  -4 * (Real.sin (Real.pi * (k + 1) / (2 * (n + 1))))^2

/-- **Path-Dirichlet eigenvector formula** (sentinel). The `k`-th
Dirichlet eigenvector at position `j : Fin n` is

  `pathEigenvector n k (j) = sin (π(k+1)(j+1) / (n+1))`.

Stated as a definition for reference; eigenvalue equation proof is
future work. -/
noncomputable def pathEigenvector (n k : ℕ) (j : Fin n) : ℝ :=
  Real.sin (Real.pi * (k + 1) * (j.val + 1) / (n + 1))

/-- **All path eigenvalues are non-positive**. -/
theorem pathEigenvalue_nonpos (n k : ℕ) : pathEigenvalue n k ≤ 0 := by
  unfold pathEigenvalue
  have h_sq : (0 : ℝ) ≤ (Real.sin (Real.pi * (k + 1) / (2 * (n + 1))))^2 :=
    sq_nonneg _
  nlinarith

end InfraFormalization
