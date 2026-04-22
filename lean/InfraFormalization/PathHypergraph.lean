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

/-- **Path-Dirichlet ground state is strictly negative.** For `n ≥ 1`
and `k = 0` (the first Dirichlet mode), the eigenvalue
`−4 sin²(π/(2(n+1)))` is strictly negative: the argument
`π/(2(n+1))` lies strictly between `0` and `π/2`, so its sine is
strictly positive, so its square is strictly positive.

Analog of `cycleEigenvalue_one_neg` for the path-Laplacian: the
Dirichlet ground state decays (does not drift), confirming the path
spectral gap. -/
theorem pathEigenvalue_zero_neg {n : ℕ} (hn : 1 ≤ n) :
    pathEigenvalue n 0 < 0 := by
  unfold pathEigenvalue
  -- `0 < π / (2(n+1)) < π/2` so `sin` is strictly positive there.
  have hn' : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have h_pos : (0 : ℝ) < Real.pi * (0 + 1) / (2 * (n + 1)) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h_two_pos : (0 : ℝ) < 2 * (n + 1) := by linarith
    positivity
  have h_lt : Real.pi * (0 + 1) / (2 * (n + 1)) < Real.pi := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h1 : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have h_denom_ge_two : (2 : ℝ) ≤ 2 * (n + 1) := by linarith
    have h_denom_pos : (0 : ℝ) < 2 * (n + 1) := by linarith
    rw [div_lt_iff₀ h_denom_pos]
    calc Real.pi * (0 + 1) = Real.pi * 1 := by ring
      _ = Real.pi := by ring
      _ < Real.pi * 2 := by linarith
      _ ≤ Real.pi * (2 * (n + 1)) := by nlinarith
  have h_sin_pos : 0 < Real.sin (Real.pi * (0 + 1) / (2 * (n + 1))) :=
    Real.sin_pos_of_pos_of_lt_pi h_pos h_lt
  have h_sq_pos : 0 < (Real.sin (Real.pi * (0 + 1) / (2 * (n + 1))))^2 := by
    positivity
  have : (0 : ℕ) + 1 = 1 := rfl
  push_cast
  nlinarith [h_sq_pos]

end InfraFormalization
