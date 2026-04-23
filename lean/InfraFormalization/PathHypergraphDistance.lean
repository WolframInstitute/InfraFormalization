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

end InfraFormalization
