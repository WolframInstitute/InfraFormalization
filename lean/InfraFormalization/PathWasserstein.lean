import InfraFormalization.WassersteinFinite
import InfraFormalization.PathHypergraph
import InfraFormalization.PathHypergraphDistance
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
**Path-hypergraph Wasserstein distance** (task #214 consumer site).

Hypergraph-anchored consumer site for the abstract W_1 framework on
`pathHypergraph n` — the open-chain analog of `cycleHypergraph n`.

Provides:
  * `pathMetric n`, `pathMetric_nonneg`, `pathMetric_self`,
    `pathMetric_symm`, `pathMetric_triangle`.
  * `pathMetricScaled n = pathMetric / (n-1)` (diameter-normalised).
  * `wasserstein1_pathDelta_eq_hypergraphDist` — sharp δ-to-δ identity
    naming the hypergraph distance.

Since `pathHypergraph` has no wrap-around, the cyclic shift story does
not apply. Path is the direct-limit analog: W_1 between adjacent
Diracs is the unit edge-length.

Grounding convention: the abstract `wasserstein1` lives in
`WassersteinFinite.lean` (pure discrete, no hypergraph anchor in the
type signature). Here we specialise to `(Fin n, pathMetric n)`, which
is entirely built from `pathHypergraph n` — no continuum content.
-/

namespace InfraFormalization

open scoped BigOperators

/-- **Path hypergraph graph metric**: shortest-path distance in
`pathHypergraph n`, cast to ℝ. -/
noncomputable def pathMetric (n : ℕ) (i j : Fin n) : ℝ :=
  ((pathHypergraph n).dist i j : ℝ)

theorem pathMetric_nonneg (n : ℕ) (i j : Fin n) : 0 ≤ pathMetric n i j := by
  unfold pathMetric
  exact_mod_cast Nat.zero_le _

theorem pathMetric_self (n : ℕ) (i : Fin n) : pathMetric n i i = 0 := by
  unfold pathMetric
  simp

theorem pathMetric_symm (n : ℕ) (i j : Fin n) :
    pathMetric n i j = pathMetric n j i := by
  unfold pathMetric
  rw [Hypergraph.dist_comm]

/-- **Path metric triangle inequality** via `pathHypergraph_connected`
(which holds for `n ≥ 1`). -/
theorem pathMetric_triangle {n : ℕ} [NeZero n] (i j k : Fin n) :
    pathMetric n i k ≤ pathMetric n i j + pathMetric n j k := by
  unfold pathMetric
  have hconn := pathHypergraph_connected (n := n)
  have := Hypergraph.dist_triangle _ hconn i j k
  exact_mod_cast this

/-- **W_1 between two Dirac deltas on the path equals the path graph
distance.** Hypergraph-anchored instantiation of
`wasserstein1_delta_eq_dist`: the finite metric space is
`(Fin n, pathMetric n)`, which is entirely defined from
`pathHypergraph n`. Both sides of the identity are computable
from the hypergraph data alone. -/
theorem wasserstein1_pathDelta_eq_hypergraphDist
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (pathMetric n) (delta i) (delta j)
      = ((pathHypergraph n).dist i j : ℝ) := by
  rw [wasserstein1_delta_eq_dist]
  rfl

end InfraFormalization
