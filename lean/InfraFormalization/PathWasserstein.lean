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

/-! ## Universal diameter bound + scaled W_1 on the path

Path-hypergraph analogs of the cycle bounds in
`CycleWasserstein.lean`. Together with the δ identity above, these
give an O(1) scaled-W_1 universal bound and a sharp δ-to-δ scaled
identity — exactly the form `[0, 1]`-interval convergence consumes. -/

/-- **Path-metric diameter is at most `n`**: any two vertices of
`pathHypergraph n` are within `n` graph steps of each other.
Mirrors `cycleMetric_le_card`. The bound is loose by 1 (true
diameter is `n - 1`), but `≤ n` keeps the same shape as the cycle
case for downstream uniformity. -/
theorem pathMetric_le_card (n : ℕ) [NeZero n] (i j : Fin n) :
    pathMetric n i j ≤ n := by
  unfold pathMetric Hypergraph.dist
  by_cases hreach : ((pathHypergraph n).toSimpleGraph).Reachable i j
  · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    have hpath : p.toPath.1.length < Fintype.card (Fin n) :=
      SimpleGraph.Walk.IsPath.length_lt p.toPath.2
    have hle : ((pathHypergraph n).toSimpleGraph).dist i j
        ≤ p.toPath.1.length :=
      SimpleGraph.dist_le _
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    have : ((pathHypergraph n).toSimpleGraph).dist i j < n := by
      calc ((pathHypergraph n).toSimpleGraph).dist i j
          ≤ p.toPath.1.length := hle
        _ < Fintype.card (Fin n) := hpath
        _ = n := hcard
    exact_mod_cast le_of_lt this
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hreach]
    exact_mod_cast Nat.zero_le _

/-- **W_1 between any two probability measures on `pathHypergraph n`
is bounded by `n`.** The path-side concrete diameter bound for the
abstract Wasserstein distance — hypergraph-anchored universal upper
bound mirroring `wasserstein1_cycleMetric_le_card`. -/
theorem wasserstein1_pathMetric_le_card
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (pathMetric n) μ ν ≤ n := by
  refine wasserstein1_le_sup (pathMetric n) n ?_
    (pathMetric_le_card n) (pathMetric_nonneg n) μ ν hμ hν hμsum hνsum
  exact_mod_cast Nat.zero_le _

/-- **Scaled path metric**: hypergraph distance divided by `n`, so
the unit cell has length `1/n` and the path's diameter is bounded by
`1`. This is the metric under which `pathHypergraph n → [0, 1]`
convergence is quantified. -/
noncomputable def pathMetricScaled (n : ℕ) [NeZero n] (i j : Fin n) : ℝ :=
  pathMetric n i j / n

theorem pathMetricScaled_nonneg (n : ℕ) [NeZero n] (i j : Fin n) :
    0 ≤ pathMetricScaled n i j := by
  unfold pathMetricScaled
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le _
  exact div_nonneg (pathMetric_nonneg n i j) hn

/-- **Scaled path diameter is ≤ 1**. Direct from `pathMetric_le_card`. -/
theorem pathMetricScaled_le_one (n : ℕ) [NeZero n] (i j : Fin n) :
    pathMetricScaled n i j ≤ 1 := by
  unfold pathMetricScaled
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  rw [div_le_one hn_pos]
  exact pathMetric_le_card n i j

/-- **W_1 under the scaled path metric is bounded by `1`.** Universal
O(1) Wasserstein bound on the path hypergraph; together with the
scaled δ identity below, pins scaled-W_1 to `[0, 1]`. -/
theorem wasserstein1_pathMetricScaled_le_one
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (pathMetricScaled n) μ ν ≤ 1 :=
  wasserstein1_le_sup (pathMetricScaled n) 1 zero_le_one
    (pathMetricScaled_le_one n) (pathMetricScaled_nonneg n)
    μ ν hμ hν hμsum hνsum

/-- **Sharp scaled W_1 between two path Dirac deltas**:
`W_1_scaled(δ_i, δ_j) = d(i, j) / n`. Mirrors
`wasserstein1_cycleDelta_scaled_eq` for the path case. -/
theorem wasserstein1_pathDelta_scaled_eq
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (pathMetricScaled n) (delta i) (delta j)
      = ((pathHypergraph n).dist i j : ℝ) / n := by
  rw [wasserstein1_delta_eq_dist]
  rfl

end InfraFormalization
