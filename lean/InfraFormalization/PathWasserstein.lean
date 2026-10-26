import InfraFormalization.WassersteinFinite
import InfraFormalization.PathHypergraph
import InfraFormalization.PathHypergraphDistance
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
Wasserstein-1 distance on the path hypergraph.

This module specialises the finite Wasserstein-1 distance `wasserstein1` of `WassersteinFinite.lean`
to `Fin n` with the shortest-path metric `pathMetric n` of `pathHypergraph n` and with the scaled
metric `pathMetricScaled n = pathMetric n / n`. It proves that `pathMetric n` is a metric bounded by
`n`, that W₁ between two Dirac measures equals the graph distance (divided by `n` in the scaled
case), that W₁ between probability measures is at most `n` (at most 1 in the scaled case), and that
adjacent vertices are at distance 1 (`1/n` scaled).
-/

namespace InfraFormalization

open scoped BigOperators

/-- The shortest-path distance in `pathHypergraph n`, cast to ℝ. -/
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

/-- For `n ≥ 1`, `pathMetric n` satisfies the triangle inequality. -/
theorem pathMetric_triangle {n : ℕ} [NeZero n] (i j k : Fin n) :
    pathMetric n i k ≤ pathMetric n i j + pathMetric n j k := by
  unfold pathMetric
  have hconn := pathHypergraph_connected (n := n)
  have := Hypergraph.dist_triangle _ hconn i j k
  exact_mod_cast this

/-- W₁ between the Dirac measures at `i` and `j` under `pathMetric n` equals the graph distance
between `i` and `j` in `pathHypergraph n`. -/
theorem wasserstein1_pathDelta_eq_hypergraphDist
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (pathMetric n) (delta i) (delta j)
      = ((pathHypergraph n).dist i j : ℝ) := by
  rw [wasserstein1_delta_eq_dist]
  rfl

/-! ## Diameter bounds and the scaled metric -/

/-- `pathMetric n i j ≤ n`. The diameter of the path is `n - 1`. -/
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

/-- For probability measures `μ`, `ν` on `Fin n`, W₁ under `pathMetric n` is at most `n`. -/
theorem wasserstein1_pathMetric_le_card
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (pathMetric n) μ ν ≤ n := by
  refine wasserstein1_le_sup (pathMetric n) n ?_
    (pathMetric_le_card n) (pathMetric_nonneg n) μ ν hμ hν hμsum hνsum
  exact_mod_cast Nat.zero_le _

/-- `pathMetric n i j / n`. -/
noncomputable def pathMetricScaled (n : ℕ) [NeZero n] (i j : Fin n) : ℝ :=
  pathMetric n i j / n

theorem pathMetricScaled_nonneg (n : ℕ) [NeZero n] (i j : Fin n) :
    0 ≤ pathMetricScaled n i j := by
  unfold pathMetricScaled
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le _
  exact div_nonneg (pathMetric_nonneg n i j) hn

/-- `pathMetricScaled n i j ≤ 1`. -/
theorem pathMetricScaled_le_one (n : ℕ) [NeZero n] (i j : Fin n) :
    pathMetricScaled n i j ≤ 1 := by
  unfold pathMetricScaled
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  rw [div_le_one hn_pos]
  exact pathMetric_le_card n i j

/-- For probability measures `μ`, `ν` on `Fin n`, W₁ under `pathMetricScaled n` is at most 1. -/
theorem wasserstein1_pathMetricScaled_le_one
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (pathMetricScaled n) μ ν ≤ 1 :=
  wasserstein1_le_sup (pathMetricScaled n) 1 zero_le_one
    (pathMetricScaled_le_one n) (pathMetricScaled_nonneg n)
    μ ν hμ hν hμsum hνsum

/-- W₁ between the Dirac measures at `i` and `j` under `pathMetricScaled n` equals the graph
distance
divided by `n`. -/
theorem wasserstein1_pathDelta_scaled_eq
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (pathMetricScaled n) (delta i) (delta j)
      = ((pathHypergraph n).dist i j : ℝ) / n := by
  rw [wasserstein1_delta_eq_dist]
  rfl

/-! ## Adjacent vertices

For `i.val + 1 = j.val`, the graph distance is 1, W₁ between the Dirac measures is 1, and the scaled
values are `1/n`. -/

/-- If `i.val + 1 = j.val`, then `pathMetric n i j = 1`. -/
theorem pathMetric_succ_eq_one (n : ℕ) [NeZero n] (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    pathMetric n i j = 1 := by
  unfold pathMetric Hypergraph.dist
  have hne : i ≠ j := by
    intro h; subst h; omega
  have hadj : (pathHypergraph n).Adj i j :=
    (pathHypergraph_Adj_iff n i j).mpr ⟨hne, Or.inl hij⟩
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, Nat.cast_one]

/-- If `i.val + 1 = j.val`, then `pathMetricScaled n i j = 1/n`. -/
theorem pathMetricScaled_succ_eq (n : ℕ) [NeZero n] (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    pathMetricScaled n i j = 1 / n := by
  unfold pathMetricScaled
  rw [pathMetric_succ_eq_one n i j hij]

/-- If `i.val + 1 = j.val`, then W₁ between the Dirac measures at `i` and `j` under `pathMetric n`
is 1. -/
theorem wasserstein1_pathDelta_succ
    (n : ℕ) [NeZero n] (i j : Fin n) (hij : i.val + 1 = j.val) :
    wasserstein1 (pathMetric n) (delta i) (delta j) = 1 := by
  rw [wasserstein1_delta_eq_dist]
  show pathMetric n i j = 1
  exact pathMetric_succ_eq_one n i j hij

/-- If `i.val + 1 = j.val`, then W₁ between the Dirac measures at `i` and `j` under
`pathMetricScaled n` is `1/n`. -/
theorem wasserstein1_pathDelta_scaled_succ
    (n : ℕ) [NeZero n] (i j : Fin n) (hij : i.val + 1 = j.val) :
    wasserstein1 (pathMetricScaled n) (delta i) (delta j) = 1 / n := by
  rw [wasserstein1_delta_eq_dist]
  show pathMetricScaled n i j = 1 / n
  exact pathMetricScaled_succ_eq n i j hij

end InfraFormalization
