import InfraFormalization.HypergraphDistance
import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.WassersteinFinite

/-!
**Wasserstein-1 on the cycle hypergraph** (task #214 application /
foundation for task #18 A7).

Concrete link between the `wasserstein1` framework and the
`cycleHypergraph n` infrastructure. Uses the ℕ-valued hypergraph
distance cast to ℝ as the cost, and the uniform-1/n measure as
marginals.

  * `cycleMetric n` — real-valued distance on `Fin n` from
    `Hypergraph.dist (cycleHypergraph n)`.
  * `cycleUniform n` — uniform probability measure `1/n` on `Fin n`.
  * `cycleMetric_nonneg`, `cycleMetric_self`, `cycleMetric_symm` —
    the metric properties we need for W_1.
  * `cycleUniform_nonneg` — entries are non-negative.
  * `wasserstein1_cycleUniform_self` — W_1(μ_n, μ_n) = 0 on the
    cycle.

This instantiates the abstract Wasserstein framework on a concrete
hypergraph state and is the first piece of real infrastructure
downstream of `WassersteinFinite.lean`. Next-step targets:
  * W_1 between the uniform on `cycleHypergraph n` and the uniform
    on `cycleHypergraph (2n)` after embedding, bounding by 1/n
    (the A7 O(1/n) rate).
-/

namespace InfraFormalization

open scoped BigOperators

/-- **Real-valued cycle-hypergraph metric**: the ℕ-valued
`Hypergraph.dist` of `cycleHypergraph n` cast to ℝ. -/
noncomputable def cycleMetric (n : ℕ) [NeZero n] (i j : Fin n) : ℝ :=
  ((cycleHypergraph n).dist i j : ℝ)

/-- **`cycleMetric` is non-negative.** -/
theorem cycleMetric_nonneg (n : ℕ) [NeZero n] (i j : Fin n) :
    0 ≤ cycleMetric n i j := by
  unfold cycleMetric
  exact_mod_cast Nat.zero_le _

/-- **`cycleMetric i i = 0`.** -/
theorem cycleMetric_self (n : ℕ) [NeZero n] (i : Fin n) :
    cycleMetric n i i = 0 := by
  unfold cycleMetric
  simp

/-- **`cycleMetric` is symmetric.** -/
theorem cycleMetric_symm (n : ℕ) [NeZero n] (i j : Fin n) :
    cycleMetric n i j = cycleMetric n j i := by
  unfold cycleMetric
  rw [Hypergraph.dist_comm]

/-- **Uniform probability measure** on `Fin n`: `1/n` per vertex. -/
noncomputable def cycleUniform (n : ℕ) : Fin n → ℝ :=
  fun _ => (1 : ℝ) / n

/-- **`cycleUniform` entries are non-negative.** -/
theorem cycleUniform_nonneg (n : ℕ) (i : Fin n) : 0 ≤ cycleUniform n i := by
  unfold cycleUniform
  exact div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le _)

/-- **Total mass of `cycleUniform n`** is `1` when `n ≥ 1`. -/
theorem cycleUniform_total (n : ℕ) (hn : 1 ≤ n) :
    ∑ i : Fin n, cycleUniform n i = 1 := by
  unfold cycleUniform
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp

/-- **W_1(μ_n, μ_n) = 0 on the cycle**: the uniform measure is at
zero Wasserstein distance from itself. Instantiation of the generic
`wasserstein1_self_eq_zero` theorem on `(cycleMetric n, cycleUniform n)`. -/
theorem wasserstein1_cycleUniform_self (n : ℕ) [NeZero n] :
    wasserstein1 (cycleMetric n) (cycleUniform n) (cycleUniform n) = 0 :=
  wasserstein1_self_eq_zero
    (cycleMetric n)
    (cycleMetric_nonneg n)
    (cycleMetric_self n)
    (cycleUniform n)
    (cycleUniform_nonneg n)

/-- **W_1 between two Dirac deltas on the cycle equals the cycle
graph distance.** Hypergraph-anchored instantiation of
`wasserstein1_delta_eq_dist`: the finite metric space is
`(Fin n, cycleMetric n)`, which is entirely defined from
`cycleHypergraph n` (distance = shortest-path in the clique-expansion
graph of the hypergraph). Both sides of the identity are
computable from the hypergraph data alone. -/
theorem wasserstein1_cycleDelta_eq_hypergraphDist
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (cycleMetric n) (delta i) (delta j)
      = ((cycleHypergraph n).dist i j : ℝ) := by
  rw [wasserstein1_delta_eq_dist]
  rfl

end InfraFormalization
