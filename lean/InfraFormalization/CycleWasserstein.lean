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

/-- **Cycle-metric diameter is at most `n`**: any two vertices of
`cycleHypergraph n` are within `n` graph steps of each other. Weak but
easy; tighter bound `⌊n/2⌋` uses the cycle's two-way connectivity. -/
theorem cycleMetric_le_card (n : ℕ) [NeZero n] (i j : Fin n) :
    cycleMetric n i j ≤ n := by
  unfold cycleMetric Hypergraph.dist
  by_cases hreach : ((cycleHypergraph n).toSimpleGraph).Reachable i j
  · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    have hpath : p.toPath.1.length < Fintype.card (Fin n) :=
      SimpleGraph.Walk.IsPath.length_lt p.toPath.2
    have hle : ((cycleHypergraph n).toSimpleGraph).dist i j
        ≤ p.toPath.1.length :=
      SimpleGraph.dist_le _
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    have : ((cycleHypergraph n).toSimpleGraph).dist i j < n := by
      calc ((cycleHypergraph n).toSimpleGraph).dist i j
          ≤ p.toPath.1.length := hle
        _ < Fintype.card (Fin n) := hpath
        _ = n := hcard
    exact_mod_cast le_of_lt this
  · -- Unreachable: SimpleGraph.dist is 0 ≤ n.
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hreach]
    exact_mod_cast Nat.zero_le _

/-- **W_1 between any two probability measures on `cycleHypergraph n`
is bounded by `n`.** Concrete diameter bound applied to the
cycle-hypergraph Wasserstein metric — hypergraph-anchored universal
upper bound. -/
theorem wasserstein1_cycleMetric_le_card
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (cycleMetric n) μ ν ≤ n := by
  refine wasserstein1_le_sup (cycleMetric n) n ?_
    (cycleMetric_le_card n) (cycleMetric_nonneg n) μ ν hμ hν hμsum hνsum
  exact_mod_cast Nat.zero_le _

/-- **Scaled cycle metric**: the hypergraph distance divided by `n`,
so that the unit cell has length `1/n` and the full cycle has
"circumference" bounded by `1`. This is the metric under which
`cycleHypergraph n → S¹` convergence can be quantified. -/
noncomputable def cycleMetricScaled (n : ℕ) [NeZero n] (i j : Fin n) : ℝ :=
  cycleMetric n i j / n

theorem cycleMetricScaled_nonneg (n : ℕ) [NeZero n] (i j : Fin n) :
    0 ≤ cycleMetricScaled n i j := by
  unfold cycleMetricScaled
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le _
  exact div_nonneg (cycleMetric_nonneg n i j) hn

/-- **Scaled cycle diameter is ≤ 1**: under `cycleMetricScaled n`, any
two vertices are within unit distance. Direct consequence of
`cycleMetric_le_card` (the unscaled diameter is ≤ n). -/
theorem cycleMetricScaled_le_one (n : ℕ) [NeZero n] (i j : Fin n) :
    cycleMetricScaled n i j ≤ 1 := by
  unfold cycleMetricScaled
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  rw [div_le_one hn_pos]
  exact cycleMetric_le_card n i j

/-- **W_1 under the scaled cycle metric is bounded by `1`.** Universal
O(1) Wasserstein bound on the cycle hypergraph. Along with the delta
identity (`wasserstein1_cycleDelta_eq_hypergraphDist`) this pins W_1
to the range `[0, 1]` under scaling, matching the unit-circle limit. -/
theorem wasserstein1_cycleMetricScaled_le_one
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (cycleMetricScaled n) μ ν ≤ 1 :=
  wasserstein1_le_sup (cycleMetricScaled n) 1 zero_le_one
    (cycleMetricScaled_le_one n) (cycleMetricScaled_nonneg n)
    μ ν hμ hν hμsum hνsum

/-- **Sharp scaled W_1 between two cycle Dirac deltas**:
`W_1_scaled(δ_i, δ_j) = d(i,j) / n` on `cycleHypergraph n`, where `d`
is the hypergraph graph distance. Combines the abstract δ identity
with the `/n` scaling — the entire range `[0, ⌊n/2⌋/n]` of observed
W_1_scaled values is indexed by hypergraph-graph distance. -/
theorem wasserstein1_cycleDelta_scaled_eq
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (cycleMetricScaled n) (delta i) (delta j)
      = ((cycleHypergraph n).dist i j : ℝ) / n := by
  rw [wasserstein1_delta_eq_dist]
  rfl

/-! ## Sharp O(1/n) Wasserstein identity for adjacent Dirac measures -/

/-- **Distance between adjacent cycle vertices is exactly `1`.** The
edge `{v, v+1}` of `cycleHypergraph n` makes them adjacent in the
clique-expansion graph, so the shortest path has length 1. -/
theorem cycleMetric_succ_eq_one (n : ℕ) [NeZero n] (hn : 2 ≤ n) (v : Fin n) :
    cycleMetric n v (v + 1) = 1 := by
  unfold cycleMetric Hypergraph.dist
  have hadj : (cycleHypergraph n).Adj v (v + 1) :=
    (cycleHypergraph_succ_pred_adj hn v).1
  have : ((cycleHypergraph n).toSimpleGraph).dist v (v + 1) = 1 := by
    rw [SimpleGraph.dist_eq_one_iff_adj]
    exact hadj
  rw [this]
  norm_cast

/-- **Scaled distance between adjacent cycle vertices is `1/n`.**
Direct consequence of `cycleMetric_succ_eq_one` and the `/ n` scaling. -/
theorem cycleMetricScaled_succ_eq (n : ℕ) [NeZero n] (hn : 2 ≤ n) (v : Fin n) :
    cycleMetricScaled n v (v + 1) = 1 / n := by
  unfold cycleMetricScaled
  rw [cycleMetric_succ_eq_one n hn v]

/-- **Sharp A7 identity on the cycle**: the Wasserstein-1 distance
between two adjacent Dirac deltas on `cycleHypergraph n`, under the
scaled cycle metric, is exactly `1/n`. Combines
`wasserstein1_delta_eq_dist` (abstract) with
`cycleMetricScaled_succ_eq` (hypergraph-anchored). **First genuinely
O(1/n) Wasserstein rate in the project**, all from explicit
hypergraph data. -/
theorem wasserstein1_cycleDelta_succ
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (v : Fin n) :
    wasserstein1 (cycleMetricScaled n) (delta v) (delta (v + 1))
      = 1 / n := by
  rw [wasserstein1_delta_eq_dist]
  exact cycleMetricScaled_succ_eq n hn v

/-! ## Measure-level O(1/n) bound: shift plan for general probability measures -/

/-- **Shift-forward measure** `shiftMeasure n μ j := μ (j + 1)`.
Rotates the measure one step on the cycle. As `Fin n` addition is
modular, this is a bijection-induced pushforward, preserving total
mass. -/
noncomputable def shiftMeasure (n : ℕ) [NeZero n] (μ : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j => μ (j + 1)

theorem shiftMeasure_nonneg (n : ℕ) [NeZero n]
    {μ : Fin n → ℝ} (hμ : ∀ i, 0 ≤ μ i) (j : Fin n) :
    0 ≤ shiftMeasure n μ j := hμ _

/-- **Total mass is preserved** by `shiftMeasure` (reindexing via the
bijection `j ↦ j + 1` on `Fin n`). -/
theorem shiftMeasure_total (n : ℕ) [NeZero n] (μ : Fin n → ℝ) :
    ∑ j : Fin n, shiftMeasure n μ j = ∑ i : Fin n, μ i := by
  unfold shiftMeasure
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n)) μ

/-- **Shift plan** between `μ` and `shiftMeasure n μ` on
`cycleHypergraph n`: puts mass `μ i` on the `(i, i-1)` slot and zero
elsewhere. Row marginal at `i` picks up the `j = i - 1` slot only,
giving `μ i`; column marginal at `j` picks up the `i = j + 1` slot
only, giving `μ (j+1) = shiftMeasure μ j`. -/
noncomputable def shiftPlan (n : ℕ) [NeZero n]
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    TransportPlan μ (shiftMeasure n μ) where
  π := fun i j => if j + 1 = i then μ i else 0
  nonneg := fun i j => by
    by_cases h : j + 1 = i
    · simp [h, hμ i]
    · simp [h]
  rowMarginal := fun i => by
    rw [Finset.sum_eq_single (i - 1)]
    · have : (i - 1) + 1 = i := by abel
      simp [this]
    · intros j _ hj
      have : j + 1 ≠ i := by
        intro heq
        apply hj
        have : j = i - 1 := by rw [← heq]; abel
        exact this
      simp [this]
    · intro hne
      exact absurd (Finset.mem_univ _) hne
  colMarginal := fun j => by
    rw [Finset.sum_eq_single (j + 1)]
    · simp
      rfl
    · intros i _ hi
      have : j + 1 ≠ i := fun heq => hi heq.symm
      simp [this]
    · intro hne
      exact absurd (Finset.mem_univ _) hne

/-- **Cost of the shift plan under `cycleMetric` is at most the
total mass**: each unit of mass moves exactly one adjacent step
(distance 1), so the total cost equals the sum of `μ`. -/
theorem shiftPlan_cost_cycleMetric
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    (shiftPlan n μ hμ).cost (cycleMetric n) = ∑ i, μ i := by
  unfold TransportPlan.cost shiftPlan
  simp only
  refine Finset.sum_congr rfl ?_
  intros i _
  rw [Finset.sum_eq_single (i - 1)]
  · have hsum : (i - 1) + 1 = i := by abel
    have hadj : cycleMetric n i (i - 1) = 1 := by
      have h1 : cycleMetric n (i - 1) ((i - 1) + 1) = 1 :=
        cycleMetric_succ_eq_one n hn (i - 1)
      rw [hsum] at h1
      rw [cycleMetric_symm]
      exact h1
    rw [if_pos hsum, hadj, mul_one]
  · intros j _ hj
    have : j + 1 ≠ i := by
      intro heq
      apply hj
      have : j = i - 1 := by rw [← heq]; abel
      exact this
    rw [if_neg this, zero_mul]
  · intro hne
    exact absurd (Finset.mem_univ _) hne

/-- **Cost of the shift plan under `cycleMetric` is 1** for
probability measures. -/
theorem shiftPlan_cost_cycleMetric_one
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1) :
    (shiftPlan n μ hμ).cost (cycleMetric n) = 1 := by
  rw [shiftPlan_cost_cycleMetric n hn μ hμ]
  exact hμsum

/-- **W_1 under the scaled cycle metric, between any probability
measure and its shift, is at most `1/n`.** Full A7 measure-level
O(1/n) rate: for any probability measure `μ`,
`W_1_scaled(μ, μ ∘ (·+1)) ≤ 1/n`. Proof: instantiate the shift plan,
compute cost = `1` unscaled = `1/n` scaled, apply `csInf_le`. -/
theorem wasserstein1_shiftMeasure_le (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1) :
    wasserstein1 (cycleMetricScaled n) μ (shiftMeasure n μ) ≤ 1 / n := by
  unfold wasserstein1
  refine csInf_le ⟨0, ?_⟩ ?_
  · rintro c ⟨q, rfl⟩
    exact q.cost_nonneg (cycleMetricScaled n) (cycleMetricScaled_nonneg n)
  · refine ⟨shiftPlan n μ hμ, ?_⟩
    -- cost_scaled = (1/n) · cost_unscaled = (1/n) · 1 = 1/n
    unfold TransportPlan.cost cycleMetricScaled
    -- ∑_i ∑_j π(i,j) * (d i j / n) = (∑_i ∑_j π(i,j) * d i j) / n
    have h_unscaled : (shiftPlan n μ hμ).cost (cycleMetric n) = 1 :=
      shiftPlan_cost_cycleMetric_one n hn μ hμ hμsum
    have h_rewrite : (∑ i, ∑ j, (shiftPlan n μ hμ).π i j *
        (cycleMetric n i j / n))
        = (∑ i, ∑ j, (shiftPlan n μ hμ).π i j * cycleMetric n i j) / n := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intros i _
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intros j _
      ring
    rw [h_rewrite]
    have : (∑ i, ∑ j, (shiftPlan n μ hμ).π i j * cycleMetric n i j) = 1 := by
      show (shiftPlan n μ hμ).cost (cycleMetric n) = 1
      exact h_unscaled
    rw [this]

/-- **`cycleMetric` triangle inequality** — inherited from the
underlying hypergraph-distance triangle inequality
(`cycleHypergraph_dist_triangle` for `n ≥ 2`). -/
theorem cycleMetric_triangle (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (i j k : Fin n) :
    cycleMetric n i k ≤ cycleMetric n i j + cycleMetric n j k := by
  unfold cycleMetric
  have := cycleHypergraph_dist_triangle hn i j k
  exact_mod_cast this

/-- **`cycleMetricScaled` triangle inequality** — triangle inequality
survives division by the positive constant `n`. -/
theorem cycleMetricScaled_triangle (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (i j k : Fin n) :
    cycleMetricScaled n i k
      ≤ cycleMetricScaled n i j + cycleMetricScaled n j k := by
  unfold cycleMetricScaled
  have htri := cycleMetric_triangle n hn i j k
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [show cycleMetric n i j / (n : ℝ) + cycleMetric n j k / (n : ℝ)
        = (cycleMetric n i j + cycleMetric n j k) / n by ring]
  exact div_le_div_of_nonneg_right htri hnpos.le

/-- **`cycleMetricScaled` self-distance is zero.** -/
theorem cycleMetricScaled_self (n : ℕ) [NeZero n] (i : Fin n) :
    cycleMetricScaled n i i = 0 := by
  unfold cycleMetricScaled
  rw [cycleMetric_self]
  simp

/-- **Iterated forward shift** on the cycle — `shiftIter n μ k j = μ(j+k)`.
Iteratively applies `shiftMeasure` `k` times. -/
noncomputable def shiftIter (n : ℕ) [NeZero n]
    (μ : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => μ
  | k+1 => shiftMeasure n (shiftIter n μ k)

theorem shiftIter_nonneg (n : ℕ) [NeZero n]
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    ∀ k (j : Fin n), 0 ≤ shiftIter n μ k j
  | 0, j => hμ j
  | k+1, j => by
      unfold shiftIter
      exact shiftMeasure_nonneg n (shiftIter_nonneg n μ hμ k) j

theorem shiftIter_total (n : ℕ) [NeZero n]
    (μ : Fin n → ℝ) (hμsum : ∑ i, μ i = 1) :
    ∀ k, ∑ j, shiftIter n μ k j = 1
  | 0 => hμsum
  | k+1 => by
      unfold shiftIter
      rw [shiftMeasure_total]
      exact shiftIter_total n μ hμsum k

/-- **k-step shift rate**: for any probability measure `μ` on the
cycle, `W_1_scaled(μ, μ ∘ (·+k)) ≤ k/n`. Proof by induction on `k`,
using `wasserstein1_triangle` + the 1-step bound
`wasserstein1_shiftMeasure_le`. -/
theorem wasserstein1_shiftIter_le (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ∀ (k : ℕ) (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
      (hμsum : ∑ i, μ i = 1),
    wasserstein1 (cycleMetricScaled n) μ (shiftIter n μ k) ≤ (k : ℝ) / n
  | 0, μ, hμ, hμsum => by
      unfold shiftIter
      simp only [Nat.cast_zero, zero_div]
      exact (wasserstein1_self_eq_zero (cycleMetricScaled n)
        (cycleMetricScaled_nonneg n) (fun x => cycleMetricScaled_self n x)
        μ hμ).le
  | k+1, μ, hμ, hμsum => by
      unfold shiftIter
      -- W_1(μ, shift(shift^k μ)) ≤ W_1(μ, shift^k μ) + W_1(shift^k μ, shift(shift^k μ))
      -- ≤ k/n + 1/n = (k+1)/n
      have hIH := wasserstein1_shiftIter_le n hn k μ hμ hμsum
      have hν_nn : ∀ i, 0 ≤ shiftIter n μ k i := shiftIter_nonneg n μ hμ k
      have hν_sum : ∑ i, shiftIter n μ k i = 1 :=
        shiftIter_total n μ hμsum k
      have hstep : wasserstein1 (cycleMetricScaled n)
          (shiftIter n μ k) (shiftMeasure n (shiftIter n μ k)) ≤ 1 / n :=
        wasserstein1_shiftMeasure_le n hn (shiftIter n μ k) hν_nn hν_sum
      have htri := wasserstein1_triangle (cycleMetricScaled n)
        (cycleMetricScaled_nonneg n)
        (cycleMetricScaled_triangle n hn)
        μ (shiftIter n μ k) (shiftMeasure n (shiftIter n μ k))
        hμ hν_nn (fun j => shiftMeasure_nonneg n hν_nn j)
        hμsum hν_sum (by rw [shiftMeasure_total]; exact hν_sum)
      have hsum_cast : ((k : ℝ) + 1) / n = (k : ℝ) / n + 1 / n := by
        ring
      calc wasserstein1 (cycleMetricScaled n) μ
            (shiftMeasure n (shiftIter n μ k))
          ≤ wasserstein1 (cycleMetricScaled n) μ (shiftIter n μ k)
            + wasserstein1 (cycleMetricScaled n) (shiftIter n μ k)
              (shiftMeasure n (shiftIter n μ k)) := htri
        _ ≤ (k : ℝ) / n + 1 / n := by linarith
        _ = ((k : ℝ) + 1) / n := by rw [hsum_cast]
        _ = ((k + 1 : ℕ) : ℝ) / n := by push_cast; ring

/-- **Physical-observable shift-rate corollary**: for any probability
measure `μ` on the cycle and any `L`-Lipschitz observable `f` (against
the scaled cycle metric), the change in expectation under `k` forward
shifts is bounded by `L · k / n`. Combines `wasserstein1_lipschitz_bound`
(KR one-direction) with `wasserstein1_shiftIter_le` (k-step shift rate).
Every Lipschitz observable has expectation variation O(k/n) under k-step
cyclic shifts — the sharpest expectation-level A7 statement currently
in the library. -/
theorem expectationDiff_shiftIter_le
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1)
    (k : ℕ) (f : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hfLip : ∀ i j, |f i - f j| ≤ L * cycleMetricScaled n i j) :
    |(∑ i, μ i * f i) - (∑ i, shiftIter n μ k i * f i)|
      ≤ L * (k : ℝ) / n := by
  have hshift_nn : ∀ i, 0 ≤ shiftIter n μ k i := shiftIter_nonneg n μ hμ k
  have hshift_sum : ∑ i, shiftIter n μ k i = 1 :=
    shiftIter_total n μ hμsum k
  have hkr := wasserstein1_lipschitz_bound (cycleMetricScaled n)
    (cycleMetricScaled_nonneg n)
    μ (shiftIter n μ k)
    hμ hshift_nn hμsum hshift_sum
    f L hL hfLip
  have hshift_rate :
      wasserstein1 (cycleMetricScaled n) μ (shiftIter n μ k)
        ≤ (k : ℝ) / n :=
    wasserstein1_shiftIter_le n hn k μ hμ hμsum
  calc |(∑ i, μ i * f i) - (∑ i, shiftIter n μ k i * f i)|
      ≤ L * wasserstein1 (cycleMetricScaled n) μ (shiftIter n μ k) := hkr
    _ ≤ L * ((k : ℝ) / n) := by
        exact mul_le_mul_of_nonneg_left hshift_rate hL
    _ = L * (k : ℝ) / n := by ring

end InfraFormalization
