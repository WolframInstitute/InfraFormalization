import InfraFormalization.HypergraphDistance
import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.WassersteinFinite

/-!
Wasserstein-1 distance on `Fin n` with the distance of `cycleHypergraph n`.

The module defines `cycleMetric n` (the hypergraph distance cast to ℝ), its scaled version
`cycleMetricScaled n = cycleMetric n / n`, the uniform measure, and the shifted measures
`μ (· + k)`. It proves the metric properties, `W_1(δ_i, δ_j) = d(i, j)`, the bounds
`W_1 ≤ n` and `W_1 ≤ 1` (scaled) for probability measures, `W_1(δ_v, δ_{v+1}) = 1/n`
(scaled), `W_1(μ, μ(· + k)) ≤ k/n` (scaled), and the resulting bound `L·k/n` on the change
of the expectation of an `L`-Lipschitz function under a shift by `k`.
-/

namespace InfraFormalization

open scoped BigOperators

/-- `Hypergraph.dist` of `cycleHypergraph n`, cast to ℝ. -/
noncomputable def cycleMetric (n : ℕ) [NeZero n] (i j : Fin n) : ℝ :=
  ((cycleHypergraph n).dist i j : ℝ)

/-- `cycleMetric` is non-negative. -/
theorem cycleMetric_nonneg (n : ℕ) [NeZero n] (i j : Fin n) :
    0 ≤ cycleMetric n i j := by
  unfold cycleMetric
  exact_mod_cast Nat.zero_le _

/-- `cycleMetric n i i = 0`. -/
theorem cycleMetric_self (n : ℕ) [NeZero n] (i : Fin n) :
    cycleMetric n i i = 0 := by
  unfold cycleMetric
  simp

/-- `cycleMetric` is symmetric. -/
theorem cycleMetric_symm (n : ℕ) [NeZero n] (i j : Fin n) :
    cycleMetric n i j = cycleMetric n j i := by
  unfold cycleMetric
  rw [Hypergraph.dist_comm]

/-- The uniform weight `1/n` on `Fin n`. -/
noncomputable def cycleUniform (n : ℕ) : Fin n → ℝ :=
  fun _ => (1 : ℝ) / n

/-- `cycleUniform n i ≥ 0`. -/
theorem cycleUniform_nonneg (n : ℕ) (i : Fin n) : 0 ≤ cycleUniform n i := by
  unfold cycleUniform
  exact div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le _)

/-- For `n ≥ 1`, the weights `cycleUniform n i` sum to 1. -/
theorem cycleUniform_total (n : ℕ) (hn : 1 ≤ n) :
    ∑ i : Fin n, cycleUniform n i = 1 := by
  unfold cycleUniform
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp

/-- `W_1(cycleUniform n, cycleUniform n) = 0` under `cycleMetric n`. -/
theorem wasserstein1_cycleUniform_self (n : ℕ) [NeZero n] :
    wasserstein1 (cycleMetric n) (cycleUniform n) (cycleUniform n) = 0 :=
  wasserstein1_self_eq_zero
    (cycleMetric n)
    (cycleMetric_nonneg n)
    (cycleMetric_self n)
    (cycleUniform n)
    (cycleUniform_nonneg n)

/-- `W_1(δ_i, δ_j) = (cycleHypergraph n).dist i j` under `cycleMetric n`. -/
theorem wasserstein1_cycleDelta_eq_hypergraphDist
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (cycleMetric n) (delta i) (delta j)
      = ((cycleHypergraph n).dist i j : ℝ) := by
  rw [wasserstein1_delta_eq_dist]
  rfl

/-- `cycleMetric n i j ≤ n`. -/
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
  · -- If `j` is unreachable from `i`, `SimpleGraph.dist` is 0.
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hreach]
    exact_mod_cast Nat.zero_le _

/-- For probability vectors `μ, ν` on `Fin n`, `W_1(μ, ν) ≤ n` under `cycleMetric n`. -/
theorem wasserstein1_cycleMetric_le_card
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (cycleMetric n) μ ν ≤ n := by
  refine wasserstein1_le_sup (cycleMetric n) n ?_
    (cycleMetric_le_card n) (cycleMetric_nonneg n) μ ν hμ hν hμsum hνsum
  exact_mod_cast Nat.zero_le _

/-- `cycleMetric n i j / n`. -/
noncomputable def cycleMetricScaled (n : ℕ) [NeZero n] (i j : Fin n) : ℝ :=
  cycleMetric n i j / n

theorem cycleMetricScaled_nonneg (n : ℕ) [NeZero n] (i j : Fin n) :
    0 ≤ cycleMetricScaled n i j := by
  unfold cycleMetricScaled
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le _
  exact div_nonneg (cycleMetric_nonneg n i j) hn

/-- `cycleMetricScaled n i j ≤ 1`. -/
theorem cycleMetricScaled_le_one (n : ℕ) [NeZero n] (i j : Fin n) :
    cycleMetricScaled n i j ≤ 1 := by
  unfold cycleMetricScaled
  have hn_pos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  rw [div_le_one hn_pos]
  exact cycleMetric_le_card n i j

/-- For probability vectors `μ, ν` on `Fin n`, `W_1(μ, ν) ≤ 1` under `cycleMetricScaled n`. -/
theorem wasserstein1_cycleMetricScaled_le_one
    (n : ℕ) [NeZero n]
    (μ ν : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1) :
    wasserstein1 (cycleMetricScaled n) μ ν ≤ 1 :=
  wasserstein1_le_sup (cycleMetricScaled n) 1 zero_le_one
    (cycleMetricScaled_le_one n) (cycleMetricScaled_nonneg n)
    μ ν hμ hν hμsum hνsum

/-- `W_1(δ_i, δ_j) = (cycleHypergraph n).dist i j / n` under `cycleMetricScaled n`. -/
theorem wasserstein1_cycleDelta_scaled_eq
    (n : ℕ) [NeZero n] (i j : Fin n) :
    wasserstein1 (cycleMetricScaled n) (delta i) (delta j)
      = ((cycleHypergraph n).dist i j : ℝ) / n := by
  rw [wasserstein1_delta_eq_dist]
  rfl

/-! ## Adjacent Dirac measures -/

/-- For `n ≥ 2`, `cycleMetric n v (v + 1) = 1`. -/
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

/-- For `n ≥ 2`, `cycleMetricScaled n v (v + 1) = 1/n`. -/
theorem cycleMetricScaled_succ_eq (n : ℕ) [NeZero n] (hn : 2 ≤ n) (v : Fin n) :
    cycleMetricScaled n v (v + 1) = 1 / n := by
  unfold cycleMetricScaled
  rw [cycleMetric_succ_eq_one n hn v]

/-- For `n ≥ 2`, `W_1(δ_v, δ_{v+1}) = 1/n` under `cycleMetricScaled n`. -/
theorem wasserstein1_cycleDelta_succ
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (v : Fin n) :
    wasserstein1 (cycleMetricScaled n) (delta v) (delta (v + 1))
      = 1 / n := by
  rw [wasserstein1_delta_eq_dist]
  exact cycleMetricScaled_succ_eq n hn v

/-! ## Shifted measures -/

/-- `shiftMeasure n μ j := μ (j + 1)`, with addition in `Fin n`. -/
noncomputable def shiftMeasure (n : ℕ) [NeZero n] (μ : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j => μ (j + 1)

theorem shiftMeasure_nonneg (n : ℕ) [NeZero n]
    {μ : Fin n → ℝ} (hμ : ∀ i, 0 ≤ μ i) (j : Fin n) :
    0 ≤ shiftMeasure n μ j := hμ _

/-- `∑ j, shiftMeasure n μ j = ∑ i, μ i`. -/
theorem shiftMeasure_total (n : ℕ) [NeZero n] (μ : Fin n → ℝ) :
    ∑ j : Fin n, shiftMeasure n μ j = ∑ i : Fin n, μ i := by
  unfold shiftMeasure
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n)) μ

/-- The transport plan from `μ` to `shiftMeasure n μ` with mass `μ i` at `(i, i - 1)` and
zero elsewhere. -/
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

/-- For `n ≥ 2`, the cost of `shiftPlan` under `cycleMetric n` equals `∑ i, μ i`. -/
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

/-- For `n ≥ 2` and a probability vector `μ`, the cost of `shiftPlan` under
`cycleMetric n` is 1. -/
theorem shiftPlan_cost_cycleMetric_one
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1) :
    (shiftPlan n μ hμ).cost (cycleMetric n) = 1 := by
  rw [shiftPlan_cost_cycleMetric n hn μ hμ]
  exact hμsum

/-- For `n ≥ 2` and a probability vector `μ`, `W_1(μ, shiftMeasure n μ) ≤ 1/n` under
`cycleMetricScaled n`. The proof bounds the infimum by the cost of `shiftPlan`. -/
theorem wasserstein1_shiftMeasure_le (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1) :
    wasserstein1 (cycleMetricScaled n) μ (shiftMeasure n μ) ≤ 1 / n := by
  unfold wasserstein1
  refine csInf_le ⟨0, ?_⟩ ?_
  · rintro c ⟨q, rfl⟩
    exact q.cost_nonneg (cycleMetricScaled n) (cycleMetricScaled_nonneg n)
  · refine ⟨shiftPlan n μ hμ, ?_⟩
    -- The scaled cost is the unscaled cost 1 divided by `n`.
    unfold TransportPlan.cost cycleMetricScaled
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

/-- For `n ≥ 2`, `cycleMetric` satisfies the triangle inequality. -/
theorem cycleMetric_triangle (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (i j k : Fin n) :
    cycleMetric n i k ≤ cycleMetric n i j + cycleMetric n j k := by
  unfold cycleMetric
  have := cycleHypergraph_dist_triangle hn i j k
  exact_mod_cast this

/-- For `n ≥ 2`, `cycleMetricScaled` satisfies the triangle inequality. -/
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

/-- `cycleMetricScaled n i i = 0`. -/
theorem cycleMetricScaled_self (n : ℕ) [NeZero n] (i : Fin n) :
    cycleMetricScaled n i i = 0 := by
  unfold cycleMetricScaled
  rw [cycleMetric_self]
  simp

/-- `shiftMeasure` applied `k` times, so `shiftIter n μ k j = μ (j + k)`. -/
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

/-- For `n ≥ 2` and a probability vector `μ`, `W_1(μ, shiftIter n μ k) ≤ k/n` under
`cycleMetricScaled n`. The proof is by induction on `k` with the triangle inequality for
`W_1`. -/
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

/-- For `n ≥ 2`, a probability vector `μ`, and `f` that is `L`-Lipschitz for
`cycleMetricScaled n`, `|∑ μ f − ∑ (shiftIter n μ k) f| ≤ L·k/n`. -/
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

