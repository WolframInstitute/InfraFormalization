import InfraFormalization.HypergraphMeasure
import InfraFormalization.Infra.GHBound
import Mathlib.Topology.Order.MonotoneConvergence

/-! Rate obligations for a discrepancy sequence `d : ℕ → ℝ`.

`WassersteinRateObligation d` states `d n ≤ C / n` for large `n`.
`ConvergenceRateObligation d r` states `d n ≤ C * r n`. Neither definition
computes a Wasserstein distance; `d` is supplied by the caller, and the zero
function satisfies both (`wassersteinRateObligation_zero`). -/

namespace InfraFormalization

open scoped BigOperators

/-- **Discrepancy functional** on scaled cycle hypergraphs: a
sequence of non-negative reals indexed by `n : ℕ`. -/
def ScaledDiscrepancy : Type := ℕ → ℝ

/-- **A7 obligation**: the discrepancy admits an `O(1/n)` bound:
there exists `C > 0` and `N : ℕ` with `d(n) ≤ C/n` for every
`n ≥ max N 1`. -/
def WassersteinRateObligation (d : ScaledDiscrepancy) : Prop :=
  ∃ (C : ℝ) (_ : 0 < C) (N : ℕ), ∀ n, N ≤ n → 1 ≤ n → d n ≤ C / n

/-- **Trivial witness**: the zero discrepancy satisfies the `O(1/n)`
bound with `C = 1`, `N = 1`. -/
theorem wassersteinRateObligation_zero :
    WassersteinRateObligation (fun _ => 0) := by
  refine ⟨1, one_pos, 1, ?_⟩
  intros n _ hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_nonneg one_pos.le hn_pos.le

/-- **Tendsto variant**: the discrepancy tending to `0` as `n → ∞`. -/
def WassersteinRateTendsto (d : ScaledDiscrepancy) : Prop :=
  Filter.Tendsto d Filter.atTop (nhds 0)

/-- **Tendsto-to-zero for the zero discrepancy**. -/
theorem wassersteinRateTendsto_zero :
    WassersteinRateTendsto (fun _ => 0) :=
  tendsto_const_nhds

/-- **Bundled A7 witness**: the zero-discrepancy sequence satisfies
both the `O(1/n)` obligation and the (weaker) `tendsto 0` variant. -/
theorem wassersteinRateBundle_zero :
    WassersteinRateObligation (fun _ => 0)
    ∧ WassersteinRateTendsto (fun _ => 0) :=
  ⟨wassersteinRateObligation_zero, wassersteinRateTendsto_zero⟩

/-- The sequence `n ↦ 1/2^n`. It equals the length of one edge of the
subdivided unit path after `n` steps; it is defined directly and is not
computed from a measure.
-/
noncomputable def subdivisionDiscrepancy : ScaledDiscrepancy :=
  fun n => 1 / (2 : ℝ)^n

/-- `1/2^n ≤ 1/n` for `n ≥ 1`, so `subdivisionDiscrepancy` satisfies
`WassersteinRateObligation`.
-/
theorem subdivisionDiscrepancy_satisfies_obligation :
    WassersteinRateObligation subdivisionDiscrepancy := by
  refine ⟨1, one_pos, 1, ?_⟩
  intros n _ hn_one
  unfold subdivisionDiscrepancy
  have h_n_lt : n < 2^n := Nat.lt_two_pow_self
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn_one
  have h_2n_pos : (0 : ℝ) < (2 : ℝ)^n := by positivity
  rw [div_le_div_iff₀ h_2n_pos h_n_pos, one_mul, one_mul]
  exact_mod_cast h_n_lt.le

/-- **Tendsto variant for the subdivision discrepancy**: `1/2^n → 0`
as `n → ∞`. Direct from `tendsto_one_div_pow_atTop_nhds_zero` style
arguments — `2^n → ∞` so `1/2^n → 0`. -/
theorem subdivisionDiscrepancy_tendsto :
    WassersteinRateTendsto subdivisionDiscrepancy := by
  unfold WassersteinRateTendsto subdivisionDiscrepancy
  -- 1 / 2^n = (1/2)^n with |1/2| < 1, so → 0 by tendsto_pow_atTop_nhds_zero_iff.
  have h_eq : (fun n : ℕ => 1 / (2 : ℝ)^n) = (fun n : ℕ => (1/2 : ℝ)^n) := by
    funext n
    rw [div_pow, one_pow]
  rw [h_eq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- `subdivisionDiscrepancy` satisfies `WassersteinRateObligation` and tends to 0. -/
theorem subdivisionDiscrepancyBundle :
    WassersteinRateObligation subdivisionDiscrepancy
    ∧ WassersteinRateTendsto subdivisionDiscrepancy :=
  ⟨subdivisionDiscrepancy_satisfies_obligation, subdivisionDiscrepancy_tendsto⟩

/-! ## Generic convergence-rate obligation (#233 Phase A follow-up)

The `WassersteinRateObligation` form above hard-codes the `1/n` rate.
For a general framework, we admit any non-negative rate function
`r : ℕ → ℝ` (e.g. `1/n`, `1/n²`, geometric `c^n`, exponential decay).
This generalizes the obligation system to discrepancies measured by
metrics other than W_1 — e.g. Forman-Ricci curvature deviation,
Gromov-Hausdorff distance, spectral gap, etc.

Concrete rate functions provided: `rateOneOverN`, `rateOneOverNSquared`,
`rateGeometric c` (for `0 < c < 1`). -/

/-- **Generic convergence-rate obligation**: discrepancy `d` satisfies
`d n ≤ C * r n` for some `C > 0` and all `n ≥ N`. The rate function
`r` controls the asymptotic decay shape. -/
def ConvergenceRateObligation (d : ScaledDiscrepancy) (r : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (_ : 0 < C) (N : ℕ), ∀ n, N ≤ n → d n ≤ C * r n

/-- **Standard `O(1/n)` rate function**: `r n = 1/n`. -/
noncomputable def rateOneOverN : ℕ → ℝ := fun n => 1 / (n : ℝ)

/-- **Standard `O(1/n²)` rate function**: `r n = 1/n²`. -/
noncomputable def rateOneOverNSquared : ℕ → ℝ := fun n => 1 / ((n : ℝ)^2)

/-- **Geometric `O(c^n)` rate function** for `0 < c < 1`. -/
noncomputable def rateGeometric (c : ℝ) : ℕ → ℝ := fun n => c^n

/-- **`WassersteinRateObligation` is the special case `r = 1/n`** (with
the `n ≥ 1` constraint encoded by the implicit nonzero-N requirement).
Forward direction: a `WassersteinRateObligation` witness gives a
`ConvergenceRateObligation _ rateOneOverN` witness with N := max N 1. -/
theorem convergenceRateObligation_oneOverN_of_wasserstein
    (d : ScaledDiscrepancy) (h : WassersteinRateObligation d) :
    ConvergenceRateObligation d rateOneOverN := by
  obtain ⟨C, hC_pos, N, hN⟩ := h
  refine ⟨C, hC_pos, max N 1, ?_⟩
  intros n hn
  have h_N_le : N ≤ n := le_of_max_le_left hn
  have h_one_le : 1 ≤ n := le_of_max_le_right hn
  have := hN n h_N_le h_one_le
  unfold rateOneOverN
  rw [mul_one_div]
  exact this

/-- **Reverse direction**: a `ConvergenceRateObligation _ rateOneOverN`
witness gives a `WassersteinRateObligation` witness with the same
`C, N`. The `1 ≤ n` constraint is folded into the rate-function
denominator (vanishing safely when `n = 0` because `1/0 = 0` in `ℝ`). -/
theorem wassersteinRateObligation_of_convergenceRate_oneOverN
    (d : ScaledDiscrepancy)
    (h : ConvergenceRateObligation d rateOneOverN) :
    WassersteinRateObligation d := by
  obtain ⟨C, hC_pos, N, hN⟩ := h
  refine ⟨C, hC_pos, N, ?_⟩
  intros n h_N_le _h_one_le
  have := hN n h_N_le
  unfold rateOneOverN at this
  rw [mul_one_div] at this
  exact this

/-- **Subdivision-discrepancy as a generic geometric rate**: `1/2^n`
satisfies the `rateGeometric (1/2)` obligation with `C = 1, N = 0`.
Geometric decay is strictly faster than any polynomial `O(1/n^k)`,
so this is the strongest natural rate-statement for the subdivision
trajectory. -/
theorem subdivisionDiscrepancy_satisfies_geometric :
    ConvergenceRateObligation subdivisionDiscrepancy (rateGeometric (1/2)) := by
  refine ⟨1, one_pos, 0, ?_⟩
  intros n _
  unfold subdivisionDiscrepancy rateGeometric
  rw [one_mul, div_pow, one_pow]

/-- **Subdivision discrepancy via the generic O(1/n) form**: shows the
existing `subdivisionDiscrepancy_satisfies_obligation` lifts to the
generic `ConvergenceRateObligation _ rateOneOverN` framework. -/
theorem subdivisionDiscrepancy_satisfies_oneOverN :
    ConvergenceRateObligation subdivisionDiscrepancy rateOneOverN :=
  convergenceRateObligation_oneOverN_of_wasserstein _
    subdivisionDiscrepancy_satisfies_obligation

/-- **Trivial witness**: the zero discrepancy satisfies any
`ConvergenceRateObligation _ r` with `C = 1, N = 0`, provided `r n ≥ 0`. -/
theorem convergenceRateObligation_zero (r : ℕ → ℝ)
    (hr_nonneg : ∀ n, 0 ≤ r n) :
    ConvergenceRateObligation (fun _ => 0) r := by
  refine ⟨1, one_pos, 0, ?_⟩
  intros n _
  rw [one_mul]
  exact hr_nonneg n

end InfraFormalization
