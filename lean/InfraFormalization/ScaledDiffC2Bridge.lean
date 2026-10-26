/-
Scaled second differences of C² functions along h = 1/n.

`CTwoTaylor.lean` proves that for a C² function `f`,
`(f(x+h) + f(x-h) − 2 f(x)) / h² → f''(x)` as `h → 0`. This module
specialises the limit to `h = 1/n`, proving
`scaledSecondDiff f n x → f''(x)` as `n → ∞` for fixed `x`. It also proves
that `n²` times the hypergraph Laplacian of `cycleHypergraph n`, applied to
the samples `f(j/n)`, equals `scaledSecondDiff f n (i/n)` at an interior
index `i`.
-/

import InfraFormalization.CTwoTaylor
import InfraFormalization.LaplacianBridge
import InfraFormalization.HypergraphCycleBridge

namespace InfraFormalization

open Filter Topology

/-- For `n ≥ 1`, `scaledSecondDiff f n x` equals
`secondDifference f x (1/n) / (1/n)²`. -/
lemma scaledSecondDiff_eq_ratio (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    scaledSecondDiff f n x
      = secondDifference f x (1 / (n : ℝ)) / (1 / (n : ℝ))^2 := by
  unfold scaledSecondDiff
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp

/-- For a C² function `f` and fixed `x`, the sequence
`n ↦ scaledSecondDiff f n x` tends to `iteratedDeriv 2 f x`. -/
theorem scaledSecondDiff_tendsto_iteratedDeriv_C2
    (f : ℝ → ℝ) (x : ℝ) (hf : ContDiff ℝ 2 f) :
    Tendsto (fun n : ℕ => scaledSecondDiff f n x) atTop
      (𝓝 (iteratedDeriv 2 f x)) := by
  -- The limit in `h` along `𝓝[≠] 0`, composed with `n ↦ 1/n`.
  have hbase := scaledSecondDiff_tendsto_iteratedDeriv f x hf
  -- `n ↦ 1/n` tends to 0 through nonzero values.
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h1 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_natCast_atTop_atTop.inv_tendsto_atTop
      exact h1.congr (fun n => by simp [one_div])
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      show (1 : ℝ) / n ∈ {x : ℝ | x ≠ 0}
      simp [hn_ne]
  have hcomp :
      Tendsto (fun n : ℕ =>
          secondDifference f x (1 / (n : ℝ)) / (1 / (n : ℝ))^2) atTop
        (𝓝 (iteratedDeriv 2 f x)) := hbase.comp hseq
  -- For n ≥ 1 the body equals `scaledSecondDiff f n x`.
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (scaledSecondDiff_eq_ratio f n hn x).symm

/-- For `n ≥ 2`, an index `i : Fin n` with `1 ≤ i` and `i + 1 < n`, and any
`f : ℝ → ℝ`, `n²` times the hypergraph Laplacian of `cycleHypergraph n` at
`i`, applied to `j ↦ f(j/n)`, equals `scaledSecondDiff f n (i/n)`. The
statement is an equation for each fixed `n` and makes no assumption on
`f`. -/
theorem hypergraph_scaled_laplacian_eq_scaledSecondDiff
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : ℝ → ℝ) (i : Fin n) (hlo : 1 ≤ i.val) (hhi : i.val + 1 < n) :
    (n : ℝ)^2 * Hypergraph.laplacianHyper (cycleHypergraph n)
        (fun j : Fin n => f ((j.val : ℝ) / n)) i
    = scaledSecondDiff f n ((i.val : ℝ) / n) := by
  rw [laplacianHyper_cycleHypergraph hn]
  rw [cycleLaplacian_in_terms_of_secondDifference n f i hlo hhi]
  unfold scaledSecondDiff
  ring

end InfraFormalization
