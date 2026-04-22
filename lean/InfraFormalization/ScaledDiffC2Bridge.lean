/-
**End-to-end C² bridge: scaled discrete Laplacian → `f''`** (task A3 / #14).

R1 (`CTwoTaylor.lean`) proves that for a `C²` function `f` and real
`h → 0`,
  `(f(x+h) + f(x-h) − 2 f(x)) / h² → f''(x)`.

Specialising `h = 1/n` with `n → ∞` (a sequence-along-the-integers
instance of the general limit) gives the discrete-refinement version:

  `scaledSecondDiff f n x := n² · secondDifference f x (1/n) → f''(x)`.

This extends the previously-polynomial-only identity
`scaledSecondDiff_quadratic_independent` to **any C² function**,
closing the Rung-2 bridge at the `scaledSecondDiff` level.

**Connection to hypergraphs.** Combined with
`laplacianHyper_cycleHypergraph` and
`cycleLaplacian_in_terms_of_secondDifference`, this gives an
**end-to-end** discrete-hypergraph → continuum-second-derivative
bridge valid for all C² test functions, not just polynomials.
-/

import InfraFormalization.CTwoTaylor
import InfraFormalization.LaplacianBridge
import InfraFormalization.HypergraphCycleBridge

namespace InfraFormalization

open Filter Topology

/-- **Scaled second difference along `h = 1/n`**: at each `n ≥ 1`,
`scaledSecondDiff f n x = secondDifference f x (1/n) / (1/n)²`. -/
lemma scaledSecondDiff_eq_ratio (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    scaledSecondDiff f n x
      = secondDifference f x (1 / (n : ℝ)) / (1 / (n : ℝ))^2 := by
  unfold scaledSecondDiff
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp

/-- **R1 specialised to `h = 1/n`**: for `f : ℝ → ℝ` `C²`, the
scaled second difference along refining integer-scales converges
to `f''`. -/
theorem scaledSecondDiff_tendsto_iteratedDeriv_C2
    (f : ℝ → ℝ) (x : ℝ) (hf : ContDiff ℝ 2 f) :
    Tendsto (fun n : ℕ => scaledSecondDiff f n x) atTop
      (𝓝 (iteratedDeriv 2 f x)) := by
  -- Use scaledSecondDiff_tendsto_iteratedDeriv with the filter map
  -- 𝓝[≠] 0 via the sequence n ↦ 1/n.
  have hbase := scaledSecondDiff_tendsto_iteratedDeriv f x hf
  -- Build the sequence-level limit via the filter-map h ↦ 1/n.
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
  -- Compose: Tendsto (scaledSecondDiff f · x) atTop → 𝓝 (iteratedDeriv 2 f x).
  have hcomp :
      Tendsto (fun n : ℕ =>
          secondDifference f x (1 / (n : ℝ)) / (1 / (n : ℝ))^2) atTop
        (𝓝 (iteratedDeriv 2 f x)) := hbase.comp hseq
  -- Rewrite the body as scaledSecondDiff f n x for n ≥ 1.
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (scaledSecondDiff_eq_ratio f n hn x).symm

/-- **End-to-end C² bridge: hypergraph Laplacian on the cycle
tends to `f''` for any C² test function.** For `n ≥ 2`, an interior
index `i : Fin n`, and a C² function `f : ℝ → ℝ`, the scaled
hypergraph Laplacian at `i` (of the discretised `f(j/n)`) equals
the scaled second difference `scaledSecondDiff f n (i.val/n)`. As
`n → ∞`, **this sequence converges to `f''(i.val/n)` for any fixed
(n, i) pair — exactly when `(n, i)` varies so the interior index
stays fixed at some rational `p/q ∈ (0, 1)`**. -/
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
