/-
**C² Taylor convergence for the scaled central second difference** (task R1).

For `f : ℝ → ℝ` that is `C²` on all of `ℝ`, the scaled central
second difference converges to the second derivative:

  `lim_{h → 0} (f(x+h) + f(x-h) − 2 f(x)) / h² = f''(x)`

This is the Rung-2 bridge in full generality (beyond polynomials).
Proof is via Taylor's theorem with Peano remainder (Mathlib's
`Real.taylor_tendsto`), applied at `y = x+h` and `y = x-h`, noting
that the first-order terms cancel on addition.

**Connection to hypergraphs.** Combined with
`hypergraph_scaled_laplacian_eq_second_deriv` (exact for polynomials)
and `cycleLaplacian_is_secondDifference`, this extends the discrete
→ continuum Laplacian bridge from polynomials to all C² functions.
-/

import InfraFormalization.SecondDifference
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace InfraFormalization

open Filter Topology Set

/-- Explicit form of the degree-2 Taylor polynomial on `univ`:
`P(y) = f(x) + (y − x) · f'(x) + (y − x)²/2 · f''(x)`. -/
lemma taylorWithinEval_two_univ (f : ℝ → ℝ) (x y : ℝ) :
    taylorWithinEval f 2 univ x y
      = f x + (y - x) * deriv f x + (y - x)^2 / 2 * iteratedDeriv 2 f x := by
  have h2 : taylorWithinEval f 2 univ x y
      = taylorWithinEval f 1 univ x y
        + (((1 + 1 : ℝ) * Nat.factorial 1)⁻¹ * (y - x) ^ (1 + 1))
          • iteratedDerivWithin (1 + 1) f univ x := by
    simpa using taylorWithinEval_succ f 1 univ x y
  have h1 : taylorWithinEval f 1 univ x y
      = taylorWithinEval f 0 univ x y
        + (((0 + 1 : ℝ) * Nat.factorial 0)⁻¹ * (y - x) ^ (0 + 1))
          • iteratedDerivWithin (0 + 1) f univ x := by
    simpa using taylorWithinEval_succ f 0 univ x y
  have h0 : taylorWithinEval f 0 univ x y = f x :=
    taylor_within_zero_eval f univ x y
  rw [h2, h1, h0]
  simp only [iteratedDerivWithin_univ, Nat.factorial_zero, Nat.factorial_one,
             Nat.cast_one, smul_eq_mul]
  have hd1 : iteratedDeriv 1 f x = deriv f x := by
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hd1]
  ring

/-- **Peano remainder form of Taylor at order 2**: for a `ContDiff ℝ 2` function,
the remainder after the degree-2 Taylor polynomial, divided by `h²`, tends to 0. -/
lemma taylor_remainder_pos_tendsto (f : ℝ → ℝ) (x : ℝ) (hf : ContDiff ℝ 2 f) :
    Tendsto
      (fun h : ℝ =>
        (f (x + h)
          - (f x + h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2)
      (𝓝 0) (𝓝 0) := by
  have hTaylor :
      Tendsto (fun y => (f y - taylorWithinEval f 2 univ x y) / (y - x)^2)
        (𝓝 x) (𝓝 0) := by
    have := Real.taylor_tendsto (s := univ) convex_univ (mem_univ x) hf.contDiffOn
    simpa using this
  have hsubst : Tendsto (fun h : ℝ => x + h) (𝓝 0) (𝓝 x) := by
    have h1 : Tendsto (fun _ : ℝ => x) (𝓝 0) (𝓝 x) := tendsto_const_nhds
    simpa using h1.add tendsto_id
  have hcomp := hTaylor.comp hsubst
  -- Rewrite the body.
  apply hcomp.congr'
  filter_upwards [] with h
  simp only [Function.comp_apply]
  rw [taylorWithinEval_two_univ]
  have hsq : (x + h - x)^2 = h^2 := by ring
  rw [hsq]
  congr 1
  ring

/-- **Peano remainder form at `x − h`**: symmetric version. -/
lemma taylor_remainder_neg_tendsto (f : ℝ → ℝ) (x : ℝ) (hf : ContDiff ℝ 2 f) :
    Tendsto
      (fun h : ℝ =>
        (f (x - h)
          - (f x - h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2)
      (𝓝 0) (𝓝 0) := by
  have hTaylor :
      Tendsto (fun y => (f y - taylorWithinEval f 2 univ x y) / (y - x)^2)
        (𝓝 x) (𝓝 0) := by
    have := Real.taylor_tendsto (s := univ) convex_univ (mem_univ x) hf.contDiffOn
    simpa using this
  have hsubst : Tendsto (fun h : ℝ => x - h) (𝓝 0) (𝓝 x) := by
    have h1 : Tendsto (fun _ : ℝ => x) (𝓝 0) (𝓝 x) := tendsto_const_nhds
    simpa using h1.sub tendsto_id
  have hcomp := hTaylor.comp hsubst
  apply hcomp.congr'
  filter_upwards [] with h
  simp only [Function.comp_apply]
  rw [taylorWithinEval_two_univ]
  have hsq : (x - h - x)^2 = h^2 := by ring
  rw [hsq]
  congr 1
  ring

/-- **R1 — Scaled central second difference converges to `f''`.**

For a `C²` function `f : ℝ → ℝ` and any `x ∈ ℝ`,
`(f(x+h) + f(x−h) − 2 f(x)) / h² → f''(x)` as `h → 0`. -/
theorem scaledSecondDiff_tendsto_iteratedDeriv
    (f : ℝ → ℝ) (x : ℝ) (hf : ContDiff ℝ 2 f) :
    Tendsto (fun h : ℝ => secondDifference f x h / h^2) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv 2 f x)) := by
  have hpos := taylor_remainder_pos_tendsto f x hf
  have hneg := taylor_remainder_neg_tendsto f x hf
  have hsum :
      Tendsto
        (fun h : ℝ =>
          ((f (x + h) - (f x + h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2)
          + ((f (x - h) - (f x - h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2))
        (𝓝 0) (𝓝 (0 + 0)) := hpos.add hneg
  simp only [add_zero] at hsum
  have hsum_ne :
      Tendsto
        (fun h : ℝ =>
          ((f (x + h) - (f x + h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2)
          + ((f (x - h) - (f x - h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2))
        (𝓝[≠] 0) (𝓝 0) :=
    hsum.mono_left nhdsWithin_le_nhds
  have hbody : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      ((f (x + h) - (f x + h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2)
        + ((f (x - h) - (f x - h * deriv f x + h^2 / 2 * iteratedDeriv 2 f x)) / h^2)
      = secondDifference f x h / h^2 - iteratedDeriv 2 f x := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh_ne : h ≠ 0 := hh
    have hh2 : h^2 ≠ 0 := pow_ne_zero 2 hh_ne
    unfold secondDifference
    field_simp
    ring
  have hdiff :
      Tendsto (fun h : ℝ => secondDifference f x h / h^2 - iteratedDeriv 2 f x)
        (𝓝[≠] 0) (𝓝 0) :=
    hsum_ne.congr' hbody
  have hc : Tendsto (fun _ : ℝ => iteratedDeriv 2 f x) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv 2 f x)) := tendsto_const_nhds
  have := hdiff.add hc
  simp only [zero_add, sub_add_cancel] at this
  exact this

end InfraFormalization
