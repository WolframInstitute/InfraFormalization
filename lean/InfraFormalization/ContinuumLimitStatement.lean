/-
Limit statements for scaled discrete operators on the cycle and for Riemann sums.

The module states pointwise convergence of the scaled second difference for twice
differentiable functions (not proved) and proves it for quadratics. It proves the scalar
limits `exp(t n² λ_k) → exp(−(2πk)² t)`, `2n sin(πk/n) → 2πk` and
`4n² sin²(πk/n) (+ m²) → (2πk)² (+ m²)`, where `λ_k` is the cycle Laplacian eigenvalue. It
proves that the Riemann sums `(1/n) Σ_{k<n} f(k/n)` tend to `∫_0^1 f` for every polynomial of
degree at most 3.
-/

import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.Infra.ScaledCycle
import InfraFormalization.Infra.ScaledLorentz
import InfraFormalization.Schwarzschild
import InfraFormalization.CycleEigenLimit
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace InfraFormalization

/-! ## A. Scaled second differences

The quadratic case is proved below as `cycle_laplacian_conv_polynomial`. -/

/-- For every `f : ℝ → ℝ` and `x` such that `deriv f` has derivative `deriv (deriv f) x` at
`x`, `scaledSecondDiff f n x = n² (f(x + 1/n) − 2f(x) + f(x − 1/n))` tends to
`deriv (deriv f) x`. This proposition is not proved in this module. -/
def CycleLaplacianConvergenceC2 : Prop :=
  ∀ (f : ℝ → ℝ) (x : ℝ),
    HasDerivAt (deriv f) (deriv (deriv f) x) x →
    Filter.Tendsto (fun n : Nat => scaledSecondDiff f n x)
      Filter.atTop
      (nhds (deriv (deriv f) x))

/-! ## B. Scaled cycle eigenvalue limits and Riemann sums -/

/-- For every `k` and `t`, `exp(t · n² · cycleEigenvalue n k) → exp(−(2πk)² t)` as
`n → ∞`. This is a limit of real numbers for each fixed mode `k`. -/
def DiscreteHeatToContinuumHeat : Prop :=
  ∀ (k : ℕ) (t : ℝ),
    Filter.Tendsto
      (fun n : ℕ =>
        Real.exp (t * ((n : ℝ)^2 * cycleEigenvalue n k)))
      Filter.atTop
      (nhds (Real.exp (-(2 * Real.pi * k) ^ 2 * t)))

/-- `DiscreteHeatToContinuumHeat` holds, from `cycleEigenvalue_scaled_tendsto` and continuity
of `Real.exp`. -/
theorem discreteHeatToContinuumHeat :
    DiscreteHeatToContinuumHeat := by
  intro k t
  -- Step 1: `n² · λ_k → -(2πk)²` (`cycleEigenvalue_scaled_tendsto`).
  have hA4 := cycleEigenvalue_scaled_tendsto k
  -- Step 2: multiplying by constant t preserves the limit.
  have h_mul : Filter.Tendsto
      (fun n : ℕ => t * ((n : ℝ)^2 * cycleEigenvalue n k))
      Filter.atTop (nhds (t * (-(2 * Real.pi * k) ^ 2))) :=
    hA4.const_mul t
  -- Step 3: Real.exp is continuous, compose.
  have h_exp : Filter.Tendsto
      (fun n : ℕ => Real.exp (t * ((n : ℝ)^2 * cycleEigenvalue n k)))
      Filter.atTop (nhds (Real.exp (t * (-(2 * Real.pi * k) ^ 2)))) :=
    Real.continuous_exp.tendsto _ |>.comp h_mul
  -- Step 4: rewrite target `t * (-(2πk)²) = -(2πk)² * t`.
  have h_rewrite : Real.exp (t * (-(2 * Real.pi * k) ^ 2))
      = Real.exp (-(2 * Real.pi * k) ^ 2 * t) := by ring_nf
  rw [← h_rewrite]
  exact h_exp

/-- For every continuous `f : ℝ → ℝ`, `(1/n) · Σ_{k=0}^{n-1} f(k/n) → ∫_0^1 f dx`. This
proposition is not proved in this module. -/
def A6LatticeRiemannObligation : Prop :=
  ∀ (f : ℝ → ℝ) (_hcont : Continuous f),
    Filter.Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) * ∑ k : Fin n, f ((k : ℝ) / (n : ℝ)))
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1, f x))

/-- For a constant `c`, `(1/n) · Σ_{k : Fin n} c → ∫_0^1 c dx = c`. -/
theorem A6_for_constants (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ _k : Fin n, c)
      Filter.atTop
      (nhds (∫ _x in (0 : ℝ)..1, c)) := by
  have h_integral : (∫ _x in (0 : ℝ)..1, c) = c := by
    rw [intervalIntegral.integral_const]
    simp
  rw [h_integral]
  have h_sum : ∀ n : ℕ, 0 < n →
      (1 / (n : ℝ)) * ∑ _k : Fin n, c = c := by
    intro n hn
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  exact (h_sum n (by omega)).symm

/-- `∑_{k : Fin n} k = n(n-1)/2` in `ℝ`. -/
theorem sum_fin_val_eq_triangular (n : ℕ) :
    (∑ k : Fin n, (k.val : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- For `n > 0`, `(1/n) · Σ_{k : Fin n} (k/n) = (n - 1) / (2n)`. -/
theorem A6_identity_sum_closed_form (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ k : Fin n, ((k : ℝ) / (n : ℝ)))
      = ((n : ℝ) - 1) / (2 * n) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  rw [← Finset.sum_div, sum_fin_val_eq_triangular]
  field_simp

/-- `(n-1)/(2n) → 1/2`. -/
theorem tendsto_nMinusOne_div_twoN :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 1) / (2 * n))
      Filter.atTop (nhds (1 / 2)) := by
  have h_eqv : ∀ n : ℕ, 0 < n →
      ((n : ℝ) - 1) / (2 * n) = 1 / 2 - 1 / (2 * n) := by
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h_2n : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h_nat
  have h_inv : Filter.Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ)))
      Filter.atTop (nhds 0) := by
    have := h_2n.inv_tendsto_atTop
    refine this.congr ?_
    intro n
    rw [one_div]; rfl
  have h_target : Filter.Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) - 1 / (2 * n)) Filter.atTop
      (nhds ((1 / 2 : ℝ) - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds h_inv
  rw [sub_zero] at h_target
  refine h_target.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (h_eqv n (by omega)).symm

/-- `(1/n) · Σ_{k : Fin n} (k/n) → ∫_0^1 x dx = 1/2`. -/
theorem A6_for_identity :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ k : Fin n, ((k : ℝ) / (n : ℝ)))
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1, x)) := by
  have h_integral : (∫ x in (0 : ℝ)..1, x) = 1 / 2 := by
    rw [integral_id]; norm_num
  rw [h_integral]
  refine tendsto_nMinusOne_div_twoN.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (A6_identity_sum_closed_form n (by omega)).symm

/-- `∑_{k : Fin n} k² = n(n-1)(2n-1)/6` in `ℝ`. -/
theorem sum_fin_val_sq_eq (n : ℕ) :
    (∑ k : Fin n, ((k.val : ℝ))^2)
      = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- For `n > 0`, `(1/n) · Σ_{k : Fin n} (k/n)² = (n-1)(2n-1)/(6n²)`. -/
theorem A6_sq_sum_closed_form (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ k : Fin n, ((k : ℝ) / (n : ℝ))^2)
      = ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (6 * n^2) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_rewrite : ∀ k : Fin n,
      ((k : ℝ) / (n : ℝ))^2 = ((k.val : ℝ)^2) / (n^2) := by
    intro k; field_simp
  simp_rw [h_rewrite]
  rw [← Finset.sum_div, sum_fin_val_sq_eq]
  field_simp

/-- `(n-1)(2n-1)/(6n²) → 1/3`. -/
theorem tendsto_sqRiemann_to_third :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 1) * (2 * n - 1) / (6 * n^2))
      Filter.atTop (nhds (1 / 3)) := by
  have h_eqv : ∀ n : ℕ, 0 < n →
      ((n : ℝ) - 1) * (2 * n - 1) / (6 * n^2)
        = 1 / 3 - 1 / (2 * n) + 1 / (6 * n^2) := by
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h_2n : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h_nat
  have h_inv_2n : Filter.Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ)))
      Filter.atTop (nhds 0) := by
    refine (h_2n.inv_tendsto_atTop).congr ?_
    intro n; rw [one_div]; rfl
  have h_inv_6n2 : Filter.Tendsto (fun n : ℕ => 1 / (6 * (n : ℝ)^2))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) h_inv_2n
    · positivity
    · rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz; simp
      · have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hpos
        have hn_pos : (0 : ℝ) < n := by linarith
        have h2n_pos : (0 : ℝ) < 2 * n := by positivity
        have h_le : 2 * (n : ℝ) ≤ 6 * n^2 := by nlinarith
        exact one_div_le_one_div_of_le h2n_pos h_le
  have h_target : Filter.Tendsto
      (fun n : ℕ => (1 / 3 : ℝ) - 1 / (2 * n) + 1 / (6 * n^2)) Filter.atTop
      (nhds ((1 / 3 : ℝ) - 0 + 0)) := by
    exact (Filter.Tendsto.sub tendsto_const_nhds h_inv_2n).add h_inv_6n2
  simp only [sub_zero, add_zero] at h_target
  refine h_target.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (h_eqv n (by omega)).symm

/-- `(1/n) · Σ_{k : Fin n} (k/n)² → ∫_0^1 x² dx = 1/3`. -/
theorem A6_for_sq :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ k : Fin n, ((k : ℝ) / (n : ℝ))^2)
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1, x^2)) := by
  have h_integral : (∫ x in (0 : ℝ)..1, x^2) = 1 / 3 := by
    rw [integral_pow]; norm_num
  rw [h_integral]
  refine tendsto_sqRiemann_to_third.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (A6_sq_sum_closed_form n (by omega)).symm

/-- `∑_{k : Fin n} k³ = n²(n-1)²/4` in `ℝ`. -/
theorem sum_fin_val_cube_eq (n : ℕ) :
    (∑ k : Fin n, ((k.val : ℝ))^3)
      = (n : ℝ)^2 * ((n : ℝ) - 1)^2 / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- For `n > 0`, `(1/n) · Σ_{k : Fin n} (k/n)³ = (n-1)²/(4n²)`. -/
theorem A6_cube_sum_closed_form (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ k : Fin n, ((k : ℝ) / (n : ℝ))^3)
      = ((n : ℝ) - 1)^2 / (4 * n^2) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_rewrite : ∀ k : Fin n,
      ((k : ℝ) / (n : ℝ))^3 = ((k.val : ℝ)^3) / (n^3) := by
    intro k; field_simp
  simp_rw [h_rewrite]
  rw [← Finset.sum_div, sum_fin_val_cube_eq]
  field_simp

/-- `(n-1)²/(4n²) → 1/4`. -/
theorem tendsto_cubeRiemann_to_quarter :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 1)^2 / (4 * n^2))
      Filter.atTop (nhds (1 / 4)) := by
  have h_eqv : ∀ n : ℕ, 0 < n →
      ((n : ℝ) - 1)^2 / (4 * n^2)
        = 1 / 4 - 1 / (2 * n) + 1 / (4 * n^2) := by
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h_2n : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h_nat
  have h_inv_2n : Filter.Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ)))
      Filter.atTop (nhds 0) := by
    refine (h_2n.inv_tendsto_atTop).congr ?_
    intro n; rw [one_div]; rfl
  have h_inv_4n2 : Filter.Tendsto (fun n : ℕ => 1 / (4 * (n : ℝ)^2))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) h_inv_2n
    · positivity
    · rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz; simp
      · have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hpos
        have hn_pos : (0 : ℝ) < n := by linarith
        have h2n_pos : (0 : ℝ) < 2 * n := by positivity
        have h_le : 2 * (n : ℝ) ≤ 4 * n^2 := by nlinarith
        exact one_div_le_one_div_of_le h2n_pos h_le
  have h_target : Filter.Tendsto
      (fun n : ℕ => (1 / 4 : ℝ) - 1 / (2 * n) + 1 / (4 * n^2)) Filter.atTop
      (nhds ((1 / 4 : ℝ) - 0 + 0)) :=
    (Filter.Tendsto.sub tendsto_const_nhds h_inv_2n).add h_inv_4n2
  simp only [sub_zero, add_zero] at h_target
  refine h_target.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (h_eqv n (by omega)).symm

/-- `(1/n) · Σ_{k : Fin n} (k/n)³ → ∫_0^1 x³ dx = 1/4`. -/
theorem A6_for_cube :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ k : Fin n, ((k : ℝ) / (n : ℝ))^3)
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1, x^3)) := by
  have h_integral : (∫ x in (0 : ℝ)..1, x^3) = 1 / 4 := by
    rw [integral_pow]; norm_num
  rw [h_integral]
  refine tendsto_cubeRiemann_to_quarter.congr'
    (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (A6_cube_sum_closed_form n (by omega)).symm

/-! ## Riemann-sum convergence as a predicate -/

/-- `(1/n) · Σ_{k : Fin n} f(k/n) → ∫_0^1 f dx`. -/
def A6Holds (f : ℝ → ℝ) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => (1 / (n : ℝ)) * ∑ k : Fin n, f ((k : ℝ) / (n : ℝ)))
    Filter.atTop
    (nhds (∫ x in (0 : ℝ)..1, f x))

/-- `A6Holds f` implies `A6Holds (c · f)`. -/
theorem A6Holds.const_mul (c : ℝ) {f : ℝ → ℝ} (hf : A6Holds f) :
    A6Holds (fun x => c * f x) := by
  unfold A6Holds at *
  have h_integral : (∫ x in (0 : ℝ)..1, (c * f x))
      = c * (∫ x in (0 : ℝ)..1, f x) :=
    intervalIntegral.integral_const_mul c f
  rw [h_integral]
  have h_sum : ∀ n : ℕ,
      (1 / (n : ℝ)) * ∑ k : Fin n, c * f ((k : ℝ) / (n : ℝ))
        = c * ((1 / (n : ℝ)) * ∑ k : Fin n, f ((k : ℝ) / (n : ℝ))) := by
    intro n
    rw [← Finset.mul_sum]
    ring
  refine (hf.const_mul c).congr ?_
  intro n
  exact (h_sum n).symm

/-- For `f` and `g` interval-integrable on `[0, 1]`, `A6Holds f` and `A6Holds g` imply
`A6Holds (f + g)`. -/
theorem A6Holds.add {f g : ℝ → ℝ}
    (hf : A6Holds f) (hg : A6Holds g)
    (hf_int : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg_int : IntervalIntegrable g MeasureTheory.volume 0 1) :
    A6Holds (fun x => f x + g x) := by
  unfold A6Holds at *
  have h_integral : (∫ x in (0 : ℝ)..1, (f x + g x))
      = (∫ x in (0 : ℝ)..1, f x) + (∫ x in (0 : ℝ)..1, g x) :=
    intervalIntegral.integral_add hf_int hg_int
  rw [h_integral]
  have h_sum : ∀ n : ℕ,
      (1 / (n : ℝ))
          * ∑ k : Fin n, (f ((k : ℝ) / (n : ℝ)) + g ((k : ℝ) / (n : ℝ)))
        = ((1 / (n : ℝ)) * ∑ k : Fin n, f ((k : ℝ) / (n : ℝ)))
          + ((1 / (n : ℝ)) * ∑ k : Fin n, g ((k : ℝ) / (n : ℝ))) := by
    intro n
    rw [Finset.sum_add_distrib]
    ring
  refine (hf.add hg).congr ?_
  intro n
  exact (h_sum n).symm

/-- `A6_for_constants` in the `A6Holds`-predicate form. -/
theorem A6Holds_const (c : ℝ) : A6Holds (fun _ => c) :=
  A6_for_constants c

/-- `A6_for_identity` in the `A6Holds`-predicate form. -/
theorem A6Holds_id : A6Holds (fun x => x) := A6_for_identity

/-- `A6_for_sq` in the `A6Holds`-predicate form. -/
theorem A6Holds_sq : A6Holds (fun x => x^2) := A6_for_sq

/-- `A6_for_cube` in the `A6Holds`-predicate form. -/
theorem A6Holds_cube : A6Holds (fun x => x^3) := A6_for_cube

/-- `A6Holds` for the zero function. -/
theorem A6Holds_zero : A6Holds (fun _ : ℝ => (0 : ℝ)) := A6Holds_const 0

/-- For `f` and `g` interval-integrable on `[0, 1]`, `A6Holds f` and `A6Holds g` imply
`A6Holds (f − g)`. -/
theorem A6Holds.sub {f g : ℝ → ℝ}
    (hf : A6Holds f) (hg : A6Holds g)
    (hf_int : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg_int : IntervalIntegrable g MeasureTheory.volume 0 1) :
    A6Holds (fun x => f x - g x) := by
  have h_neg_g : A6Holds (fun x => (-1) * g x) := hg.const_mul (-1)
  have h_neg_g_int : IntervalIntegrable (fun x : ℝ => (-1) * g x)
      MeasureTheory.volume 0 1 := hg_int.const_mul (-1)
  have h_eq : (fun x : ℝ => f x - g x) = (fun x : ℝ => f x + (-1) * g x) := by
    funext x; ring
  rw [h_eq]
  exact hf.add h_neg_g hf_int h_neg_g_int

/-- `A6Holds` for `a + b x + c x² + d x³`. -/
theorem A6Holds_poly_deg3 (a b c d : ℝ) :
    A6Holds (fun x => a + b * x + c * x^2 + d * x^3) := by
  have h_const_int : IntervalIntegrable (fun _ : ℝ => a)
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  have h_id_int : IntervalIntegrable (fun x : ℝ => x)
      MeasureTheory.volume 0 1 := continuous_id.intervalIntegrable 0 1
  have h_sq_int : IntervalIntegrable (fun x : ℝ => x^2)
      MeasureTheory.volume 0 1 := by
    exact (continuous_pow 2).intervalIntegrable 0 1
  have h_cube_int : IntervalIntegrable (fun x : ℝ => x^3)
      MeasureTheory.volume 0 1 := by
    exact (continuous_pow 3).intervalIntegrable 0 1
  have h_bx : IntervalIntegrable (fun x : ℝ => b * x)
      MeasureTheory.volume 0 1 := h_id_int.const_mul b
  have h_cx2 : IntervalIntegrable (fun x : ℝ => c * x^2)
      MeasureTheory.volume 0 1 := h_sq_int.const_mul c
  have h_dx3 : IntervalIntegrable (fun x : ℝ => d * x^3)
      MeasureTheory.volume 0 1 := h_cube_int.const_mul d
  have h_a_bx : IntervalIntegrable (fun x : ℝ => a + b * x)
      MeasureTheory.volume 0 1 := h_const_int.add h_bx
  have h_a_bx_cx2 : IntervalIntegrable
      (fun x : ℝ => a + b * x + c * x^2)
      MeasureTheory.volume 0 1 := h_a_bx.add h_cx2
  exact ((((A6Holds_const a).add (A6Holds_id.const_mul b) h_const_int h_bx).add
            (A6Holds_sq.const_mul c) h_a_bx h_cx2).add
          (A6Holds_cube.const_mul d) h_a_bx_cx2 h_dx3)

/-- For every `k`, `n · 2 sin(πk/n) → 2πk`. The number `2 sin(πk/n)` is the square root of
`−cycleEigenvalue n k`. -/
def DiscreteWaveToContinuumWave : Prop :=
  ∀ (k : ℕ),
    Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) * (2 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))))
      Filter.atTop
      (nhds (2 * Real.pi * k))

/-- For every `k`, `n² · 4 sin²(πk/n) → (2πk)²`. This is `cycleEigenvalue_scaled_tendsto`
with the sign reversed. -/
def DiscreteSchrodingerToContinuumSchrodinger : Prop :=
  ∀ (k : ℕ),
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ))^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2))
      Filter.atTop
      (nhds ((2 * Real.pi * k)^2))

/-- `DiscreteWaveToContinuumWave` holds, from `n · sin(πk/n) → πk`
(`n_sin_pi_k_div_n_tendsto`). -/
theorem discreteWaveToContinuumWave_holds :
    DiscreteWaveToContinuumWave := by
  intro k
  have h1 := n_sin_pi_k_div_n_tendsto k
  have h2 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * ((n : ℝ) * Real.sin (Real.pi * k / n)))
      Filter.atTop (nhds (2 * (Real.pi * k))) :=
    h1.const_mul 2
  have h_eq : ∀ n : ℕ, (2 : ℝ) * ((n : ℝ) * Real.sin (Real.pi * k / n))
      = (n : ℝ) * (2 * Real.sin (Real.pi * k / n)) := by
    intro n; ring
  have h_target : 2 * (Real.pi * (k : ℝ)) = 2 * Real.pi * k := by ring
  rw [h_target] at h2
  exact h2.congr h_eq

/-- `DiscreteSchrodingerToContinuumSchrodinger` holds, by negating
`cycleEigenvalue_scaled_tendsto`. -/
theorem discreteSchrodingerToContinuumSchrodinger_holds :
    DiscreteSchrodingerToContinuumSchrodinger := by
  intro k
  have hA4 := cycleEigenvalue_scaled_tendsto k
  -- hA4: n² · (−4 sin²(π k / n)) → −(2πk)²; negate it.
  have hneg : Filter.Tendsto
      (fun n : ℕ => - ((n : ℝ)^2 * cycleEigenvalue n k))
      Filter.atTop (nhds (-(-(2 * Real.pi * k)^2))) := hA4.neg
  have h_eq : ∀ n : ℕ, - ((n : ℝ)^2 * cycleEigenvalue n k)
      = (n : ℝ)^2 * (4 * (Real.sin (Real.pi * k / n))^2) := by
    intro n
    unfold cycleEigenvalue
    ring
  have h_target : -(-(2 * Real.pi * (k : ℝ))^2) = (2 * Real.pi * k)^2 := by ring
  rw [h_target] at hneg
  exact hneg.congr h_eq

/-- For every `k`, `n² · 4 sin²(πk/n) + m² → (2πk)² + m²`. -/
def DiscreteKleinGordonSpectrum (m : ℝ) : Prop :=
  ∀ (k : ℕ),
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ))^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2)
        + m^2)
      Filter.atTop
      (nhds ((2 * Real.pi * k)^2 + m^2))

/-- `DiscreteKleinGordonSpectrum m` holds, from
`discreteSchrodingerToContinuumSchrodinger_holds` and the constant limit `m²`. -/
theorem discreteKleinGordonSpectrum_holds (m : ℝ) :
    DiscreteKleinGordonSpectrum m := by
  intro k
  have h_schr := discreteSchrodingerToContinuumSchrodinger_holds k
  have h_const : Filter.Tendsto (fun _ : ℕ => m^2) Filter.atTop (nhds (m^2)) :=
    tendsto_const_nhds
  exact h_schr.add h_const

/-! ## C. The quadratic case of `CycleLaplacianConvergenceC2` -/

/-- For `f(y) = a y² + b y + c`, `scaledSecondDiff f n x` equals `f''(x)` for every `n > 0`,
so it tends to `f''(x)`. -/
theorem cycle_laplacian_conv_polynomial (a b c : ℝ) (x : ℝ) :
    Filter.Tendsto
      (fun n : Nat => scaledSecondDiff (fun y => a * y^2 + b * y + c) n x)
      Filter.atTop
      (nhds (deriv (deriv (fun y => a * y^2 + b * y + c)) x)) := by
  have hconst : ∀ n : Nat, 0 < n →
      scaledSecondDiff (fun y => a * y^2 + b * y + c) n x
      = deriv (deriv (fun y => a * y^2 + b * y + c)) x :=
    fun n hn => polynomial_scaled_laplacian_eq_second_deriv a b c n hn x
  rw [Metric.tendsto_atTop]
  intros ε hε
  refine ⟨1, fun n hn => ?_⟩
  rw [hconst n hn]
  simpa using hε

end InfraFormalization
