/-
Limits of quadratic polynomials divided by `n²`, and the 3D torus.

The module proves that `(a·n² + b·n + c)/n²` tends to `a` for all real `a`, `b`, `c`, and applies
this to the grid closed forms `gridFormanClosedForm` and `gridHiguchiClosedForm`, whose quotients
by `n²` tend to `-16` and `-2`. It defines the 3D torus `torus3HG m n k` and proves, with
`native_decide`, that its Forman scalar equals `-48n³` at `n ∈ {4, 5}` and its doubled Higuchi
total equals `-4n³` at `n ∈ {3, 4, 5}`.
-/

import InfraFormalization.NormalizedDensityLimits

namespace InfraFormalization
namespace PolynomialDensityLimits

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener
open AdvancedContinuumLimits
open GridContinuumLimit
open NormalizedDensityLimits
open Filter

/-! ## Limit of a quadratic divided by `n²`

For real `a`, `b`, `c` the sequence `(a·n² + b·n + c)/n²` tends to `a`. The proof rewrites the
quotient as `a + b/n + c/n²` and uses `1/n → 0`. -/

/-- `b/n → 0` as `n → ∞` for any real `b`. -/
lemma tendsto_const_div_natCast_atTop_zero (b : ℝ) :
    Tendsto (fun n : ℕ => b / (n : ℝ)) atTop (nhds 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat).const_mul b
  simpa [mul_div_assoc'] using h

/-- `c/n² → 0` as `n → ∞` for any real `c`. -/
lemma tendsto_const_div_natCast_sq_atTop_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / ((n : ℝ)^2)) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * (1 / (n : ℝ))) atTop (nhds 0) := by
    simpa using h1.mul h1
  have h3 : Tendsto (fun n : ℕ => c * ((1 / (n : ℝ)) * (1 / (n : ℝ)))) atTop (nhds 0) := by
    simpa using h2.const_mul c
  apply h3.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- For real `a`, `b`, `c`, the sequence `(a·n² + b·n + c)/n²` tends to `a` as `n → ∞`. -/
theorem polynomialPerArea_tendsto (a b c : ℝ) :
    Tendsto (fun n : ℕ =>
        (a * (n : ℝ)^2 + b * (n : ℝ) + c) / ((n : ℝ)^2))
      atTop (nhds a) := by
  have key :
      Tendsto (fun n : ℕ => a + b / (n : ℝ) + c / ((n : ℝ)^2))
        atTop (nhds (a + 0 + 0)) := by
    refine ((tendsto_const_nhds (x := a)).add ?_).add ?_
    · exact tendsto_const_div_natCast_atTop_zero b
    · exact tendsto_const_div_natCast_sq_atTop_zero c
  have key' : Tendsto (fun n : ℕ => a + b / (n : ℝ) + c / ((n : ℝ)^2))
                atTop (nhds a) := by
    simpa using key
  apply key'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn2 : ((n : ℝ)^2) ≠ 0 := pow_ne_zero 2 hn'
  field_simp

/-! ## 3D torus

For `n ≥ 4` every vertex of `torus3HG n n n` has degree 6 and no edge lies on a triangle. -/

/-- The 3D torus `T³(m, n, k)` as `ExecHG ℕ`. Each vertex `(i, j, l)`
has 6 neighbors (one in each of the 3 directions, both forward and
backward via the wraparound). -/
def torus3HG (m n k : ℕ) : ExecHG ℕ :=
  let nodeId : ℕ → ℕ → ℕ → ℕ := fun i j l => i * (n * k) + j * k + l
  let dirX : List (Hyperedge ℕ) :=
    (List.range m).flatMap (fun i =>
      (List.range n).flatMap (fun j =>
        (List.range k).map (fun l =>
          ⟨[nodeId i j l, nodeId ((i + 1) % m) j l], List.cons_ne_nil _ _⟩)))
  let dirY : List (Hyperedge ℕ) :=
    (List.range m).flatMap (fun i =>
      (List.range n).flatMap (fun j =>
        (List.range k).map (fun l =>
          ⟨[nodeId i j l, nodeId i ((j + 1) % n) l], List.cons_ne_nil _ _⟩)))
  let dirZ : List (Hyperedge ℕ) :=
    (List.range m).flatMap (fun i =>
      (List.range n).flatMap (fun j =>
        (List.range k).map (fun l =>
          ⟨[nodeId i j l, nodeId i j ((l + 1) % k)], List.cons_ne_nil _ _⟩)))
  dirX ++ dirY ++ dirZ

/-! ### T³ Forman closed form: `-48 n³`

Checked at `n ∈ {4, 5}`. At `n = 3` the wraparound edges form triangles. -/

def torus3FormanClosedForm (n : ℕ) : ℤ := -48 * (n : ℤ)^3

theorem torus3_4_4_4_forman_closed_form :
    execFormanScalar (torus3HG 4 4 4) = torus3FormanClosedForm 4 := by
  show execFormanScalar (torus3HG 4 4 4) = -48 * 64
  native_decide

theorem torus3_5_5_5_forman_closed_form :
    execFormanScalar (torus3HG 5 5 5) = torus3FormanClosedForm 5 := by
  show execFormanScalar (torus3HG 5 5 5) = -48 * 125
  native_decide

/-! ### T³ Higuchi closed form: `-4 n³`

Checked at `n ∈ {3, 4, 5}`. -/

def torus3HiguchiClosedForm (n : ℕ) : ℤ := -4 * (n : ℤ)^3

theorem torus3_3_3_3_higuchi_closed_form :
    higuchiTotalDoubled (torus3HG 3 3 3) = torus3HiguchiClosedForm 3 := by
  show higuchiTotalDoubled (torus3HG 3 3 3) = -4 * 27
  native_decide

theorem torus3_4_4_4_higuchi_closed_form :
    higuchiTotalDoubled (torus3HG 4 4 4) = torus3HiguchiClosedForm 4 := by
  show higuchiTotalDoubled (torus3HG 4 4 4) = -4 * 64
  native_decide

theorem torus3_5_5_5_higuchi_closed_form :
    higuchiTotalDoubled (torus3HG 5 5 5) = torus3HiguchiClosedForm 5 := by
  show higuchiTotalDoubled (torus3HG 5 5 5) = -4 * 125
  native_decide

/-! ## Grid closed forms divided by `n²`

`polynomialPerArea_tendsto` applied with `(a, b, c) = (-16, 40, -16)` and `(-2, 4, 0)`. The
sequences are defined from the closed-form polynomials of `NormalizedDensityLimits`. -/

/-- The real sequence `gridFormanClosedForm n / n²`. -/
noncomputable def gridFormanPerAreaSeq : ℕ → ℝ :=
  fun n => (gridFormanClosedForm n : ℝ) / ((n : ℝ)^2)

/-- `gridFormanClosedForm n / n²` tends to `-16`. -/
theorem gridFormanClosedForm_div_sq_tendsto_neg16 :
    Tendsto gridFormanPerAreaSeq atTop (nhds (-16)) := by
  have key : Tendsto
      (fun n : ℕ => (-16 * (n : ℝ)^2 + 40 * (n : ℝ) + (-16)) / ((n : ℝ)^2))
      atTop (nhds (-16)) := polynomialPerArea_tendsto (-16) 40 (-16)
  apply key.congr'
  filter_upwards [eventually_gt_atTop 0] with n _
  show (-16 * (n : ℝ)^2 + 40 * (n : ℝ) + (-16)) / ((n : ℝ)^2)
       = gridFormanPerAreaSeq n
  unfold gridFormanPerAreaSeq gridFormanClosedForm
  push_cast
  ring

/-- The real sequence `gridHiguchiClosedForm n / n²`. -/
noncomputable def gridHiguchiPerAreaSeq : ℕ → ℝ :=
  fun n => (gridHiguchiClosedForm n : ℝ) / ((n : ℝ)^2)

/-- `gridHiguchiClosedForm n / n²` tends to `-2`. -/
theorem gridHiguchiClosedForm_div_sq_tendsto_neg2 :
    Tendsto gridHiguchiPerAreaSeq atTop (nhds (-2)) := by
  have key : Tendsto
      (fun n : ℕ => (-2 * (n : ℝ)^2 + 4 * (n : ℝ) + 0) / ((n : ℝ)^2))
      atTop (nhds (-2)) := polynomialPerArea_tendsto (-2) 4 0
  apply key.congr'
  filter_upwards [eventually_gt_atTop 0] with n _
  show (-2 * (n : ℝ)^2 + 4 * (n : ℝ) + 0) / ((n : ℝ)^2)
       = gridHiguchiPerAreaSeq n
  unfold gridHiguchiPerAreaSeq gridHiguchiClosedForm
  push_cast
  ring

end PolynomialDensityLimits
end InfraFormalization
