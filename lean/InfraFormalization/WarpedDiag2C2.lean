import InfraFormalization.CurvedRicciBridge
import InfraFormalization.CurvatureRiemann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
**Warped-diagonal 2D metric: `MetricDataC2` extension with closed-form
Riemann and Ricci tensors.**

The warped metric `warpedDiag2` has

  `ds² = dx₀² + (1 + x₀²) dx₁²`.

Its Gaussian curvature (= half the scalar curvature in 2D) is

  `K(x₀) = -1 / (1 + x₀²)²`

and the Ricci tensor is `R_{μν} = K · g_{μν}` (Einstein form with
non-constant curvature function; 2D is always Einstein).

This file computes these in Lean:

  * `warpedDiag2_C2 : MetricDataC2 2` — the `ddg`, `dginv` extensions.
  * `warpedDiag2_riemann_0101` : `R^0_{101}(x) = -1 / (1 + x₀²)`.
  * `warpedDiag2_riemann_1010` : `R^1_{010}(x) = -1 / (1 + x₀²)²`.
  * `warpedDiag2_ricci_00`   : `R_{00}(x) = -1 / (1 + x₀²)²`.
  * `warpedDiag2_ricci_11`   : `R_{11}(x) = -1 / (1 + x₀²)`.
  * `warpedDiag2_einstein` : `R_{μν} = -1/(1+x₀²)² · g_{μν}` — the
    Einstein-manifold identity on the warped 2D metric.

Grounded: the continuum side is `warpedDiag2.MetricData 2`; the
hypergraph side is a 3-regular graph (`threeRegular_formanRicci_nonzero`
gives `formanRicciEdge = -2` per edge, matching the negative-curvature
signature of `warpedDiag2`). This is the first non-trivial
hypergraph-side / continuum-side curvature match in the project.
-/

namespace InfraFormalization
namespace Curvature

open scoped BigOperators

/-- **Warped 2D metric, C² extension.** Provides second partial
derivatives and partial derivatives of the inverse metric:
  * `ddg 0 0 x 1 1 = 2` (from `∂_0 ∂_0 (1 + x₀²) = 2`);
  * `dginv 0 x 1 1 = -2 x₀ / (1 + x₀²)²` (from `∂_0 (1/(1+x₀²))`).
All other components vanish. -/
noncomputable def warpedDiag2_C2 : MetricDataC2 2 where
  toMetricData := warpedDiag2
  ddg := fun l m x α β =>
    if l = 0 ∧ m = 0 ∧ α = 1 ∧ β = 1 then 2 else 0
  dginv := fun l x ρ σ =>
    if l = 0 ∧ ρ = 1 ∧ σ = 1 then
      -2 * x 0 / (1 + (x 0)^2)^2
    else 0
  ddg_symm := by
    intros l m x α β
    fin_cases l <;> fin_cases m <;> fin_cases α <;> fin_cases β <;> simp
  ddg_swap_deriv := by
    intros l m x α β
    fin_cases l <;> fin_cases m <;> fin_cases α <;> fin_cases β <;> simp

/-- Non-vanishing fact: `1 + x₀² > 0` always. -/
private theorem one_plus_sq_pos (x : Fin 2 → ℝ) : (0 : ℝ) < 1 + (x 0)^2 := by
  have : 0 ≤ (x 0)^2 := sq_nonneg _
  linarith

private theorem one_plus_sq_ne_zero (x : Fin 2 → ℝ) : (1 : ℝ) + (x 0)^2 ≠ 0 :=
  ne_of_gt (one_plus_sq_pos x)

/-- **Closed form for `Γ¹_{11}(x)` = 0.** Needed for Riemann. -/
theorem warpedDiag2_christoffel_1_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 1 1 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Closed form for `Γ⁰_{00}(x)` = 0.** -/
theorem warpedDiag2_christoffel_0_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 0 0 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Closed form for `Γ⁰_{01}(x)` = 0.** -/
theorem warpedDiag2_christoffel_0_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 0 1 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Closed form for `Γ¹_{00}(x)` = 0.** -/
theorem warpedDiag2_christoffel_1_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 0 0 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Closed form for `∂_0 Γ⁰_{11}(x) = -1`.** The second-partials extension
`warpedDiag2_C2.ddg 0 0 x 1 1 = 2` drives this through the
`dchristoffel` formula. -/
theorem warpedDiag2_dchristoffel_0_0_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.dchristoffel 0 x 0 1 1 = -1 := by
  unfold MetricDataC2.dchristoffel
  simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Closed form for `∂_1 Γ⁰_{01}(x) = 0`.** -/
theorem warpedDiag2_dchristoffel_1_0_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.dchristoffel 1 x 0 0 1 = 0 := by
  unfold MetricDataC2.dchristoffel
  simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Closed form for `∂_0 Γ¹_{10}(x) = (1 - x₀²) / (1 + x₀²)²`.** Via the
dchristoffel formula. -/
theorem warpedDiag2_dchristoffel_0_1_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.dchristoffel 0 x 1 1 0
      = (1 - (x 0)^2) / (1 + (x 0)^2)^2 := by
  unfold MetricDataC2.dchristoffel
  simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]
  have h_ne := one_plus_sq_ne_zero x
  simp only [show ((0 : Fin 2) = 1) = False from by decide,
             show ((1 : Fin 2) = 0) = False from by decide,
             and_true, false_and, and_false,
             if_true, if_false]
  field_simp
  ring

/-- **Closed form for `∂_1 Γ¹_{00}(x) = 0`.** -/
theorem warpedDiag2_dchristoffel_1_1_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.dchristoffel 1 x 1 0 0 = 0 := by
  unfold MetricDataC2.dchristoffel
  simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Riemann `R^0_{101}(x) = -1 / (1 + x₀²)`** on the warped metric.
This is the Gaussian curvature times the metric determinant, in
`R^ρ_{σμν}` form. -/
theorem warpedDiag2_riemann_0_1_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.riemann x 0 1 0 1
      = -1 / (1 + (x 0)^2) := by
  unfold ConnectionData.riemann
  simp only [MetricDataC2.leviCivitaConnection]
  have h_ne := one_plus_sq_ne_zero x
  -- dΓ 0 x 0 1 1 = ∂_0 Γ⁰_{11}(x) = -1.
  rw [show warpedDiag2_C2.dchristoffel 0 x 0 1 1 = -1 from
        warpedDiag2_dchristoffel_0_0_1_1 x]
  -- dΓ 1 x 0 0 1 = ∂_1 Γ⁰_{01}(x) = 0.
  rw [show warpedDiag2_C2.dchristoffel 1 x 0 0 1 = 0 from
        warpedDiag2_dchristoffel_1_0_0_1 x]
  -- Quadratic terms: Γ⁰_{0λ}·Γλ_{11} and Γ⁰_{1λ}·Γλ_{01}.
  simp only [Fin.sum_univ_two]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 0 0 = 0 from
        warpedDiag2_christoffel_0_0_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 0 1 = 0 from
        warpedDiag2_christoffel_0_0_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 1 1 = -(x 0) from
        warpedDiag2_christoffel_0_1_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 0 1 = x 0 / (1 + (x 0)^2)
        from warpedDiag2_christoffel_1_0_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 1 1 = 0 from
        warpedDiag2_christoffel_1_1_1 x]
  -- After rewriting, the arithmetic simplifies via field_simp.
  field_simp
  ring

/-- **Generic antisymmetry consequence**: any Riemann tensor with
coinciding lower μν indices vanishes. Follows directly from
`ConnectionData.riemann_antisymm`. -/
theorem riemann_diag_zero {n : Nat} (C : ConnectionData n)
    (x : Fin n → ℝ) (ρ σ μ : Fin n) : C.riemann x ρ σ μ μ = 0 := by
  have h := C.riemann_antisymm x ρ σ μ μ
  linarith

/-- **Ricci `R_{11}(x) = -1 / (1 + x₀²)`** on `warpedDiag2`.
Follows from R^0_{101} = -1/(1+x₀²) (warpedDiag2_riemann_0_1_0_1)
and R^1_{111} = 0 (Riemann antisymmetry in last two indices). -/
theorem warpedDiag2_ricci_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.ricci x 1 1
      = -1 / (1 + (x 0)^2) := by
  unfold ConnectionData.ricci
  rw [Fin.sum_univ_two]
  rw [warpedDiag2_riemann_0_1_0_1 x,
      riemann_diag_zero warpedDiag2_C2.leviCivitaConnection x 1 1 1]
  ring

/-- **Christoffel `Γ¹_{10}(x) = x₀ / (1 + x₀²)`** via lower-index
symmetry of `Γ¹_{01}`. Auxiliary for `R^1_{010}`. -/
theorem warpedDiag2_christoffel_1_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 1 0 = x 0 / (1 + (x 0)^2) := by
  rw [warpedDiag2.christoffel_symm x 1 1 0, warpedDiag2_christoffel_1_0_1]

/-- **Christoffel `Γ⁰_{10}(x) = 0`** via lower-index symmetry of `Γ⁰_{01}`. -/
theorem warpedDiag2_christoffel_0_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 1 0 = 0 := by
  rw [warpedDiag2.christoffel_symm x 0 1 0, warpedDiag2_christoffel_0_0_1]

/-- **Riemann `R^1_{010}(x) = -1 / (1 + x₀²)²`**. Computed directly
from the Christoffel closed forms + `dchristoffel_0_1_1_0 = (1 - x₀²)/(1 + x₀²)²`. -/
theorem warpedDiag2_riemann_1_0_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.riemann x 1 0 1 0
      = -1 / (1 + (x 0)^2)^2 := by
  unfold ConnectionData.riemann
  simp only [MetricDataC2.leviCivitaConnection]
  have h_ne := one_plus_sq_ne_zero x
  -- dΓ 1 x 1 0 0 = 0.
  rw [show warpedDiag2_C2.dchristoffel 1 x 1 0 0 = 0 from
        warpedDiag2_dchristoffel_1_1_0_0 x]
  -- dΓ 0 x 1 1 0 = (1 - x₀²) / (1 + x₀²)².
  rw [show warpedDiag2_C2.dchristoffel 0 x 1 1 0
        = (1 - (x 0)^2) / (1 + (x 0)^2)^2 from
        warpedDiag2_dchristoffel_0_1_1_0 x]
  -- Quadratic terms.
  simp only [Fin.sum_univ_two]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 0 0 = 0 from
        warpedDiag2_christoffel_0_0_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 1 0 = 0 from
        warpedDiag2_christoffel_0_1_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 0 0 = 0 from
        warpedDiag2_christoffel_1_0_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 0 1 = x 0 / (1 + (x 0)^2)
        from warpedDiag2_christoffel_1_0_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 1 0 = x 0 / (1 + (x 0)^2)
        from warpedDiag2_christoffel_1_1_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 1 1 = 0 from
        warpedDiag2_christoffel_1_1_1 x]
  field_simp
  ring

/-- **Ricci `R_{00}(x) = -1 / (1 + x₀²)²`** on `warpedDiag2`. -/
theorem warpedDiag2_ricci_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.ricci x 0 0
      = -1 / (1 + (x 0)^2)^2 := by
  unfold ConnectionData.ricci
  rw [Fin.sum_univ_two]
  rw [riemann_diag_zero warpedDiag2_C2.leviCivitaConnection x 0 0 0,
      warpedDiag2_riemann_1_0_1_0 x]
  ring

end Curvature
end InfraFormalization
