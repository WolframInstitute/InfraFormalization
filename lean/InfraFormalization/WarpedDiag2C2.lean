import InfraFormalization.CurvedRicciBridge
import InfraFormalization.CurvatureRiemann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Curvature of the warped metric `ds² = dx₀² + (1 + x₀²) dx₁²`.

This module extends `warpedDiag2` to `MetricDataC2 2` with second partial
derivatives and derivatives of the inverse metric, and computes the
Christoffel symbols, the Riemann components, the Ricci tensor
`R_{μν} = K g_{μν}` with `K = −1/(1 + x₀²)²`, the scalar curvature
`−2/(1 + x₀²)²`, and the Einstein tensor, which is 0. No theorem in this
module relates these values to a hypergraph.
-/

namespace InfraFormalization
namespace Curvature

open scoped BigOperators

/-- `warpedDiag2` with second partial derivatives `ddg 0 0 x 1 1 = 2` and
inverse-metric derivatives `dginv 0 x 1 1 = −2 x₀ / (1 + x₀²)²`, all other
components 0. -/
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

/-- `1 + x₀² > 0`. -/
private theorem one_plus_sq_pos (x : Fin 2 → ℝ) : (0 : ℝ) < 1 + (x 0)^2 := by
  have : 0 ≤ (x 0)^2 := sq_nonneg _
  linarith

private theorem one_plus_sq_ne_zero (x : Fin 2 → ℝ) : (1 : ℝ) + (x 0)^2 ≠ 0 :=
  ne_of_gt (one_plus_sq_pos x)

/-- `Γ¹_{11}(x) = 0`. -/
theorem warpedDiag2_christoffel_1_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 1 1 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- `Γ⁰_{00}(x) = 0`. -/
theorem warpedDiag2_christoffel_0_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 0 0 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- `Γ⁰_{01}(x) = 0`. -/
theorem warpedDiag2_christoffel_0_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 0 1 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- `Γ¹_{00}(x) = 0`. -/
theorem warpedDiag2_christoffel_1_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 0 0 = 0 := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- `∂_0 Γ⁰_{11}(x) = −1`. -/
theorem warpedDiag2_dchristoffel_0_0_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.dchristoffel 0 x 0 1 1 = -1 := by
  unfold MetricDataC2.dchristoffel
  simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]
  simp

/-- `∂_1 Γ⁰_{01}(x) = 0`. -/
theorem warpedDiag2_dchristoffel_1_0_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.dchristoffel 1 x 0 0 1 = 0 := by
  unfold MetricDataC2.dchristoffel
  simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]
  simp

/-- `∂_0 Γ¹_{10}(x) = (1 − x₀²) / (1 + x₀²)²`. -/
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

/-- `∂_1 Γ¹_{00}(x) = 0`. -/
theorem warpedDiag2_dchristoffel_1_1_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.dchristoffel 1 x 1 0 0 = 0 := by
  unfold MetricDataC2.dchristoffel
  simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]
  simp

/-- For the Levi-Civita connection of `warpedDiag2_C2`,
`R^0_{101}(x) = −1 / (1 + x₀²)`. -/
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
  field_simp
  ring

/-- For every connection, `R^ρ_{σμμ} = 0`, by
`ConnectionData.riemann_antisymm`. -/
theorem riemann_diag_zero {n : Nat} (C : ConnectionData n)
    (x : Fin n → ℝ) (ρ σ μ : Fin n) : C.riemann x ρ σ μ μ = 0 := by
  have h := C.riemann_antisymm x ρ σ μ μ
  linarith

/-- `R_{11}(x) = −1 / (1 + x₀²)`, from `R^0_{101}` and `R^1_{111} = 0`. -/
theorem warpedDiag2_ricci_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.ricci x 1 1
      = -1 / (1 + (x 0)^2) := by
  unfold ConnectionData.ricci
  rw [Fin.sum_univ_two]
  rw [warpedDiag2_riemann_0_1_0_1 x,
      riemann_diag_zero warpedDiag2_C2.leviCivitaConnection x 1 1 1]
  ring

/-- `Γ¹_{10}(x) = x₀ / (1 + x₀²)`, by lower-index symmetry. -/
theorem warpedDiag2_christoffel_1_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 1 0 = x 0 / (1 + (x 0)^2) := by
  rw [warpedDiag2.christoffel_symm x 1 1 0, warpedDiag2_christoffel_1_0_1]

/-- `Γ⁰_{10}(x) = 0`, by lower-index symmetry. -/
theorem warpedDiag2_christoffel_0_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 1 0 = 0 := by
  rw [warpedDiag2.christoffel_symm x 0 1 0, warpedDiag2_christoffel_0_0_1]

/-- `R^1_{010}(x) = −1 / (1 + x₀²)²`. -/
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

/-- `R_{00}(x) = −1 / (1 + x₀²)²`. -/
theorem warpedDiag2_ricci_0_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.ricci x 0 0
      = -1 / (1 + (x 0)^2)^2 := by
  unfold ConnectionData.ricci
  rw [Fin.sum_univ_two]
  rw [riemann_diag_zero warpedDiag2_C2.leviCivitaConnection x 0 0 0,
      warpedDiag2_riemann_1_0_1_0 x]
  ring

/-- `R^0_{001}(x) = 0`. -/
theorem warpedDiag2_riemann_0_0_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.riemann x 0 0 0 1 = 0 := by
  unfold ConnectionData.riemann
  simp only [MetricDataC2.leviCivitaConnection]
  rw [show warpedDiag2_C2.dchristoffel 0 x 0 1 0 = 0 by
        unfold MetricDataC2.dchristoffel
        simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]; simp]
  rw [show warpedDiag2_C2.dchristoffel 1 x 0 0 0 = 0 by
        unfold MetricDataC2.dchristoffel
        simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]; simp]
  simp only [Fin.sum_univ_two]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 0 0 = 0 from
        warpedDiag2_christoffel_0_0_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 1 1 = -(x 0) from
        warpedDiag2_christoffel_0_1_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 1 0 = 0 from
        warpedDiag2_christoffel_0_1_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 1 0 = x 0 / (1 + (x 0)^2)
        from warpedDiag2_christoffel_1_1_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 0 1 = 0 from
        warpedDiag2_christoffel_0_0_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 0 0 = 0 from
        warpedDiag2_christoffel_1_0_0 x]
  ring

/-- `R_{01}(x) = 0`. -/
theorem warpedDiag2_ricci_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.ricci x 0 1 = 0 := by
  unfold ConnectionData.ricci
  rw [Fin.sum_univ_two]
  rw [warpedDiag2_riemann_0_0_0_1 x,
      riemann_diag_zero warpedDiag2_C2.leviCivitaConnection x 1 0 1]
  ring

/-- `R^1_{110}(x) = 0`. -/
theorem warpedDiag2_riemann_1_1_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.riemann x 1 1 1 0 = 0 := by
  unfold ConnectionData.riemann
  simp only [MetricDataC2.leviCivitaConnection]
  rw [show warpedDiag2_C2.dchristoffel 1 x 1 0 1 = 0 by
        unfold MetricDataC2.dchristoffel
        simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]; simp]
  rw [show warpedDiag2_C2.dchristoffel 0 x 1 1 1 = 0 by
        unfold MetricDataC2.dchristoffel
        simp only [warpedDiag2_C2, warpedDiag2, Fin.sum_univ_two]; simp]
  simp only [Fin.sum_univ_two]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 1 0 = x 0 / (1 + (x 0)^2)
        from warpedDiag2_christoffel_1_1_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 0 1 = 0 from
        warpedDiag2_christoffel_0_0_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 1 1 = 0 from
        warpedDiag2_christoffel_1_1_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 0 0 = 0 from
        warpedDiag2_christoffel_1_0_0 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 0 1 1 = -(x 0) from
        warpedDiag2_christoffel_0_1_1 x]
  rw [show warpedDiag2_C2.toMetricData.christoffel x 1 0 1 = x 0 / (1 + (x 0)^2)
        from warpedDiag2_christoffel_1_0_1 x]
  ring

/-- `R_{10}(x) = 0`. -/
theorem warpedDiag2_ricci_1_0 (x : Fin 2 → ℝ) :
    warpedDiag2_C2.leviCivitaConnection.ricci x 1 0 = 0 := by
  unfold ConnectionData.ricci
  rw [Fin.sum_univ_two]
  rw [riemann_diag_zero warpedDiag2_C2.leviCivitaConnection x 0 1 0,
      warpedDiag2_riemann_1_1_1_0 x]
  ring

/-- `R_{μν}(x) = R_{νμ}(x)`, by cases on `(μ, ν)`. -/
theorem warpedDiag2_ricci_symm (x : Fin 2 → ℝ) (μ ν : Fin 2) :
    warpedDiag2_C2.leviCivitaConnection.ricci x μ ν
      = warpedDiag2_C2.leviCivitaConnection.ricci x ν μ := by
  match μ, ν with
  | 0, 0 => rfl
  | 0, 1 => rw [warpedDiag2_ricci_0_1 x, warpedDiag2_ricci_1_0 x]
  | 1, 0 => rw [warpedDiag2_ricci_0_1 x, warpedDiag2_ricci_1_0 x]
  | 1, 1 => rfl

/-- `R_{μν}(x) = K(x) · g_{μν}(x)` with `K(x) = −1 / (1 + x₀²)²`. -/
theorem warpedDiag2_einstein (x : Fin 2 → ℝ) (μ ν : Fin 2) :
    warpedDiag2_C2.leviCivitaConnection.ricci x μ ν
      = (-1 / (1 + (x 0)^2)^2) * warpedDiag2.g x μ ν := by
  have h_ne := one_plus_sq_ne_zero x
  have h_sq_ne : ((1 : ℝ) + (x 0)^2)^2 ≠ 0 := pow_ne_zero _ h_ne
  match μ, ν with
  | 0, 0 => rw [warpedDiag2_ricci_0_0 x]; simp [warpedDiag2]
  | 0, 1 => rw [warpedDiag2_ricci_0_1 x]; simp [warpedDiag2]
  | 1, 0 => rw [warpedDiag2_ricci_1_0 x]; simp [warpedDiag2]
  | 1, 1 =>
    rw [warpedDiag2_ricci_1_1 x]
    show -1 / (1 + (x 0)^2) = -1 / (1 + (x 0)^2)^2 * warpedDiag2.g x 1 1
    simp only [warpedDiag2]
    simp only [show ((1 : Fin 2) = 0) = False from by decide,
               false_and, and_true, if_false, if_true, true_and]
    field_simp

/-- The scalar curvature is `R(x) = −2 / (1 + x₀²)²`. -/
theorem warpedDiag2_scalarCurvature (x : Fin 2 → ℝ) :
    ConnectionData.scalarCurvature warpedDiag2
        warpedDiag2_C2.leviCivitaConnection x
      = -2 / (1 + (x 0)^2)^2 := by
  have h_ne := one_plus_sq_ne_zero x
  have h_sq_ne : ((1 : ℝ) + (x 0)^2)^2 ≠ 0 := pow_ne_zero _ h_ne
  unfold ConnectionData.scalarCurvature
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [warpedDiag2_ricci_0_0 x, warpedDiag2_ricci_0_1 x,
      warpedDiag2_ricci_1_0 x, warpedDiag2_ricci_1_1 x]
  simp [warpedDiag2]
  field_simp
  ring

/-- The Einstein tensor `G_{μν}(x) = R_{μν} − (1/2) R g_{μν}` is 0 for all
`μ`, `ν` and `x`. -/
theorem warpedDiag2_einsteinTensor_zero (x : Fin 2 → ℝ) (μ ν : Fin 2) :
    ConnectionData.einsteinTensor warpedDiag2
        warpedDiag2_C2.leviCivitaConnection x μ ν = 0 := by
  have h_ne := one_plus_sq_ne_zero x
  have h_sq_ne : ((1 : ℝ) + (x 0)^2)^2 ≠ 0 := pow_ne_zero _ h_ne
  unfold ConnectionData.einsteinTensor
  rw [warpedDiag2_scalarCurvature x, warpedDiag2_einstein x μ ν]
  match μ, ν with
  | 0, 0 => simp [warpedDiag2]; field_simp; ring
  | 0, 1 => simp [warpedDiag2]
  | 1, 0 => simp [warpedDiag2]
  | 1, 1 =>
    simp only [warpedDiag2]
    simp only [show ((1 : Fin 2) = 0) = False from by decide,
               false_and, if_false]
    field_simp
    ring

/-- `∑_μ Γ^μ_{μν}(x) · G_{μν}(x) = 0`, since every `G_{μν}(x)` is 0. The
statement is this sum, not the covariant divergence `∇_μ G^{μν}`. -/
theorem warpedDiag2_christoffel_trace_einstein_zero (x : Fin 2 → ℝ) (ν : Fin 2) :
    ∑ μ : Fin 2, warpedDiag2_C2.leviCivitaConnection.Γ x μ μ ν
          * ConnectionData.einsteinTensor warpedDiag2
              warpedDiag2_C2.leviCivitaConnection x μ ν = 0 := by
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  rw [warpedDiag2_einsteinTensor_zero x μ ν]
  ring

end Curvature
end InfraFormalization
