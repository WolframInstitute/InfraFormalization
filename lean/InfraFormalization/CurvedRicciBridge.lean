/-
A warped 2-D metric with nonzero Christoffel symbols, and the Forman
edge value on 3-regular neighbourhood structures.

This module defines the metric `warpedDiag2` with `g₀₀ = 1`,
`g₁₁ = 1 + x₀²` and zero off-diagonal entries. It computes
`Γ¹_{01} = x₀ / (1 + x₀²)` and `Γ⁰_{11} = −x₀`, and proves
`Γ¹_{01} ≠ 0` where `x₀ ≠ 0`. It also proves that `formanRicciEdge`
equals −2 on every edge of a 3-regular `Neighbourhood`. No statement
relates the discrete and continuum quantities.
-/

import InfraFormalization.DiscreteRicci
import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization

open Curvature

/-- The diagonal 2-D metric with `g₀₀ = 1` and `g₁₁ = 1 + x₀²`. Its
inverse has `g^{00} = 1` and `g^{11} = 1 / (1 + x₀²)`. The only nonzero
derivative entry is `∂_0 g_{11} = 2 x₀`. -/
noncomputable def warpedDiag2 : MetricData 2 where
  g := fun x μ ν =>
    if μ = 0 ∧ ν = 0 then 1
    else if μ = 1 ∧ ν = 1 then 1 + (x 0)^2
    else 0
  ginv := fun x μ ν =>
    if μ = 0 ∧ ν = 0 then 1
    else if μ = 1 ∧ ν = 1 then 1 / (1 + (x 0)^2)
    else 0
  dg := fun l x μ ν =>
    if l = 0 ∧ μ = 1 ∧ ν = 1 then 2 * x 0 else 0
  g_symm := by
    intros x μ ν
    fin_cases μ <;> fin_cases ν <;> simp
  ginv_symm := by
    intros x μ ν
    fin_cases μ <;> fin_cases ν <;> simp
  ginv_mul := by
    intros x μ ν
    have h_pos : (0 : ℝ) < 1 + (x 0)^2 := by
      have : 0 ≤ (x 0)^2 := sq_nonneg _
      linarith
    have h_ne : (1 : ℝ) + (x 0)^2 ≠ 0 := ne_of_gt h_pos
    fin_cases μ <;> fin_cases ν <;>
      simp [Fin.sum_univ_two, one_div, inv_mul_cancel₀ h_ne]
  dg_symm := by
    intros l x μ ν
    fin_cases l <;> fin_cases μ <;> fin_cases ν <;> simp

/-- For `warpedDiag2`, `Γ¹_{01}(x) = x₀ / (1 + x₀²)`. -/
theorem warpedDiag2_christoffel_1_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 0 1 = x 0 / (1 + (x 0)^2) := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  have h_pos : (0 : ℝ) < 1 + (x 0)^2 := by
    have : 0 ≤ (x 0)^2 := sq_nonneg _
    linarith
  have h_ne : (1 : ℝ) + (x 0)^2 ≠ 0 := ne_of_gt h_pos
  simp
  field_simp

/-- For `warpedDiag2`, `Γ⁰_{11}(x) = −x₀`. -/
theorem warpedDiag2_christoffel_0_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 1 1 = -(x 0) := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- For `warpedDiag2`, `Γ¹_{01}(x) ≠ 0` whenever `x 0 ≠ 0`. -/
theorem warpedDiag2_christoffel_nonzero (x : Fin 2 → ℝ)
    (hx : x 0 ≠ 0) :
    warpedDiag2.christoffel x 1 0 1 ≠ 0 := by
  rw [warpedDiag2_christoffel_1_0_1]
  have h_pos : (0 : ℝ) < 1 + (x 0)^2 := by
    have : 0 ≤ (x 0)^2 := sq_nonneg _
    linarith
  have h_ne : (1 : ℝ) + (x 0)^2 ≠ 0 := ne_of_gt h_pos
  exact div_ne_zero hx h_ne

/-- There exist a 2-D `MetricData`, a point and indices at which a
Christoffel symbol is nonzero. The witness is `warpedDiag2` at
`x = (1, 0)` with `Γ¹_{01}`. The statement does not mention Ricci
curvature or a graph. -/
theorem curvedRicciBridgeObligation :
    ∃ (M : MetricData 2) (x : Fin 2 → ℝ) (μ ν ρ : Fin 2),
      M.christoffel x ρ μ ν ≠ 0 := by
  refine ⟨warpedDiag2, fun i => if i = 0 then 1 else 0, 0, 1, 1, ?_⟩
  have hx0_ne : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) 0 ≠ 0 := by
    simp
  exact warpedDiag2_christoffel_nonzero _ hx0_ne

/-- On a `Neighbourhood` in which every vertex has degree 3,
`formanRicciEdge N v w = −2` for all `v` and `w`. -/
theorem threeRegular_formanRicci_nonzero {V : Type*} [Fintype V] [DecidableEq V]
    (N : Neighbourhood V) (h3reg : ∀ v : V, N.degree v = 3) (v w : V) :
    formanRicciEdge N v w = -2 := by
  have h : formanRicciEdge N v w = 4 - 2 * (3 : ℤ) :=
    formanRicciEdge_regular N 3 h3reg v w
  rw [h]; ring

end InfraFormalization
