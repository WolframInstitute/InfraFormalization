/-
Forman-Ricci curvature on 2-regular graphs and the Ricci tensor of the flat
connection in one dimension.

This module defines `circleMetric`, the constant metric `g₀₀ = 1` on one
coordinate, and proves that the Ricci tensor and scalar curvature of the
flat connection `flatConnection 1` are 0, that the Forman-Ricci curvature
of every edge of a 2-regular neighbourhood structure on `Fin n` is 0, and
that the two values are equal because both are 0.
-/

import InfraFormalization.DiscreteRicci
import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann

namespace InfraFormalization

/-- The metric data on one coordinate with `g₀₀ = 1`, `g^{00} = 1` and all
partial derivatives 0. -/
noncomputable def circleMetric : Curvature.MetricData 1 where
  g := fun _ _ _ => 1
  ginv := fun _ _ _ => 1
  dg := fun _ _ _ _ => 0
  g_symm := by intros; rfl
  ginv_symm := by intros; rfl
  ginv_mul := by
    intros x μ ν
    -- `Fin 1` has one element, so μ = ν and the sum has one summand.
    have hμν : μ = ν := Subsingleton.elim μ ν
    rw [Finset.sum_const, Finset.card_univ]
    have : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    rw [this]
    simp [hμν]
  dg_symm := by intros; rfl

/-- The Ricci tensor of `flatConnection 1` is 0. The statement does not
involve `circleMetric`. -/
theorem flatConnection_one_ricci_zero (x : Fin 1 → ℝ) (σ ν : Fin 1) :
    (Curvature.flatConnection 1).ricci x σ ν = 0 :=
  Curvature.flatConnection_ricci_zero 1 x σ ν

/-- The scalar curvature of `flatConnection 1` with respect to
`circleMetric` is 0. -/
theorem circle_scalar_zero (x : Fin 1 → ℝ) :
    Curvature.ConnectionData.scalarCurvature circleMetric
      (Curvature.flatConnection 1) x = 0 :=
  Curvature.flatConnection_scalar_zero circleMetric x

/-- If every vertex of a neighbourhood structure on `Fin n` has degree 2,
the Forman-Ricci curvature of every pair `v`, `w` is 0. -/
theorem cycleForman_zero {n : Nat} (N : Neighbourhood (Fin n))
    (h2reg : ∀ v : Fin n, N.degree v = 2) (v w : Fin n) :
    formanRicciEdge N v w = 0 :=
  formanRicciEdge_zero_of_two_regular N h2reg v w

/-- For a 2-regular neighbourhood structure on `Fin n`, the Forman-Ricci
curvature of every pair is 0 and the Ricci tensor of `flatConnection 1` is
0. -/
theorem cycle_forman_and_flat_ricci_zero
    {n : Nat} (N : Neighbourhood (Fin n))
    (h2reg : ∀ v : Fin n, N.degree v = 2)
    (v w : Fin n) (x : Fin 1 → ℝ) (σ ν : Fin 1) :
    (formanRicciEdge N v w : ℤ) = 0
    ∧ (Curvature.flatConnection 1).ricci x σ ν = 0 := by
  refine ⟨?_, ?_⟩
  · exact cycleForman_zero N h2reg v w
  · exact flatConnection_one_ricci_zero x σ ν

/-- For a 2-regular neighbourhood structure on `Fin n`, the Forman-Ricci
curvature of every pair, cast to ℝ, equals the Ricci tensor of
`flatConnection 1`; both are 0. -/
theorem cycle_forman_and_flat_ricci_zero_real
    {n : Nat} (N : Neighbourhood (Fin n))
    (h2reg : ∀ v : Fin n, N.degree v = 2)
    (v w : Fin n) (x : Fin 1 → ℝ) (σ ν : Fin 1) :
    ((formanRicciEdge N v w : ℤ) : ℝ)
    = (Curvature.flatConnection 1).ricci x σ ν := by
  rw [cycleForman_zero N h2reg v w, flatConnection_one_ricci_zero x σ ν]
  simp

end InfraFormalization
