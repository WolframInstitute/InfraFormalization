/-
Einstein field equations with cosmological constant in four dimensions.

`EinsteinEqLambda M C Λ κ T x` states `G_{μν}(x) + Λ · g_{μν}(x) = κ · T_{μν}`
for all `μ, ν`, where `G_{μν} = R_{μν} − ½ R g_{μν}` is the Einstein tensor of
the connection `C` and metric `M`, and `κ` is a real parameter. The module
proves that the Minkowski metric with the flat connection satisfies the
equation with `Λ = 0` and `T = 0`, and that it satisfies the vacuum equation
only for `Λ = 0`. No hypergraph appears in this module.
-/

import InfraFormalization.CurvatureRiemann
import InfraFormalization.StressEnergyTensor
import InfraFormalization.LorentzianManifold

namespace InfraFormalization

open Curvature

/-- For every `μ, ν : Fin 4`,
`C.einsteinTensor M x μ ν + Λ · M.g x μ ν = κ · T.T μ ν`. The tensor `T` is a
constant `Fin 4 → Fin 4 → ℝ` array and does not depend on `x`. -/
def EinsteinEqLambda (M : MetricData 4) (C : ConnectionData 4)
    (Λ κ : ℝ) (T : StressEnergyTensor) (x : Fin 4 → ℝ) : Prop :=
  ∀ μ ν : Fin 4,
    C.einsteinTensor M x μ ν + Λ * M.g x μ ν = κ * T.T μ ν

/-- The Minkowski metric `minkowski4` with the flat connection satisfies
`EinsteinEqLambda` with `Λ = 0` and `T = 0` at every point, for every `κ`. -/
theorem minkowski4_satisfies_EFE_zero_lambda (κ : ℝ) (x : Fin 4 → ℝ) :
    EinsteinEqLambda minkowski4 (flatConnection 4) 0 κ
      StressEnergyTensor.zero x := by
  intro μ ν
  unfold ConnectionData.einsteinTensor
  rw [flatConnection_ricci_zero, flatConnection_scalar_zero]
  unfold StressEnergyTensor.zero
  simp

/-- With `T = 0`, `EinsteinEqLambda` is equivalent to
`G_{μν} + Λ · g_{μν} = 0` for all `μ, ν`. -/
theorem einsteinEqLambda_vacuum_iff (M : MetricData 4) (C : ConnectionData 4)
    (Λ κ : ℝ) (x : Fin 4 → ℝ) :
    EinsteinEqLambda M C Λ κ StressEnergyTensor.zero x ↔
      ∀ μ ν : Fin 4,
        C.einsteinTensor M x μ ν + Λ * M.g x μ ν = 0 := by
  unfold EinsteinEqLambda StressEnergyTensor.zero
  refine ⟨?_, ?_⟩
  · intro h μ ν; have := h μ ν; simp at this; exact this
  · intro h μ ν; rw [h μ ν]; simp

/-- If `minkowski4` with the flat connection satisfies `EinsteinEqLambda`
with `T = 0` at a point `x`, then `Λ = 0`. The proof uses the `(1, 1)`
component, where the Einstein tensor is 0 and `g₁₁ = 1`. -/
theorem minkowski4_flat_vacuum_forces_lambda_zero
    (Λ κ : ℝ) (x : Fin 4 → ℝ)
    (h : EinsteinEqLambda minkowski4 (flatConnection 4) Λ κ
           StressEnergyTensor.zero x) :
    Λ = 0 := by
  -- At μ = ν = 1, minkowski4.g x 1 1 = 1 (spatial component).
  have h11 := h 1 1
  unfold ConnectionData.einsteinTensor at h11
  rw [flatConnection_ricci_zero, flatConnection_scalar_zero] at h11
  unfold StressEnergyTensor.zero minkowski4 at h11
  simp at h11
  exact h11

/-- The metric of `minkowski4Manifold` with the flat connection satisfies
`EinsteinEqLambda` with `Λ = 0` and `T = 0` at every point. The proof is
`minkowski4_satisfies_EFE_zero_lambda`. -/
theorem minkowski4Manifold_satisfies_vacuum_EFE (κ : ℝ) (x : Fin 4 → ℝ) :
    EinsteinEqLambda minkowski4Manifold.toMetric
      (flatConnection 4) 0 κ StressEnergyTensor.zero x :=
  minkowski4_satisfies_EFE_zero_lambda κ x

end InfraFormalization
