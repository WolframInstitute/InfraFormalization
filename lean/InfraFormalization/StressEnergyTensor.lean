/-
**Stress-energy tensor type** (F1 / #60).

A stress-energy tensor `T_μν` on a 4-dim spacetime is a symmetric
rank-2 tensor encoding matter/field energy, momentum, and stress
densities. Here we give the minimal type definition, with symmetry
as a field.

**Connection to hypergraphs.** Future: a stress-energy tensor on
the causal-graph side will encode matter injection rates per event,
with the continuum limit being the classical `T_μν`. For now we
provide the continuum type.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

namespace InfraFormalization

/-- **Stress-energy tensor on a 4D tangent space.** A symmetric
rank-2 covariant tensor `T : Fin 4 → Fin 4 → ℝ`. The symmetry
condition `T μ ν = T ν μ` is carried as a field. -/
structure StressEnergyTensor where
  /-- Components `T_{μν}` in a chosen frame. -/
  T : Fin 4 → Fin 4 → ℝ
  /-- Symmetry: `T_{μν} = T_{νμ}`. -/
  symm : ∀ μ ν : Fin 4, T μ ν = T ν μ

/-- **Zero stress-energy tensor** (vacuum). -/
def StressEnergyTensor.zero : StressEnergyTensor where
  T _ _ := 0
  symm _ _ := rfl

/-- **Scalar trace** `Tr(T) = ∑_μ T μ μ`. -/
noncomputable def StressEnergyTensor.trace (T : StressEnergyTensor) : ℝ :=
  ∑ μ : Fin 4, T.T μ μ

/-- **Zero tensor has zero trace**. -/
theorem zero_stressEnergyTensor_trace :
    StressEnergyTensor.zero.trace = 0 := by
  unfold StressEnergyTensor.trace StressEnergyTensor.zero
  simp

/-- **Energy density** `ρ = T_{00}` in a chosen frame (the 0-th index
is the time direction). -/
noncomputable def StressEnergyTensor.energyDensity (T : StressEnergyTensor) :
    ℝ :=
  T.T 0 0

/-- **The zero tensor has zero energy density**. -/
theorem zero_stressEnergyTensor_energyDensity :
    StressEnergyTensor.zero.energyDensity = 0 := rfl

end InfraFormalization
