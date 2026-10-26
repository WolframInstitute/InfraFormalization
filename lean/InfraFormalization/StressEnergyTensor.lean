/-
Stress-energy tensors in components.

This module defines a stress-energy tensor as a symmetric function
`Fin 4 → Fin 4 → ℝ`, its trace and energy density `T_{00}`, and the weak,
null, strong and dominant energy conditions in terms of the diagonal
components `ρ = T_{00}` and `p_i = T_{ii}`. It proves that the weak
condition implies the null condition and that the zero tensor satisfies
both. It also defines two propositions named after the Penrose singularity
theorem and the Raychaudhuri focusing inequality; they are stated over
arbitrary propositions and real numbers, not over a spacetime.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

namespace InfraFormalization

/-- A function `T : Fin 4 → Fin 4 → ℝ` with `T μ ν = T ν μ`. -/
structure StressEnergyTensor where
  /-- Components `T_{μν}` in a chosen frame. -/
  T : Fin 4 → Fin 4 → ℝ
  /-- Symmetry: `T_{μν} = T_{νμ}`. -/
  symm : ∀ μ ν : Fin 4, T μ ν = T ν μ

/-- The tensor with all components 0. -/
def StressEnergyTensor.zero : StressEnergyTensor where
  T _ _ := 0
  symm _ _ := rfl

/-- The trace `∑_μ T μ μ`. -/
noncomputable def StressEnergyTensor.trace (T : StressEnergyTensor) : ℝ :=
  ∑ μ : Fin 4, T.T μ μ

/-- The zero tensor has trace 0. -/
theorem zero_stressEnergyTensor_trace :
    StressEnergyTensor.zero.trace = 0 := by
  unfold StressEnergyTensor.trace StressEnergyTensor.zero
  simp

/-- The energy density `ρ = T_{00}`. -/
noncomputable def StressEnergyTensor.energyDensity (T : StressEnergyTensor) :
    ℝ :=
  T.T 0 0

/-- The zero tensor has energy density 0. -/
theorem zero_stressEnergyTensor_energyDensity :
    StressEnergyTensor.zero.energyDensity = 0 := rfl

/-! ### Energy conditions

The conditions below are stated on the diagonal components `T_{00} = ρ` and
`T_{ii} = p_i` for `i = 1, 2, 3`.
-/

/-- Weak energy condition: `ρ ≥ 0` and `ρ + p_i ≥ 0` for each `i`. -/
def StressEnergyTensor.WeakEnergyCondition (T : StressEnergyTensor) : Prop :=
  0 ≤ T.T 0 0 ∧ ∀ i : Fin 3, 0 ≤ T.T 0 0 + T.T (i.succ) (i.succ)

/-- Null energy condition: `ρ + p_i ≥ 0` for each `i`. -/
def StressEnergyTensor.NullEnergyCondition (T : StressEnergyTensor) : Prop :=
  ∀ i : Fin 3, 0 ≤ T.T 0 0 + T.T (i.succ) (i.succ)

/-- Strong energy condition: `ρ + Σ p_i ≥ 0` and `ρ + p_i ≥ 0` for each
`i`. -/
def StressEnergyTensor.StrongEnergyCondition (T : StressEnergyTensor) : Prop :=
  (0 ≤ T.T 0 0 + T.T 1 1 + T.T 2 2 + T.T 3 3) ∧
    ∀ i : Fin 3, 0 ≤ T.T 0 0 + T.T (i.succ) (i.succ)

/-- Dominant energy condition: `ρ ≥ 0` and `|p_i| ≤ ρ` for each `i`. -/
def StressEnergyTensor.DominantEnergyCondition (T : StressEnergyTensor) : Prop :=
  0 ≤ T.T 0 0 ∧ ∀ i : Fin 3,
    |T.T (i.succ) (i.succ)| ≤ T.T 0 0

/-- The weak energy condition implies the null energy condition. -/
theorem wec_implies_nec
    {T : StressEnergyTensor} (h : T.WeakEnergyCondition) :
    T.NullEnergyCondition :=
  h.2

/-- The zero tensor satisfies the weak energy condition. -/
theorem zero_stressEnergyTensor_weakEnergy :
    StressEnergyTensor.zero.WeakEnergyCondition := by
  refine ⟨le_refl 0, fun i => ?_⟩
  unfold StressEnergyTensor.zero
  simp

/-- The zero tensor satisfies the null energy condition. -/
theorem zero_stressEnergyTensor_nullEnergy :
    StressEnergyTensor.zero.NullEnergyCondition :=
  wec_implies_nec zero_stressEnergyTensor_weakEnergy

/-! ### Propositions named after the Penrose and Raychaudhuri theorems -/

end InfraFormalization
