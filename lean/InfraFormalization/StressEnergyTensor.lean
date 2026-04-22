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

/-! ### Energy conditions (F2 / #61)

In a coordinate frame where `T_{00} = ρ` is the energy density and
`T_{ii} = p_i` (for `i = 1, 2, 3`) are the principal pressures, the
four classical energy conditions are algebraic conditions on these
components. We give them here at the component level.
-/

/-- **Weak energy condition (WEC)**: energy density is non-negative and
every principal-pressure sum `ρ + p_i` is non-negative. WEC states
that every observer's measured energy density is non-negative. -/
def StressEnergyTensor.WeakEnergyCondition (T : StressEnergyTensor) : Prop :=
  0 ≤ T.T 0 0 ∧ ∀ i : Fin 3, 0 ≤ T.T 0 0 + T.T (i.succ) (i.succ)

/-- **Null energy condition (NEC)**: `ρ + p_i ≥ 0` for every
principal direction. Weakest of the energy conditions; implied by
WEC. -/
def StressEnergyTensor.NullEnergyCondition (T : StressEnergyTensor) : Prop :=
  ∀ i : Fin 3, 0 ≤ T.T 0 0 + T.T (i.succ) (i.succ)

/-- **Strong energy condition (SEC)**: every observer sees gravity
as attractive. Component form: `ρ + Σ p_i ≥ 0` AND `ρ + p_i ≥ 0` for
each i. -/
def StressEnergyTensor.StrongEnergyCondition (T : StressEnergyTensor) : Prop :=
  (0 ≤ T.T 0 0 + T.T 1 1 + T.T 2 2 + T.T 3 3) ∧
    ∀ i : Fin 3, 0 ≤ T.T 0 0 + T.T (i.succ) (i.succ)

/-- **Dominant energy condition (DEC)**: energy density dominates
every pressure. Component form: `ρ ≥ 0` AND `ρ ≥ |p_i|` for each i.
Equivalently: energy-flux is timelike or null for every observer. -/
def StressEnergyTensor.DominantEnergyCondition (T : StressEnergyTensor) : Prop :=
  0 ≤ T.T 0 0 ∧ ∀ i : Fin 3,
    |T.T (i.succ) (i.succ)| ≤ T.T 0 0

/-- **WEC ⇒ NEC** (WEC is strictly stronger than NEC). -/
theorem wec_implies_nec
    {T : StressEnergyTensor} (h : T.WeakEnergyCondition) :
    T.NullEnergyCondition :=
  h.2

/-- **The zero tensor satisfies every energy condition trivially**. -/
theorem zero_stressEnergyTensor_weakEnergy :
    StressEnergyTensor.zero.WeakEnergyCondition := by
  refine ⟨le_refl 0, fun i => ?_⟩
  unfold StressEnergyTensor.zero
  simp

/-- **The zero tensor satisfies NEC**. -/
theorem zero_stressEnergyTensor_nullEnergy :
    StressEnergyTensor.zero.NullEnergyCondition :=
  wec_implies_nec zero_stressEnergyTensor_weakEnergy

end InfraFormalization
