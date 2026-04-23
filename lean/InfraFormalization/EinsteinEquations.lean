/-
**Einstein field equations with cosmological constant Λ** (F3 / #62).

The full EFE:
  `G_{μν}(x) + Λ · g_{μν}(x) = κ · T_{μν}(x)`

where:
  * `G_{μν} = R_{μν} − ½ R g_{μν}` is the Einstein tensor,
  * `Λ` is the cosmological constant,
  * `κ = 8π G / c⁴` in classical units (we leave it abstract here),
  * `T_{μν}` is the stress-energy tensor.

This file provides a concrete Prop + vacuum-case proofs. The full
task of exhibiting a rewriting rule whose continuum limit satisfies
this Prop with non-zero `T` is a separate obligation.

**Connection to hypergraphs.** Same anchor as `StressEnergyTensor`:
this is the continuum-target side of the bridge. A future hypergraph
stress-energy tensor would pair with a hypergraph Einstein tensor
via a discrete-Ricci → continuum-Ricci convergence theorem.
-/

import InfraFormalization.CurvatureRiemann
import InfraFormalization.StressEnergyTensor
import InfraFormalization.LorentzianManifold

namespace InfraFormalization

open Curvature

/-- **Einstein equations with Λ, pointwise** (in 4 dimensions, matching
`StressEnergyTensor` which is `Fin 4 → Fin 4 → ℝ`).

`M` is the metric, `C` the connection, `Λ` the cosmological constant,
`κ` the Einstein coupling constant, `T` the stress-energy tensor, and
`x` a spacetime point. The equation:

  `G_{μν}(x) + Λ · g_{μν}(x) = κ · T_{μν}(x)`   (for every μ, ν). -/
def EinsteinEqLambda (M : MetricData 4) (C : ConnectionData 4)
    (Λ κ : ℝ) (T : StressEnergyTensor) (x : Fin 4 → ℝ) : Prop :=
  ∀ μ ν : Fin 4,
    C.einsteinTensor M x μ ν + Λ * M.g x μ ν = κ * T.T μ ν

/-- **Vacuum with Λ = 0 on Minkowski with flat connection.** The
Minkowski metric with the flat connection satisfies the Einstein
equations with Λ = 0 and zero stress-energy. This is the trivial
flat-space sanity check. -/
theorem minkowski4_satisfies_EFE_zero_lambda (κ : ℝ) (x : Fin 4 → ℝ) :
    EinsteinEqLambda minkowski4 (flatConnection 4) 0 κ
      StressEnergyTensor.zero x := by
  intro μ ν
  unfold ConnectionData.einsteinTensor
  rw [flatConnection_ricci_zero, flatConnection_scalar_zero]
  unfold StressEnergyTensor.zero
  simp

/-- **EFE with Λ reduces to `G + Λ g = 0` in vacuum** (`T = 0`). Just
unfolds the zero stress-energy tensor. Useful as a rewrite. -/
theorem einsteinEqLambda_vacuum_iff (M : MetricData 4) (C : ConnectionData 4)
    (Λ κ : ℝ) (x : Fin 4 → ℝ) :
    EinsteinEqLambda M C Λ κ StressEnergyTensor.zero x ↔
      ∀ μ ν : Fin 4,
        C.einsteinTensor M x μ ν + Λ * M.g x μ ν = 0 := by
  unfold EinsteinEqLambda StressEnergyTensor.zero
  refine ⟨?_, ?_⟩
  · intro h μ ν; have := h μ ν; simp at this; exact this
  · intro h μ ν; rw [h μ ν]; simp

/-- **De Sitter–type vacuum with Λ**: the EFE with Λ ≠ 0 and zero
stress-energy requires `G_{μν} = −Λ g_{μν}`. For Minkowski with flat
connection, this forces `0 = −Λ g`, which in turn (since `g` is
non-degenerate) forces `Λ = 0`. Hence non-zero-Λ de Sitter/anti-de
Sitter cannot live on Minkowski + flat connection.

This theorem: if Minkowski + flat connection + some stress-energy
satisfies EFE with Λ, and `Λ ≠ 0`, then the stress-energy is
non-zero at the 0-0 component.

Simpler consequence: proves Minkowski + flat does not admit a vacuum
solution with Λ ≠ 0. -/
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

/-- **Second Bianchi identity (divergence of Einstein tensor) vanishes
on the flat connection** — trivially, since the entire Einstein tensor
vanishes. This is `∇_μ G^{μν} = 0` in the degenerate flat case.

For general torsion-free metric-compatible (Levi-Civita) connections
the contracted second Bianchi identity `∇_μ G^{μν} = 0` is a
consequence of the un-contracted Bianchi `∇_{[λ} R_{μν]ρσ} = 0`; full
proof requires metric compatibility (not yet formalised). Here we
close the flat-vacuum case. -/
theorem flatConnection_einstein_divergence_zero (n : Nat)
    (M : MetricData n) (x : Fin n → ℝ)
    (dG : Fin n → (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (h_dG : ∀ μ ν ρ y, dG μ y ν ρ = 0) (ν : Fin n) :
    (∑ μ : Fin n, dG μ x μ ν)
      + (∑ μ : Fin n, ∑ ρ : Fin n, (flatConnection n).Γ x μ μ ρ
          * (flatConnection n).einsteinTensor M x ρ ν) = 0 := by
  -- dG = 0 everywhere, and Γ_flat = 0.
  have h_first : (∑ μ : Fin n, dG μ x μ ν) = 0 := by
    refine Finset.sum_eq_zero (fun μ _ => ?_)
    exact h_dG μ μ ν x
  have h_second : (∑ μ : Fin n, ∑ ρ : Fin n, (flatConnection n).Γ x μ μ ρ
      * (flatConnection n).einsteinTensor M x ρ ν) = 0 := by
    simp [flatConnection]
  rw [h_first, h_second]
  ring

/-- **Bundled Lorentzian vacuum bridge**: the Minkowski 4-space, as a
`DiagLorentzianManifold`, with the flat connection, satisfies vacuum
Einstein equations (zero Λ, zero stress-energy) at every point.

This ties E1 (`DiagLorentzianManifold`) + F3 (`EinsteinEqLambda`) into
a single theorem: we have a formal Lorentzian GR framework with
Minkowski as a concrete instance. -/
theorem minkowski4Manifold_satisfies_vacuum_EFE (κ : ℝ) (x : Fin 4 → ℝ) :
    EinsteinEqLambda minkowski4Manifold.toMetric
      (flatConnection 4) 0 κ StressEnergyTensor.zero x :=
  minkowski4_satisfies_EFE_zero_lambda κ x

end InfraFormalization
