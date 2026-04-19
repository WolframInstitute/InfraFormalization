/-
Riemann curvature tensor, Ricci tensor, scalar curvature, Einstein
tensor — all in local coordinates.

**Continuation of Rung 5.** `CurvatureLocalCoord.lean` formalised
Christoffel symbols. Here we add the Riemann tensor (which needs
first partial derivatives of Γ, as data), Ricci (a contraction of
Riemann), scalar curvature (Ricci traced against the inverse metric),
and Einstein tensor `G_{μν} = R_{μν} − ½ R g_{μν}`.

**Representation.** A `ConnectionData n` carries connection
coefficients `Γ^ρ_{μν}(x)` and their first partial derivatives
`∂_λ Γ^ρ_{μν}(x)` as user-supplied data, plus the lower-index
symmetry of Γ. (We do not require Γ to be derived from a metric —
this is the Riemann-tensor-as-formula viewpoint.)

When a `MetricData` is also supplied, contractions to Ricci and scalar
become available.

**Sanity check.** The `flat` instance has `Γ ≡ 0, ∂Γ ≡ 0`; we prove
`riemann ≡ 0`, `ricci ≡ 0`, `scalarCurvature ≡ 0`. This is the
flat-space check — no curvature when Christoffel symbols vanish.
-/

import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- **Connection-with-derivatives data.** -/
structure ConnectionData (n : Nat) where
  /-- `Γ^ρ_{μν}(x)`. -/
  Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ
  /-- `∂_l Γ^ρ_{μν}(x)`. -/
  dΓ : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ
  /-- Lower-index symmetry of Γ. -/
  Γ_symm : ∀ x ρ μ ν, Γ x ρ μ ν = Γ x ρ ν μ

namespace ConnectionData

variable {n : Nat} (C : ConnectionData n)

/-- **Riemann curvature tensor (mixed indices).**

  `R^ρ_{σμν}(x) = ∂_μ Γ^ρ_{νσ}(x) − ∂_ν Γ^ρ_{μσ}(x)
                 + Σ_λ Γ^ρ_{μλ}(x) Γ^λ_{νσ}(x)
                 − Σ_λ Γ^ρ_{νλ}(x) Γ^λ_{μσ}(x)`.
-/
def riemann (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  C.dΓ μ x ρ ν σ - C.dΓ ν x ρ μ σ
    + (∑ l : Fin n, C.Γ x ρ μ l * C.Γ x l ν σ)
    - (∑ l : Fin n, C.Γ x ρ ν l * C.Γ x l μ σ)

/-- **Antisymmetry of Riemann in the last two indices.** `R^ρ_{σμν} = −R^ρ_{σνμ}`. -/
theorem riemann_antisymm (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.riemann x ρ σ μ ν = - C.riemann x ρ σ ν μ := by
  unfold riemann
  ring

/-- **Ricci tensor.** Contraction of Riemann over the first upper and
second lower index: `R_{σν}(x) = Σ_ρ R^ρ_{σρν}(x)`. -/
def ricci (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ : Fin n, C.riemann x ρ σ ρ ν

/-- **Scalar curvature.** Trace of Ricci against the inverse metric:
`R(x) = Σ_{σν} g^{σν}(x) R_{σν}(x)`.

This requires a metric. We provide the formula here against an
externally-supplied `MetricData`; the type system enforces that the
metric and connection share the same dimension `n`. -/
def scalarCurvature {n : Nat} (M : MetricData n) (C : ConnectionData n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ : Fin n, ∑ ν : Fin n, M.ginv x σ ν * C.ricci x σ ν

/-- **Einstein tensor.** `G_{μν}(x) = R_{μν}(x) − ½ R(x) g_{μν}(x)`. -/
noncomputable def einsteinTensor {n : Nat} (M : MetricData n)
    (C : ConnectionData n) (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  C.ricci x μ ν - (1 / 2) * scalarCurvature M C x * M.g x μ ν

end ConnectionData

/-- **Flat connection** on `ℝⁿ`: `Γ ≡ 0, ∂Γ ≡ 0`. -/
def flatConnection (n : Nat) : ConnectionData n where
  Γ := fun _ _ _ _ => 0
  dΓ := fun _ _ _ _ _ => 0
  Γ_symm := by intros; rfl

/-- For the flat connection, the Riemann tensor vanishes identically. -/
theorem flatConnection_riemann_zero (n : Nat)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    (flatConnection n).riemann x ρ σ μ ν = 0 := by
  unfold ConnectionData.riemann flatConnection
  simp

/-- For the flat connection, the Ricci tensor vanishes identically. -/
theorem flatConnection_ricci_zero (n : Nat) (x : Fin n → ℝ) (σ ν : Fin n) :
    (flatConnection n).ricci x σ ν = 0 := by
  unfold ConnectionData.ricci
  apply Finset.sum_eq_zero
  intros ρ _
  exact flatConnection_riemann_zero n x ρ σ ρ ν

/-- For the flat connection, the scalar curvature vanishes (against
any metric). -/
theorem flatConnection_scalar_zero {n : Nat} (M : MetricData n)
    (x : Fin n → ℝ) :
    ConnectionData.scalarCurvature M (flatConnection n) x = 0 := by
  unfold ConnectionData.scalarCurvature
  apply Finset.sum_eq_zero
  intros σ _
  apply Finset.sum_eq_zero
  intros ν _
  rw [flatConnection_ricci_zero]
  ring

/-- For the flat connection, the Einstein tensor vanishes. -/
theorem flatConnection_einstein_zero {n : Nat} (M : MetricData n)
    (x : Fin n → ℝ) (μ ν : Fin n) :
    ConnectionData.einsteinTensor M (flatConnection n) x μ ν = 0 := by
  unfold ConnectionData.einsteinTensor
  rw [flatConnection_ricci_zero, flatConnection_scalar_zero]
  ring

/-- **Vacuum Einstein equation.** `G_{μν} = 0` on Minkowski with the
flat connection. This is the trivial flat-space sanity check that the
formalism is set up correctly. -/
theorem minkowski4_satisfies_vacuum_EFE
    (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    ConnectionData.einsteinTensor minkowski4 (flatConnection 4) x μ ν = 0 :=
  flatConnection_einstein_zero minkowski4 x μ ν

end Curvature
end InfraFormalization
