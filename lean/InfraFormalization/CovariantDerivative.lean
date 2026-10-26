/-
Covariant derivative formulas for `ConnectionData`.

For a `ConnectionData n` with Christoffel symbols `Γ`, this module
defines pointwise the expressions `∂_μ φ`, `∂_μ V^ν + Γ^ν_{μρ} V^ρ` and
`∂_μ ω_ν − Γ^ρ_{μν} ω_ρ`, where the partial derivatives are supplied as
separate functions and are not required to be derivatives of the
fields. It proves that the vector and covector expressions reduce to
the supplied partial derivative for `flatConnection n`, and that all
three are additive. The Leibniz rule, the commutator identity with the
Riemann tensor, and metric compatibility are not stated.
-/

import InfraFormalization.CurvatureRiemann

namespace InfraFormalization
namespace Curvature
namespace ConnectionData

variable {n : Nat} (C : ConnectionData n)

/-- The scalar covariant derivative `∇_μ φ(x)`, defined as `dφ μ x`,
where `dφ` is a supplied family of partial derivatives. -/
def nabla_scalar (dφ : Fin n → (Fin n → ℝ) → ℝ)
    (μ : Fin n) (x : Fin n → ℝ) : ℝ :=
  dφ μ x

/-- The vector covariant derivative
`∇_μ V^ν(x) = dV μ x ν + ∑_ρ Γ^ν_{μρ}(x) · V^ρ(x)`, where `dV` is a
supplied family of partial derivatives. -/
def nabla_vector (V : (Fin n → ℝ) → Fin n → ℝ)
    (dV : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  dV μ x ν + ∑ ρ : Fin n, C.Γ x ν μ ρ * V x ρ

/-- The covector covariant derivative
`∇_μ ω_ν(x) = dω μ x ν − ∑_ρ Γ^ρ_{μν}(x) · ω_ρ(x)`, where `dω` is a
supplied family of partial derivatives. -/
def nabla_covector (ω : (Fin n → ℝ) → Fin n → ℝ)
    (dω : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  dω μ x ν - ∑ ρ : Fin n, C.Γ x ρ μ ν * ω x ρ

/-- For `flatConnection n`, whose `Γ` is zero, the vector covariant
derivative equals `dV μ x ν`. -/
theorem nabla_vector_flat (n : Nat)
    (V : (Fin n → ℝ) → Fin n → ℝ)
    (dV : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) :
    (flatConnection n).nabla_vector V dV μ ν x = dV μ x ν := by
  unfold nabla_vector
  simp [flatConnection]

/-- For `flatConnection n`, the covector covariant derivative equals
`dω μ x ν`. -/
theorem nabla_covector_flat (n : Nat)
    (ω : (Fin n → ℝ) → Fin n → ℝ)
    (dω : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) :
    (flatConnection n).nabla_covector ω dω μ ν x = dω μ x ν := by
  unfold nabla_covector
  simp [flatConnection]

/-- The scalar covariant derivative is additive in the supplied
partial derivatives. -/
theorem nabla_scalar_add (n : Nat) (dφ dψ : Fin n → (Fin n → ℝ) → ℝ)
    (μ : Fin n) (x : Fin n → ℝ) :
    nabla_scalar (fun μ x => dφ μ x + dψ μ x) μ x
      = nabla_scalar dφ μ x + nabla_scalar dψ μ x := by
  unfold nabla_scalar
  rfl

/-- The vector covariant derivative is additive:
`∇_μ (V + W)^ν = ∇_μ V^ν + ∇_μ W^ν` at each point, with partial
derivatives `dV + dW`. -/
theorem nabla_vector_add (V W : (Fin n → ℝ) → Fin n → ℝ)
    (dV dW : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) :
    C.nabla_vector (fun x ρ => V x ρ + W x ρ)
      (fun μ x ν => dV μ x ν + dW μ x ν) μ ν x
      = C.nabla_vector V dV μ ν x + C.nabla_vector W dW μ ν x := by
  unfold nabla_vector
  rw [show (∑ ρ : Fin n, C.Γ x ν μ ρ * (V x ρ + W x ρ))
        = (∑ ρ : Fin n, C.Γ x ν μ ρ * V x ρ)
          + (∑ ρ : Fin n, C.Γ x ν μ ρ * W x ρ) from by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros ρ _
      ring]
  ring

/-- The covector covariant derivative is additive:
`∇_μ (ω + η)_ν = ∇_μ ω_ν + ∇_μ η_ν` at each point, with partial
derivatives `dω + dη`. -/
theorem nabla_covector_add (ω η : (Fin n → ℝ) → Fin n → ℝ)
    (dω dη : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) :
    C.nabla_covector (fun x ρ => ω x ρ + η x ρ)
      (fun μ x ν => dω μ x ν + dη μ x ν) μ ν x
      = C.nabla_covector ω dω μ ν x + C.nabla_covector η dη μ ν x := by
  unfold nabla_covector
  rw [show (∑ ρ : Fin n, C.Γ x ρ μ ν * (ω x ρ + η x ρ))
        = (∑ ρ : Fin n, C.Γ x ρ μ ν * ω x ρ)
          + (∑ ρ : Fin n, C.Γ x ρ μ ν * η x ρ) from by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros ρ _
      ring]
  ring

end ConnectionData
end Curvature
end InfraFormalization
