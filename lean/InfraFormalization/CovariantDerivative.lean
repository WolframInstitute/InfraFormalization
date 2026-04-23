/-
**Covariant derivative on `ConnectionData`** (X2 / #31).

Given a `ConnectionData n` carrying Christoffel symbols `Γ`, the
covariant derivative `∇_μ` acts on tensor fields as:

  * scalar field `φ(x)`:     `∇_μ φ = ∂_μ φ`
  * (1,0) tensor `V^ν(x)`:   `∇_μ V^ν = ∂_μ V^ν + Γ^ν_{μρ} V^ρ`
  * (0,1) tensor `ω_ν(x)`:   `∇_μ ω_ν = ∂_μ ω_ν − Γ^ρ_{μν} ω_ρ`

This file defines the three cases pointwise. Higher-rank tensors
follow by repeated application of these rules.

**Connection to hypergraphs.** Same anchor as `CurvatureRiemann`: on
the continuum side. A future hypergraph covariant derivative (via
discrete connection on `FiberedGraph`) would pair with this via the
discrete → continuum convergence theorem.

**What we do NOT prove.** The Leibniz rule across the three types,
the commutator `[∇_μ, ∇_ν] V^ρ = R^ρ_{σμν} V^σ`, and the metric
compatibility `∇_μ g_{νρ} = 0` for Levi-Civita. Those are natural
next theorems.
-/

import InfraFormalization.CurvatureRiemann

namespace InfraFormalization
namespace Curvature
namespace ConnectionData

variable {n : Nat} (C : ConnectionData n)

/-- **Covariant derivative of a scalar field**. On a scalar field
`φ`, the covariant derivative coincides with the ordinary partial
derivative: `∇_μ φ(x) = ∂_μ φ(x)`. The user supplies both `φ` and
its partial derivatives `dφ`. -/
def nabla_scalar (dφ : Fin n → (Fin n → ℝ) → ℝ)
    (μ : Fin n) (x : Fin n → ℝ) : ℝ :=
  dφ μ x

/-- **Covariant derivative of a vector field** (1,0 tensor).

  `∇_μ V^ν(x) = ∂_μ V^ν(x) + ∑_ρ Γ^ν_{μρ}(x) · V^ρ(x)`.

User supplies `V` and `∂V` as data. -/
def nabla_vector (V : (Fin n → ℝ) → Fin n → ℝ)
    (dV : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  dV μ x ν + ∑ ρ : Fin n, C.Γ x ν μ ρ * V x ρ

/-- **Covariant derivative of a covector field** (0,1 tensor).

  `∇_μ ω_ν(x) = ∂_μ ω_ν(x) − ∑_ρ Γ^ρ_{μν}(x) · ω_ρ(x)`.

Note the sign difference from the vector case and the swapped upper
index position in the Christoffel term. -/
def nabla_covector (ω : (Fin n → ℝ) → Fin n → ℝ)
    (dω : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  dω μ x ν - ∑ ρ : Fin n, C.Γ x ρ μ ν * ω x ρ

/-- **Flat-connection covariant derivative = partial derivative** on
a scalar field (trivial; shown for completeness). -/
theorem nabla_scalar_flat (n : Nat) (dφ : Fin n → (Fin n → ℝ) → ℝ)
    (μ : Fin n) (x : Fin n → ℝ) :
    nabla_scalar dφ μ x = dφ μ x := rfl

/-- **Flat-connection covariant derivative of a vector field
coincides with the partial derivative**: on the flat connection,
`Γ ≡ 0`, so `∇_μ V^ν = ∂_μ V^ν`. -/
theorem nabla_vector_flat (n : Nat)
    (V : (Fin n → ℝ) → Fin n → ℝ)
    (dV : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) :
    (flatConnection n).nabla_vector V dV μ ν x = dV μ x ν := by
  unfold nabla_vector
  simp [flatConnection]

/-- **Flat-connection covariant derivative of a covector field
coincides with the partial derivative**: on the flat connection,
`∇_μ ω_ν = ∂_μ ω_ν`. -/
theorem nabla_covector_flat (n : Nat)
    (ω : (Fin n → ℝ) → Fin n → ℝ)
    (dω : Fin n → (Fin n → ℝ) → Fin n → ℝ)
    (μ ν : Fin n) (x : Fin n → ℝ) :
    (flatConnection n).nabla_covector ω dω μ ν x = dω μ x ν := by
  unfold nabla_covector
  simp [flatConnection]

/-- **Linearity (additivity) of the scalar covariant derivative.**
`∇_μ (dφ + dψ) = ∇_μ dφ + ∇_μ dψ`. Trivial on scalars. -/
theorem nabla_scalar_add (n : Nat) (dφ dψ : Fin n → (Fin n → ℝ) → ℝ)
    (μ : Fin n) (x : Fin n → ℝ) :
    nabla_scalar (fun μ x => dφ μ x + dψ μ x) μ x
      = nabla_scalar dφ μ x + nabla_scalar dψ μ x := by
  unfold nabla_scalar
  rfl

/-- **Linearity (additivity) of the vector covariant derivative.**
`∇_μ (V + W)^ν = ∇_μ V^ν + ∇_μ W^ν` at each point. -/
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

/-- **Linearity (additivity) of the covector covariant derivative.**
`∇_μ (ω + η)_ν = ∇_μ ω_ν + ∇_μ η_ν`. -/
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
