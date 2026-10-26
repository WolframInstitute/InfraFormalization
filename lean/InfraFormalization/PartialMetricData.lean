/-
Metric data with a domain of validity.

`MetricData n` requires `ginv` to be the inverse of `g` at every point, which fails for metrics such
as Schwarzschild, whose components are singular at `r = 2M`. This module defines
`PartialMetricData n`, which carries a predicate `valid` and requires symmetry and the inverse
relation only where `valid x` holds. It defines the Christoffel symbols, proves their symmetry in
the
lower indices on the domain, and embeds `MetricData n` with `valid = True`.
-/

import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- Metric components `g`, inverse components `ginv` and first derivatives `dg` on `Fin n → ℝ`, with
a
predicate `valid`. Symmetry and the inverse relation are required only at points where `valid`
holds,
and the components are unconstrained elsewhere. -/
structure PartialMetricData (n : Nat) where
  /-- Metric components `g_{μν}(x)`. -/
  g : (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- Inverse metric components `g^{μν}(x)`. -/
  ginv : (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- First partial derivatives `∂_l g_{μν}(x)`, indexed by `l : Fin n`. -/
  dg : Fin n → (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- Domain of validity: predicate on spacetime points. -/
  valid : (Fin n → ℝ) → Prop
  /-- `g` is symmetric on the validity domain. -/
  g_symm : ∀ x, valid x → ∀ μ ν, g x μ ν = g x ν μ
  /-- `ginv` is symmetric on the validity domain. -/
  ginv_symm : ∀ x, valid x → ∀ μ ν, ginv x μ ν = ginv x ν μ
  /-- `ginv` is the matrix inverse of `g` on the validity domain. -/
  ginv_mul : ∀ x, valid x → ∀ μ ν,
    (∑ α : Fin n, ginv x μ α * g x α ν) = if μ = ν then 1 else 0
  /-- `dg l x` is symmetric on the validity domain. -/
  dg_symm : ∀ l x, valid x → ∀ μ ν, dg l x μ ν = dg l x ν μ

namespace PartialMetricData

variable {n : Nat} (M : PartialMetricData n)

/-- `Γ^ρ_{μν}(x) = ½ g^{ρσ}(x) · (∂_μ g_{σν}(x) + ∂_ν g_{σμ}(x) − ∂_σ g_{μν}(x))`, defined at every
point. -/
noncomputable def christoffel (x : Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (1 / 2) * ∑ σ : Fin n,
    M.ginv x ρ σ *
      (M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν)

/-- If `valid x`, then `Γ^ρ_{μν}(x) = Γ^ρ_{νμ}(x)`. -/
theorem christoffel_symm (x : Fin n → ℝ) (hv : M.valid x) (ρ μ ν : Fin n) :
    M.christoffel x ρ μ ν = M.christoffel x ρ ν μ := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intros σ _
  have h1 : M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν
          = M.dg ν x σ μ + M.dg μ x σ ν - M.dg σ x ν μ := by
    rw [M.dg_symm σ x hv μ ν]
    ring
  rw [h1]

end PartialMetricData

/-- A `MetricData n` as a `PartialMetricData n` with `valid x = True`. -/
noncomputable def MetricData.toPartial {n : Nat} (M : MetricData n) :
    PartialMetricData n where
  g := M.g
  ginv := M.ginv
  dg := M.dg
  valid := fun _ => True
  g_symm := fun x _ => M.g_symm x
  ginv_symm := fun x _ => M.ginv_symm x
  ginv_mul := fun x _ => M.ginv_mul x
  dg_symm := fun l x _ => M.dg_symm l x

/-- The Christoffel symbols of `M.toPartial` equal those of `M`. -/
theorem MetricData.toPartial_christoffel {n : Nat} (M : MetricData n)
    (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    M.toPartial.christoffel x ρ μ ν = M.christoffel x ρ μ ν := by
  unfold PartialMetricData.christoffel MetricData.christoffel MetricData.toPartial
  rfl

end Curvature
end InfraFormalization
