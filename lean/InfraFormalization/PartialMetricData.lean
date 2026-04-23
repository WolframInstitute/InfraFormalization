/-
**Partial metric data with domain predicate** (X1 / #24).

Some exact solutions of general relativity (Schwarzschild exterior,
FLRW-with-constraints, etc.) are only valid on a subset of ambient
coordinate space. A `MetricData n` demands the inverse axiom
`ginv_mul` *everywhere*, which is wrong for Schwarzschild: inside
the horizon `g_{tt}` changes sign and the components blow up at
`r = 2M`. So Schwarzschild does not naturally fit `MetricData 4`.

A `PartialMetricData n` carries a domain predicate `valid : (Fin n → ℝ) → Prop`
and asks inverse-compatibility, partial-derivative symmetry, etc.
*only when `valid x` holds*. The `MetricData n` form is the special
case `valid x = True`.

**Connection to hypergraphs.** Same anchor as `CurvatureLocalCoord`:
on the continuum side. A future hypergraph trajectory that produces a
manifold with singularities would pair with a `PartialMetricData`
via the bridge theorems.
-/

import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- **Partial metric data**: `MetricData n` with a domain predicate
`valid : (Fin n → ℝ) → Prop`. Axioms hold only at `x` with `valid x`.

Note that the *type* of the components `g`, `ginv`, `dg` is the same
(functions on the full `Fin n → ℝ`). Outside `valid`, these are
allowed to be anything; downstream theorems use them only inside
`valid`. This mirrors how a chart-extension in differential geometry
leaves values outside the chart unspecified. -/
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
  /-- Partial derivatives inherit symmetry on the validity domain. -/
  dg_symm : ∀ l x, valid x → ∀ μ ν, dg l x μ ν = dg l x ν μ

namespace PartialMetricData

variable {n : Nat} (M : PartialMetricData n)

/-- **Restricted Christoffel symbols** — only defined on the validity
domain. Outside `valid`, the value is the same formula applied to
whatever `ginv` and `dg` return (but not guaranteed to satisfy the
usual geometric axioms).

`Γ^ρ_{μν}(x) = ½ g^{ρσ}(x) · (∂_μ g_{σν}(x) + ∂_ν g_{σμ}(x) − ∂_σ g_{μν}(x))`. -/
noncomputable def christoffel (x : Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (1 / 2) * ∑ σ : Fin n,
    M.ginv x ρ σ *
      (M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν)

/-- **Christoffel symmetry on the validity domain.** -/
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

/-- **Every `MetricData n` is a `PartialMetricData n` with trivial
validity**: the domain predicate is `True` everywhere. -/
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

/-- **Consistency**: the partial Christoffel on `toPartial` equals
the full Christoffel. -/
theorem MetricData.toPartial_christoffel {n : Nat} (M : MetricData n)
    (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    M.toPartial.christoffel x ρ μ ν = M.christoffel x ρ μ ν := by
  unfold PartialMetricData.christoffel MetricData.christoffel MetricData.toPartial
  rfl

end Curvature
end InfraFormalization
