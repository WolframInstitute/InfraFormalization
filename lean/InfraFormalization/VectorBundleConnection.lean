import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
Connections on trivial vector bundles in coordinates.

A `VectorBundleConnection n k` has coefficients `Γ^a_{μ b}(x)` with base
index `μ : Fin n` and fibre indices `a, b : Fin k`, and their partial
derivatives supplied as data. This module defines the covariant derivative
`(∇_μ s)^a = ∂_μ s^a + Γ^a_{μ b} s^b`, the curvature `F^a_{μν b}` and, for
`k = n`, the torsion. It proves antisymmetry of the curvature, maps
`ConnectionData n` to `VectorBundleConnection n n` and back, and proves
that the curvature of the image is the Riemann tensor and that the image
is torsion-free.
-/

namespace InfraFormalization
namespace Curvature

open scoped BigOperators

/-- Coefficients `Γ^a_{μ b}(x)` for base dimension `n` and fibre dimension
`k`, with their partial derivatives `dΓ`. -/
structure VectorBundleConnection (n k : Nat) where
  /-- The connection coefficients `Γ^a_{μ b}(x)`. -/
  Γ : (Fin n → ℝ) → Fin n → Fin k → Fin k → ℝ
  /-- First partial derivatives of `Γ` in the base coordinates, supplied
  as data and not required to be derivatives of `Γ`. -/
  dΓ : Fin n → (Fin n → ℝ) → Fin n → Fin k → Fin k → ℝ

namespace VectorBundleConnection

variable {n k : Nat} (V : VectorBundleConnection n k)

/-- `(∇_μ s)^a (x) = ds μ x a + Σ_b Γ^a_{μ b}(x) · s^b(x)`, where `ds` is
supplied as data. -/
def covariantDerivSection
    (s : (Fin n → ℝ) → Fin k → ℝ)
    (ds : Fin n → (Fin n → ℝ) → Fin k → ℝ) :
    Fin n → (Fin n → ℝ) → Fin k → ℝ :=
  fun μ x a => ds μ x a + ∑ b : Fin k, V.Γ x μ a b * s x b

/-- The curvature
`F^a_{μν b}(x) = ∂_μ Γ^a_{ν b}(x) − ∂_ν Γ^a_{μ b}(x)
               + Σ_c Γ^a_{μ c}(x) Γ^c_{ν b}(x)
               − Σ_c Γ^a_{ν c}(x) Γ^c_{μ b}(x)`. -/
def curvature (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin k) : ℝ :=
  V.dΓ μ x ν a b - V.dΓ ν x μ a b
    + (∑ c : Fin k, V.Γ x μ a c * V.Γ x ν c b)
    - (∑ c : Fin k, V.Γ x ν a c * V.Γ x μ c b)

/-- `F^a_{μν b} = −F^a_{νμ b}`. -/
theorem curvature_antisymm (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin k) :
    V.curvature x μ ν a b = - V.curvature x ν μ a b := by
  unfold curvature
  ring

end VectorBundleConnection

/-- The connection with `Γ = 0` and `dΓ = 0`. -/
def flatVectorBundleConnection (n k : Nat) : VectorBundleConnection n k where
  Γ := fun _ _ _ _ => 0
  dΓ := fun _ _ _ _ _ => 0

/-- The curvature of `flatVectorBundleConnection` is 0. -/
theorem flatVectorBundleConnection_curvature_zero (n k : Nat)
    (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin k) :
    (flatVectorBundleConnection n k).curvature x μ ν a b = 0 := by
  unfold VectorBundleConnection.curvature flatVectorBundleConnection
  simp

/-- For `flatVectorBundleConnection`, the covariant derivative equals
`ds μ x a`. -/
theorem flatVectorBundleConnection_covariantDerivSection_eq
    (n k : Nat)
    (s : (Fin n → ℝ) → Fin k → ℝ)
    (ds : Fin n → (Fin n → ℝ) → Fin k → ℝ)
    (μ : Fin n) (x : Fin n → ℝ) (a : Fin k) :
    (flatVectorBundleConnection n k).covariantDerivSection s ds μ x a
      = ds μ x a := by
  unfold VectorBundleConnection.covariantDerivSection flatVectorBundleConnection
  simp

/-- The `VectorBundleConnection n n` with `Γ x μ a b = C.Γ x a μ b` and
`dΓ l x μ a b = C.dΓ l x a μ b`. -/
def VectorBundleConnection.ofConnectionData {n : Nat}
    (C : ConnectionData n) : VectorBundleConnection n n where
  Γ := fun x μ a b => C.Γ x a μ b
  dΓ := fun l x μ a b => C.dΓ l x a μ b

/-- `ofConnectionData (flatConnection n) = flatVectorBundleConnection n n`. -/
theorem VectorBundleConnection.ofConnectionData_flat (n : Nat) :
    VectorBundleConnection.ofConnectionData (flatConnection n)
      = flatVectorBundleConnection n n := by
  unfold VectorBundleConnection.ofConnectionData flatConnection flatVectorBundleConnection
  rfl

/-- The curvature `F^a_{μν b}` of `ofConnectionData C` equals the Riemann
tensor `R^a_{b μν}` of `C`. -/
theorem VectorBundleConnection.ofConnectionData_curvature_eq_riemann
    {n : Nat} (C : ConnectionData n)
    (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin n) :
    (VectorBundleConnection.ofConnectionData C).curvature x μ ν a b
      = C.riemann x a b μ ν := by
  unfold VectorBundleConnection.curvature VectorBundleConnection.ofConnectionData
         ConnectionData.riemann
  ring

/-- For fibre dimension equal to base dimension, the torsion
`T^a_{μ b}(x) = Γ^a_{μ b}(x) − Γ^a_{b μ}(x)`. -/
def VectorBundleConnection.torsion {n : Nat} (V : VectorBundleConnection n n)
    (x : Fin n → ℝ) (μ : Fin n) (a b : Fin n) : ℝ :=
  V.Γ x μ a b - V.Γ x b a μ

/-- The torsion of `ofConnectionData C` is 0, by the lower-index symmetry
`C.Γ_symm`. -/
theorem VectorBundleConnection.torsion_ofConnectionData_zero
    {n : Nat} (C : ConnectionData n)
    (x : Fin n → ℝ) (μ : Fin n) (a b : Fin n) :
    (VectorBundleConnection.ofConnectionData C).torsion x μ a b = 0 := by
  unfold VectorBundleConnection.torsion VectorBundleConnection.ofConnectionData
  have h := C.Γ_symm x a μ b
  linarith

/-- The torsion of `flatVectorBundleConnection n n` is 0. -/
theorem flatVectorBundleConnection_torsion_zero (n : Nat)
    (x : Fin n → ℝ) (μ : Fin n) (a b : Fin n) :
    (flatVectorBundleConnection n n).torsion x μ a b = 0 := by
  unfold VectorBundleConnection.torsion flatVectorBundleConnection
  simp

/-- The torsion is 0 at every point and for all indices. -/
def VectorBundleConnection.IsTorsionFree {n : Nat}
    (V : VectorBundleConnection n n) : Prop :=
  ∀ x μ a b, V.torsion x μ a b = 0

/-- `ofConnectionData C` is torsion-free. -/
theorem VectorBundleConnection.ofConnectionData_isTorsionFree
    {n : Nat} (C : ConnectionData n) :
    (VectorBundleConnection.ofConnectionData C).IsTorsionFree :=
  fun x μ a b => VectorBundleConnection.torsion_ofConnectionData_zero C x μ a b

/-- `flatVectorBundleConnection n n` is torsion-free. -/
theorem flatVectorBundleConnection_isTorsionFree (n : Nat) :
    (flatVectorBundleConnection n n).IsTorsionFree :=
  fun x μ a b => flatVectorBundleConnection_torsion_zero n x μ a b

/-- A torsion-free `VectorBundleConnection n n` as a `ConnectionData n`
with `Γ x ρ μ ν = V.Γ x μ ρ ν`. Torsion-freeness gives the lower-index
symmetry of `Γ`; the symmetry of `dΓ` is the hypothesis `hdV`. -/
noncomputable def VectorBundleConnection.toConnectionData {n : Nat}
    (V : VectorBundleConnection n n)
    (hV : V.IsTorsionFree)
    (hdV : ∀ l x μ ρ ν, V.dΓ l x μ ρ ν = V.dΓ l x ν ρ μ) :
    ConnectionData n where
  Γ := fun x ρ μ ν => V.Γ x μ ρ ν
  dΓ := fun l x ρ μ ν => V.dΓ l x μ ρ ν
  Γ_symm := fun x ρ μ ν => by
    have h1 := hV x μ ρ ν
    have h2 := hV x ν ρ μ
    unfold VectorBundleConnection.torsion at h1 h2
    linarith
  dΓ_symm := fun l x ρ μ ν => hdV l x μ ρ ν

/-- `toConnectionData (ofConnectionData C) = C`. -/
theorem VectorBundleConnection.toConnectionData_ofConnectionData
    {n : Nat} (C : ConnectionData n) :
    VectorBundleConnection.toConnectionData
        (VectorBundleConnection.ofConnectionData C)
        (VectorBundleConnection.ofConnectionData_isTorsionFree C)
        (fun l x μ ρ ν => by
          unfold VectorBundleConnection.ofConnectionData
          exact C.dΓ_symm l x ρ μ ν)
      = C := by
  unfold VectorBundleConnection.toConnectionData VectorBundleConnection.ofConnectionData
  rfl

/-- `(toConnectionData V hV hdV).Γ x ρ μ ν = V.Γ x μ ρ ν`, by `rfl`. -/
theorem VectorBundleConnection.toConnectionData_Γ
    {n : Nat} (V : VectorBundleConnection n n)
    (hV : V.IsTorsionFree)
    (hdV : ∀ l x μ ρ ν, V.dΓ l x μ ρ ν = V.dΓ l x ν ρ μ)
    (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    (VectorBundleConnection.toConnectionData V hV hdV).Γ x ρ μ ν
      = V.Γ x μ ρ ν := rfl

/-- `(toConnectionData V hV hdV).dΓ l x ρ μ ν = V.dΓ l x μ ρ ν`, by
`rfl`. -/
theorem VectorBundleConnection.toConnectionData_dΓ
    {n : Nat} (V : VectorBundleConnection n n)
    (hV : V.IsTorsionFree)
    (hdV : ∀ l x μ ρ ν, V.dΓ l x μ ρ ν = V.dΓ l x ν ρ μ)
    (l : Fin n) (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    (VectorBundleConnection.toConnectionData V hV hdV).dΓ l x ρ μ ν
      = V.dΓ l x μ ρ ν := rfl

end Curvature
end InfraFormalization
