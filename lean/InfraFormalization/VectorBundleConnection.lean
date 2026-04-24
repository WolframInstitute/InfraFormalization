import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
**Connection on a vector bundle** (C3 / #36).

Generalises `ConnectionData n` (which is the connection on the
*tangent* bundle `TM` — an `n`-dimensional fibre over an `n`-dimensional
base, with the Christoffel lower-index symmetry) to

    `VectorBundleConnection n k`

where:
  * `n` is the base-manifold dimension,
  * `k` is the vector-bundle fibre dimension,
  * `Γ^a_{μ b}(x)` is the connection 1-form coefficient, taking
    a base coordinate `μ : Fin n` and bundle-basis indices
    `a, b : Fin k`.

The covariant derivative of a section `s : (ℝⁿ) → (Fin k → ℝ)` with
components `s^a(x)` is

    `(∇_μ s)^a (x) = ∂_μ s^a (x) + Γ^a_{μ b}(x) · s^b(x)`.

Unlike the tangent-bundle case, no symmetry between the base-coordinate
index `μ` and a fibre index is imposed (the fibre indices label a
different space from the base coordinates).

Every `ConnectionData n` on a manifold of dimension `n` embeds into a
`VectorBundleConnection n n` via `VectorBundleConnection.ofConnectionData`.
This closes C3 while reusing the existing Christoffel machinery.
-/

namespace InfraFormalization
namespace Curvature

open scoped BigOperators

/-- **Connection on a vector bundle.** Base dimension `n`, fibre
dimension `k`. The data `Γ^a_{μ b}(x)` encodes the connection 1-form
with values in `End(fibre) ≅ Mat(k, k)`. -/
structure VectorBundleConnection (n k : Nat) where
  /-- The connection coefficients `Γ^a_{μ b}(x)`. -/
  Γ : (Fin n → ℝ) → Fin n → Fin k → Fin k → ℝ
  /-- First partial derivatives of `Γ` in the base coordinates,
  supplied as data (we do not differentiate via Mathlib's analysis). -/
  dΓ : Fin n → (Fin n → ℝ) → Fin n → Fin k → Fin k → ℝ

namespace VectorBundleConnection

variable {n k : Nat} (V : VectorBundleConnection n k)

/-- **Covariant derivative of a section** `s : (ℝⁿ) → (Fin k → ℝ)`.
`ds μ x a = ∂_μ s^a (x)` is supplied as data. The formula:
`(∇_μ s)^a (x) = ds μ x a + Σ_b Γ^a_{μ b}(x) · s^b(x)`. -/
def covariantDerivSection
    (s : (Fin n → ℝ) → Fin k → ℝ)
    (ds : Fin n → (Fin n → ℝ) → Fin k → ℝ) :
    Fin n → (Fin n → ℝ) → Fin k → ℝ :=
  fun μ x a => ds μ x a + ∑ b : Fin k, V.Γ x μ a b * s x b

/-- **Curvature 2-form** of a vector-bundle connection:
`F^a_{μν b}(x) = ∂_μ Γ^a_{ν b}(x) − ∂_ν Γ^a_{μ b}(x)
               + Σ_c Γ^a_{μ c}(x) Γ^c_{ν b}(x)
               − Σ_c Γ^a_{ν c}(x) Γ^c_{μ b}(x)`. -/
def curvature (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin k) : ℝ :=
  V.dΓ μ x ν a b - V.dΓ ν x μ a b
    + (∑ c : Fin k, V.Γ x μ a c * V.Γ x ν c b)
    - (∑ c : Fin k, V.Γ x ν a c * V.Γ x μ c b)

/-- **Antisymmetry of the curvature 2-form** in its base indices:
`F^a_{μν b} = −F^a_{νμ b}`. -/
theorem curvature_antisymm (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin k) :
    V.curvature x μ ν a b = - V.curvature x ν μ a b := by
  unfold curvature
  ring

end VectorBundleConnection

/-- **Flat vector-bundle connection**: `Γ ≡ 0`, `∂Γ ≡ 0`. -/
def flatVectorBundleConnection (n k : Nat) : VectorBundleConnection n k where
  Γ := fun _ _ _ _ => 0
  dΓ := fun _ _ _ _ _ => 0

/-- **Curvature vanishes on the flat connection.** -/
theorem flatVectorBundleConnection_curvature_zero (n k : Nat)
    (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin k) :
    (flatVectorBundleConnection n k).curvature x μ ν a b = 0 := by
  unfold VectorBundleConnection.curvature flatVectorBundleConnection
  simp

/-- **Covariant derivative on the flat connection reduces to the
partial derivative of the section.** -/
theorem flatVectorBundleConnection_covariantDerivSection_eq
    (n k : Nat)
    (s : (Fin n → ℝ) → Fin k → ℝ)
    (ds : Fin n → (Fin n → ℝ) → Fin k → ℝ)
    (μ : Fin n) (x : Fin n → ℝ) (a : Fin k) :
    (flatVectorBundleConnection n k).covariantDerivSection s ds μ x a
      = ds μ x a := by
  unfold VectorBundleConnection.covariantDerivSection flatVectorBundleConnection
  simp

/-- **Embed a tangent-bundle `ConnectionData n` as a
`VectorBundleConnection n n`.** The base dimension equals the fibre
dimension, and the Γ data coincides. This is the canonical way in which
Levi-Civita / Christoffel connections fit into the general vector-bundle
framework. -/
def VectorBundleConnection.ofConnectionData {n : Nat}
    (C : ConnectionData n) : VectorBundleConnection n n where
  Γ := fun x μ a b => C.Γ x a μ b
  dΓ := fun l x μ a b => C.dΓ l x a μ b

/-- **Sanity check**: the `flat` tangent-bundle connection, lifted to
a vector-bundle connection, *is* the flat vector-bundle connection. -/
theorem VectorBundleConnection.ofConnectionData_flat (n : Nat) :
    VectorBundleConnection.ofConnectionData (flatConnection n)
      = flatVectorBundleConnection n n := by
  unfold VectorBundleConnection.ofConnectionData flatConnection flatVectorBundleConnection
  rfl

/-- **Lifted curvature agrees with the Riemann tensor.** For a
tangent-bundle connection, the vector-bundle curvature `F^a_{μν b}`
coincides with the Riemann tensor `R^a_{b μν}` (with the tangent-fibre
indices `a, b` in the ρ, σ slots). -/
theorem VectorBundleConnection.ofConnectionData_curvature_eq_riemann
    {n : Nat} (C : ConnectionData n)
    (x : Fin n → ℝ) (μ ν : Fin n) (a b : Fin n) :
    (VectorBundleConnection.ofConnectionData C).curvature x μ ν a b
      = C.riemann x a b μ ν := by
  unfold VectorBundleConnection.curvature VectorBundleConnection.ofConnectionData
         ConnectionData.riemann
  ring

/-- **Torsion of a connection on the tangent bundle** (C4 / #37).

For a `VectorBundleConnection n n` — i.e. the fibre and base dimensions
coincide, so `Γ^a_{μ b}` can be interpreted with `a, b` as base
indices — the torsion tensor is

    `T^a_{μ b}(x) = Γ^a_{μ b}(x) − Γ^a_{b μ}(x)`.

A connection is **torsion-free** iff this vanishes pointwise. In the
tangent-bundle case (fibre = base) this matches the usual
`T^ρ_{μν} = Γ^ρ_{μν} − Γ^ρ_{νμ}`. -/
def VectorBundleConnection.torsion {n : Nat} (V : VectorBundleConnection n n)
    (x : Fin n → ℝ) (μ : Fin n) (a b : Fin n) : ℝ :=
  V.Γ x μ a b - V.Γ x b a μ

/-- **Torsion vanishes on the lifted tangent-bundle connection.**
Under `ofConnectionData`, the identification `Γ(x, μ, a, b) = C.Γ x a μ b`
combined with the lower-index symmetry `C.Γ_symm` gives
`Γ(x, b, a, μ) = C.Γ x a b μ = C.Γ x a μ b = Γ(x, μ, a, b)`. -/
theorem VectorBundleConnection.torsion_ofConnectionData_zero
    {n : Nat} (C : ConnectionData n)
    (x : Fin n → ℝ) (μ : Fin n) (a b : Fin n) :
    (VectorBundleConnection.ofConnectionData C).torsion x μ a b = 0 := by
  unfold VectorBundleConnection.torsion VectorBundleConnection.ofConnectionData
  have h := C.Γ_symm x a μ b
  linarith

/-- **Torsion vanishes on the flat vector-bundle connection.** -/
theorem flatVectorBundleConnection_torsion_zero (n : Nat)
    (x : Fin n → ℝ) (μ : Fin n) (a b : Fin n) :
    (flatVectorBundleConnection n n).torsion x μ a b = 0 := by
  unfold VectorBundleConnection.torsion flatVectorBundleConnection
  simp

/-- **Torsion-free predicate** on a tangent-bundle vector-bundle
connection: the torsion tensor vanishes everywhere. -/
def VectorBundleConnection.IsTorsionFree {n : Nat}
    (V : VectorBundleConnection n n) : Prop :=
  ∀ x μ a b, V.torsion x μ a b = 0

/-- **Every lifted tangent-bundle connection is torsion-free.** -/
theorem VectorBundleConnection.ofConnectionData_isTorsionFree
    {n : Nat} (C : ConnectionData n) :
    (VectorBundleConnection.ofConnectionData C).IsTorsionFree :=
  fun x μ a b => VectorBundleConnection.torsion_ofConnectionData_zero C x μ a b

/-- **The flat vector-bundle connection is torsion-free.** -/
theorem flatVectorBundleConnection_isTorsionFree (n : Nat) :
    (flatVectorBundleConnection n n).IsTorsionFree :=
  fun x μ a b => flatVectorBundleConnection_torsion_zero n x μ a b

/-- **Bundle-Γ consistency with local-coordinate Γ** (C6 / #39).

A torsion-free tangent-bundle `VectorBundleConnection n n` can be
recast as a local-coordinate `ConnectionData n`. With the mapping
`(ρ, μ, ν) ↦ V.Γ x μ ρ ν`, the local-coordinate lower-index symmetry
`Γ x ρ μ ν = Γ x ρ ν μ` translates to `V.Γ x μ ρ ν = V.Γ x ν ρ μ`,
which is delivered by torsion-freeness (both sides equal `V.Γ x ρ ν μ`
= `V.Γ x ρ μ ν` after the appropriate swap). The analogous identity
for `dΓ` is taken as hypothesis (we do not derive `dΓ` from `Γ`). -/
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

/-- **Round-trip through `ofConnectionData`**: starting from a
`ConnectionData n`, lifting to a `VectorBundleConnection n n`, and
projecting back via `toConnectionData` using the lifted
torsion-freeness and the symmetry of `C.dΓ` — recovers the original
`ConnectionData`. -/
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

/-- **Consistency of the bundle and local-coordinate `Γ` data** on a
torsion-free tangent-bundle connection: the `ConnectionData n` built
via `toConnectionData` has Christoffel symbols matching the bundle's
Γ with base indices swapped into the `(ρ, μ, ν)` local-coordinate
order. -/
theorem VectorBundleConnection.toConnectionData_Γ
    {n : Nat} (V : VectorBundleConnection n n)
    (hV : V.IsTorsionFree)
    (hdV : ∀ l x μ ρ ν, V.dΓ l x μ ρ ν = V.dΓ l x ν ρ μ)
    (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    (VectorBundleConnection.toConnectionData V hV hdV).Γ x ρ μ ν
      = V.Γ x μ ρ ν := rfl

/-- **Same consistency for `∂Γ`.** -/
theorem VectorBundleConnection.toConnectionData_dΓ
    {n : Nat} (V : VectorBundleConnection n n)
    (hV : V.IsTorsionFree)
    (hdV : ∀ l x μ ρ ν, V.dΓ l x μ ρ ν = V.dΓ l x ν ρ μ)
    (l : Fin n) (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    (VectorBundleConnection.toConnectionData V hV hdV).dΓ l x ρ μ ν
      = V.dΓ l x μ ρ ν := rfl

end Curvature
end InfraFormalization
