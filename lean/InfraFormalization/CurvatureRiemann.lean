/-
Riemann, Ricci, scalar and Einstein curvature in local coordinates, as formulas in supplied
data.

A `ConnectionData n` holds connection coefficients `Γ^ρ_{μν}(x)` and a table `∂_λ Γ^ρ_{μν}(x)`,
both symmetric in the lower indices; the table is not required to be the derivative of `Γ`.
The module defines the Riemann tensor, the Ricci contraction, the scalar curvature against a
`MetricData`, and the Einstein tensor `G_{μν} = R_{μν} − ½ R g_{μν}`. It proves antisymmetry of
Riemann in its last two indices and the first Bianchi identity, and that all four tensors
vanish for the zero connection. `MetricDataC2` adds tables of second derivatives of `g` and
first derivatives of `g⁻¹`, from which `leviCivitaConnection` builds a `ConnectionData`.
-/

import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- Connection coefficients and a table of their first partial derivatives. -/
structure ConnectionData (n : Nat) where
  /-- `Γ^ρ_{μν}(x)`. -/
  Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ
  /-- `∂_l Γ^ρ_{μν}(x)`. -/
  dΓ : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ
  /-- Lower-index symmetry of Γ (torsion-free). -/
  Γ_symm : ∀ x ρ μ ν, Γ x ρ μ ν = Γ x ρ ν μ
  /-- Lower-index symmetry of `dΓ`, assumed as a field because `dΓ` is supplied as data. -/
  dΓ_symm : ∀ l x ρ μ ν, dΓ l x ρ μ ν = dΓ l x ρ ν μ

namespace ConnectionData

variable {n : Nat} (C : ConnectionData n)

/-- The Riemann tensor

  `R^ρ_{σμν}(x) = ∂_μ Γ^ρ_{νσ}(x) − ∂_ν Γ^ρ_{μσ}(x)
                 + Σ_λ Γ^ρ_{μλ}(x) Γ^λ_{νσ}(x)
                 − Σ_λ Γ^ρ_{νλ}(x) Γ^λ_{μσ}(x)`.
-/
def riemann (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  C.dΓ μ x ρ ν σ - C.dΓ ν x ρ μ σ
    + (∑ l : Fin n, C.Γ x ρ μ l * C.Γ x l ν σ)
    - (∑ l : Fin n, C.Γ x ρ ν l * C.Γ x l μ σ)

/-- `R^ρ_{σμν} = −R^ρ_{σνμ}`. -/
theorem riemann_antisymm (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.riemann x ρ σ μ ν = - C.riemann x ρ σ ν μ := by
  unfold riemann
  ring

/-- The first Bianchi identity `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0`. The derivative terms
cancel by `dΓ_symm` and the quadratic terms cancel in pairs by `Γ_symm`. -/
theorem bianchi_first (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.riemann x ρ σ μ ν + C.riemann x ρ μ ν σ + C.riemann x ρ ν σ μ = 0 := by
  unfold riemann
  have hG := C.Γ_symm
  have hdG := C.dΓ_symm
  -- Align the lower indices of the derivative terms.
  have hd1 : C.dΓ μ x ρ ν σ = C.dΓ μ x ρ σ ν := hdG μ x ρ ν σ
  have hd2 : C.dΓ ν x ρ σ μ = C.dΓ ν x ρ μ σ := hdG ν x ρ σ μ
  have hd3 : C.dΓ σ x ρ μ ν = C.dΓ σ x ρ ν μ := hdG σ x ρ μ ν
  rw [hd1, hd2, hd3]
  -- Lower-index symmetries of the second factor in the quadratic terms.
  have hΓ1 : ∀ l, C.Γ x l ν σ = C.Γ x l σ ν := fun l => hG x l ν σ
  have hΓ2 : ∀ l, C.Γ x l μ σ = C.Γ x l σ μ := fun l => hG x l μ σ
  have hΓ3 : ∀ l, C.Γ x l σ μ = C.Γ x l μ σ := fun l => hG x l σ μ
  have hΓ4 : ∀ l, C.Γ x l ν μ = C.Γ x l μ ν := fun l => hG x l ν μ
  have hΓ5 : ∀ l, C.Γ x l μ ν = C.Γ x l ν μ := fun l => hG x l μ ν
  have hΓ6 : ∀ l, C.Γ x l σ ν = C.Γ x l ν σ := fun l => hG x l σ ν
  ring_nf
  -- The six quadratic sums cancel in pairs.
  have key :
      (∑ l, C.Γ x ρ μ l * C.Γ x l ν σ)
      - (∑ l, C.Γ x ρ ν l * C.Γ x l μ σ)
      + ((∑ l, C.Γ x ρ ν l * C.Γ x l σ μ)
         - (∑ l, C.Γ x ρ σ l * C.Γ x l ν μ))
      + ((∑ l, C.Γ x ρ σ l * C.Γ x l μ ν)
         - (∑ l, C.Γ x ρ μ l * C.Γ x l σ ν)) = 0 := by
    -- Pairs: terms 1 and 6, terms 2 and 3, terms 4 and 5.
    have p16 : (∑ l, C.Γ x ρ μ l * C.Γ x l ν σ)
             - (∑ l, C.Γ x ρ μ l * C.Γ x l σ ν) = 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intros l _
      rw [hG x l ν σ]
      ring
    have p23 : -(∑ l, C.Γ x ρ ν l * C.Γ x l μ σ)
             + (∑ l, C.Γ x ρ ν l * C.Γ x l σ μ) = 0 := by
      rw [show -(∑ l, C.Γ x ρ ν l * C.Γ x l μ σ)
              + (∑ l, C.Γ x ρ ν l * C.Γ x l σ μ)
            = (∑ l, C.Γ x ρ ν l * C.Γ x l σ μ)
              - (∑ l, C.Γ x ρ ν l * C.Γ x l μ σ) from by ring]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intros l _
      rw [hG x l μ σ]
      ring
    have p45 : -(∑ l, C.Γ x ρ σ l * C.Γ x l ν μ)
             + (∑ l, C.Γ x ρ σ l * C.Γ x l μ ν) = 0 := by
      rw [show -(∑ l, C.Γ x ρ σ l * C.Γ x l ν μ)
              + (∑ l, C.Γ x ρ σ l * C.Γ x l μ ν)
            = (∑ l, C.Γ x ρ σ l * C.Γ x l μ ν)
              - (∑ l, C.Γ x ρ σ l * C.Γ x l ν μ) from by ring]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intros l _
      rw [hG x l ν μ]
      ring
    linarith
  linarith

/-- The Ricci tensor `R_{σν}(x) = Σ_ρ R^ρ_{σρν}(x)`. -/
def ricci (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ : Fin n, C.riemann x ρ σ ρ ν

/-- The scalar curvature `R(x) = Σ_{σν} g^{σν}(x) R_{σν}(x)` for a supplied `MetricData`. The
connection is not required to be derived from the metric. -/
def scalarCurvature {n : Nat} (M : MetricData n) (C : ConnectionData n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ : Fin n, ∑ ν : Fin n, M.ginv x σ ν * C.ricci x σ ν

/-- The Einstein tensor `G_{μν}(x) = R_{μν}(x) − ½ R(x) g_{μν}(x)`. -/
noncomputable def einsteinTensor {n : Nat} (M : MetricData n)
    (C : ConnectionData n) (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  C.ricci x μ ν - (1 / 2) * scalarCurvature M C x * M.g x μ ν

end ConnectionData

/-- The zero connection: `Γ ≡ 0`, `dΓ ≡ 0`. -/
def flatConnection (n : Nat) : ConnectionData n where
  Γ := fun _ _ _ _ => 0
  dΓ := fun _ _ _ _ _ => 0
  Γ_symm := by intros; rfl
  dΓ_symm := by intros; rfl

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

/-- The Einstein tensor of the zero connection with the metric `minkowski4` is zero. This is
the case `M = minkowski4` of `flatConnection_einstein_zero`. -/
theorem minkowski4_satisfies_vacuum_EFE
    (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    ConnectionData.einsteinTensor minkowski4 (flatConnection 4) x μ ν = 0 :=
  flatConnection_einstein_zero minkowski4 x μ ν

/-! ## Connection from a metric with second-derivative data

The derivative table of the Christoffel symbols is computed from tables of second
derivatives of `g` and first derivatives of `g⁻¹`. The relation
`∂_μ g^{ρσ} = −g^{ρα} g^{σβ} ∂_μ g_{αβ}` is not imposed on the table `dginv`. -/

/-- `MetricData n` extended with a table `ddg l m x α β` for `∂_l ∂_m g_{αβ}(x)` and a table
`dginv l x ρ σ` for `∂_l g^{ρσ}(x)`. -/
structure MetricDataC2 (n : Nat) extends MetricData n where
  /-- Table for `∂_l ∂_m g_{αβ}(x)`. -/
  ddg : Fin n → Fin n → (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- Table for `∂_l g^{ρσ}(x)`; no relation to `dg` is imposed. -/
  dginv : Fin n → (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- `ddg` is symmetric in `α, β`. -/
  ddg_symm : ∀ l m x α β, ddg l m x α β = ddg l m x β α
  /-- `ddg` is symmetric in the two derivative indices `l, m`. -/
  ddg_swap_deriv : ∀ l m x α β, ddg l m x α β = ddg m l x α β

namespace MetricDataC2

variable {n : Nat} (M : MetricDataC2 n)

/-- The formula for the derivative of the Christoffel symbol in terms of the tables:

  `∂_λ Γ^ρ_{μν} = ½ (∂_λ g^{ρσ}) (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})
                 + ½ g^{ρσ} (∂_λ ∂_μ g_{σν} + ∂_λ ∂_ν g_{σμ} − ∂_λ ∂_σ g_{μν})`.
-/
noncomputable def dchristoffel (l : Fin n) (x : Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (1 / 2) * ∑ σ : Fin n,
    (M.dginv l x ρ σ *
       (M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν)
     + M.ginv x ρ σ *
       (M.ddg l μ x σ ν + M.ddg l ν x σ μ - M.ddg l σ x μ ν))

/-- `dchristoffel` is symmetric in its lower indices `μ, ν`. -/
theorem dchristoffel_symm (l : Fin n) (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    M.dchristoffel l x ρ μ ν = M.dchristoffel l x ρ ν μ := by
  unfold dchristoffel
  congr 1
  apply Finset.sum_congr rfl
  intros σ _
  have h1 : M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν
          = M.dg ν x σ μ + M.dg μ x σ ν - M.dg σ x ν μ := by
    rw [M.dg_symm σ x μ ν]
    ring
  have h2 : M.ddg l μ x σ ν + M.ddg l ν x σ μ - M.ddg l σ x μ ν
          = M.ddg l ν x σ μ + M.ddg l μ x σ ν - M.ddg l σ x ν μ := by
    rw [M.ddg_symm l σ x μ ν]
    ring
  rw [h1, h2]

/-- The `ConnectionData` with `Γ` the Christoffel symbols of the underlying `MetricData` and
`dΓ = dchristoffel`. -/
noncomputable def leviCivitaConnection : ConnectionData n where
  Γ := fun x ρ μ ν => M.toMetricData.christoffel x ρ μ ν
  dΓ := M.dchristoffel
  Γ_symm := fun x ρ μ ν =>
    M.toMetricData.christoffel_symm x ρ μ ν
  dΓ_symm := fun l x ρ μ ν =>
    M.dchristoffel_symm l x ρ μ ν

end MetricDataC2

end Curvature
end InfraFormalization
