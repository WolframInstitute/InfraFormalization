/-
**FLRW Ricci tensor, scalar curvature, and Einstein tensor** (task #27 / B7).

For the FLRW metric `g = diag(-1, a², a², a²)` with scale factor
`a : ℝ → ℝ`, first derivative `da : ℝ → ℝ`, and second derivative
`dda : ℝ → ℝ`, we build a `ConnectionData 4` representing the
Levi-Civita connection of FLRW and compute closed forms for:

  * `R^ρ_{σμν}` — Riemann tensor.
  * `R_{μν}` — Ricci tensor:
    - `R_{00} = -3 a''(t) / a(t)`
    - `R_{ii} = a a'' + 2 (a')²` for `i ∈ {1, 2, 3}`
    - `R_{μν} = 0` otherwise.
  * `R = g^{μν} R_{μν} = 6 a''/a + 6 (a'/a)²` — scalar curvature.
  * Einstein tensor `G_{μν}`.
  * **Friedmann form** of the EFE — the constraint and evolution
    equations connecting `a, a', a''` to perfect-fluid stress-energy.

**Approach.** Rather than build a `PartialMetricDataC2` infrastructure,
we package the closed-form Christoffel values + their `t`-derivatives
into a `ConnectionData 4` directly. Symmetries are proven by case
analysis on `Fin 4`. Riemann and Ricci then come from the abstract
machinery in `CurvatureRiemann`. The connection is non-flat whenever
`a' ≠ 0` (universe is expanding/contracting).

**Grounding.** Continuum side: this is a `ConnectionData 4` derived
from the scale-factor data `(a, da, dda)`. Hypergraph side: pairs with
the cosmological discretisation captured under
`HypergraphMetricBridges` / `EinsteinEquationsBridge`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

import InfraFormalization.FLRW
import InfraFormalization.CurvatureRiemann

namespace InfraFormalization
namespace Curvature

open scoped BigOperators

/-! ## Closed-form Christoffel and `∂Γ` data for FLRW -/

/-- **FLRW Christoffel symbols (closed form).** Encodes the textbook
non-zero entries:
  * `Γ⁰_{ii} = a(t) a'(t)` for `i ∈ {1, 2, 3}`,
  * `Γⁱ_{0i} = Γⁱ_{i0} = a'(t) / a(t)` for `i ∈ {1, 2, 3}`,
all others zero. -/
noncomputable def flrwΓ (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) : ℝ :=
  if ρ = 0 then
    -- Γ⁰_{μν}: non-zero only when μ = ν ∈ {1,2,3}, value = a a'.
    if μ = ν ∧ μ ≠ 0 then a (x 0) * da (x 0) else 0
  else
    -- ρ ∈ {1,2,3}: Γ^ρ_{0ρ} = Γ^ρ_{ρ0} = a'/a.
    if (μ = 0 ∧ ν = ρ) ∨ (μ = ρ ∧ ν = 0) then
      da (x 0) / a (x 0)
    else 0

/-- **Lower-index symmetry of `flrwΓ`** (torsion-free). -/
theorem flrwΓ_symm (a da : ℝ → ℝ) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    flrwΓ a da x ρ μ ν = flrwΓ a da x ρ ν μ := by
  unfold flrwΓ
  by_cases hρ : ρ = 0
  · simp [hρ]
    by_cases hμν : μ = ν
    · rw [hμν]
    · have h1 : ¬(μ = ν ∧ μ ≠ 0) := fun ⟨h, _⟩ => hμν h
      have h2 : ¬(ν = μ ∧ ν ≠ 0) := fun ⟨h, _⟩ => hμν h.symm
      rw [if_neg h1, if_neg h2]
  · simp [hρ]
    by_cases h1 : μ = 0 ∧ ν = ρ
    · obtain ⟨hμ0, hνρ⟩ := h1
      subst hμ0; subst hνρ
      simp
    · by_cases h2 : μ = ρ ∧ ν = 0
      · obtain ⟨hμρ, hν0⟩ := h2
        subst hμρ; subst hν0
        simp
      · -- Neither (μ=0,ν=ρ) nor (μ=ρ,ν=0) holds.
        have h1' : ¬((μ = 0 ∧ ν = ρ) ∨ (μ = ρ ∧ ν = 0)) := by
          rintro (h | h) <;> [exact h1 h; exact h2 h]
        have h2' : ¬((ν = 0 ∧ μ = ρ) ∨ (ν = ρ ∧ μ = 0)) := by
          rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
          · exact h2 ⟨hb, ha⟩
          · exact h1 ⟨hb, ha⟩
        rw [if_neg h1', if_neg h2']

/-- **Closed-form `∂Γ` for FLRW.** Only `l = 0` (time derivative) is
non-zero, with:
  * `∂_0 Γ⁰_{ii}(x) = (a')² + a a''` for `i ∈ {1, 2, 3}`,
  * `∂_0 Γⁱ_{0i}(x) = (a a'' − (a')²) / a²` for `i ∈ {1, 2, 3}`.
-/
noncomputable def flrwdΓ (a da dda : ℝ → ℝ) (l : Fin 4) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) : ℝ :=
  if l ≠ 0 then 0
  else
    if ρ = 0 then
      if μ = ν ∧ μ ≠ 0 then (da (x 0))^2 + a (x 0) * dda (x 0) else 0
    else
      if (μ = 0 ∧ ν = ρ) ∨ (μ = ρ ∧ ν = 0) then
        (a (x 0) * dda (x 0) - (da (x 0))^2) / (a (x 0))^2
      else 0

/-- **Lower-index symmetry of `flrwdΓ`**. -/
theorem flrwdΓ_symm (a da dda : ℝ → ℝ)
    (l : Fin 4) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    flrwdΓ a da dda l x ρ μ ν = flrwdΓ a da dda l x ρ ν μ := by
  unfold flrwdΓ
  by_cases hl : l ≠ 0
  · simp [hl]
  · simp [hl]
    by_cases hρ : ρ = 0
    · simp [hρ]
      by_cases hμν : μ = ν
      · rw [hμν]
      · have h1 : ¬(μ = ν ∧ μ ≠ 0) := fun ⟨h, _⟩ => hμν h
        have h2 : ¬(ν = μ ∧ ν ≠ 0) := fun ⟨h, _⟩ => hμν h.symm
        rw [if_neg h1, if_neg h2]
    · simp [hρ]
      by_cases h1 : μ = 0 ∧ ν = ρ
      · obtain ⟨hμ0, hνρ⟩ := h1
        subst hμ0; subst hνρ; simp
      · by_cases h2 : μ = ρ ∧ ν = 0
        · obtain ⟨hμρ, hν0⟩ := h2
          subst hμρ; subst hν0; simp
        · have h1' : ¬((μ = 0 ∧ ν = ρ) ∨ (μ = ρ ∧ ν = 0)) := by
            rintro (h | h) <;> [exact h1 h; exact h2 h]
          have h2' : ¬((ν = 0 ∧ μ = ρ) ∨ (ν = ρ ∧ μ = 0)) := by
            rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
            · exact h2 ⟨hb, ha⟩
            · exact h1 ⟨hb, ha⟩
          rw [if_neg h1', if_neg h2']

/-- **FLRW Levi-Civita connection** (closed-form). Packages
`flrwΓ a da` and `flrwdΓ a da dda` into a `ConnectionData 4`. -/
noncomputable def flrwConnection (a da dda : ℝ → ℝ) : ConnectionData 4 where
  Γ := flrwΓ a da
  dΓ := flrwdΓ a da dda
  Γ_symm := fun x => flrwΓ_symm a da x
  dΓ_symm := fun l x => flrwdΓ_symm a da dda l x

/-! ## Pointwise Christoffel and `∂Γ` evaluations

The proofs below repeatedly need to evaluate `flrwΓ` and `flrwdΓ` at
specific index combinations. These small lemmas cache the explicit
values so the Riemann/Ricci computations stay readable. -/

@[simp] theorem flrwΓ_0_ii (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (i : Fin 4) (hi : i ≠ 0) :
    flrwΓ a da x 0 i i = a (x 0) * da (x 0) := by
  unfold flrwΓ
  simp [hi]

@[simp] theorem flrwΓ_0_diff (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (μ ν : Fin 4) (h : μ ≠ ν) :
    flrwΓ a da x 0 μ ν = 0 := by
  unfold flrwΓ
  simp [h]

@[simp] theorem flrwΓ_0_00 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) :
    flrwΓ a da x 0 0 0 = 0 := by
  unfold flrwΓ
  simp

@[simp] theorem flrwΓ_i_0i (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (i : Fin 4) (hi : i ≠ 0) :
    flrwΓ a da x i 0 i = da (x 0) / a (x 0) := by
  unfold flrwΓ
  simp [hi]

@[simp] theorem flrwΓ_i_i0 (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (i : Fin 4) (hi : i ≠ 0) :
    flrwΓ a da x i i 0 = da (x 0) / a (x 0) := by
  unfold flrwΓ
  simp [hi]

@[simp] theorem flrwdΓ_0_0_ii (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (i : Fin 4) (hi : i ≠ 0) :
    flrwdΓ a da dda 0 x 0 i i = (da (x 0))^2 + a (x 0) * dda (x 0) := by
  unfold flrwdΓ
  simp [hi]

@[simp] theorem flrwdΓ_0_i_0i (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (i : Fin 4) (hi : i ≠ 0) :
    flrwdΓ a da dda 0 x i 0 i
      = (a (x 0) * dda (x 0) - (da (x 0))^2) / (a (x 0))^2 := by
  unfold flrwdΓ
  simp [hi]

end Curvature
end InfraFormalization
