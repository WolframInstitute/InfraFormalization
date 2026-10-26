/-
Ricci tensor, scalar curvature and Einstein tensor of a connection with FLRW Christoffel symbols.

For functions `a da dda : ℝ → ℝ`, `flrwConnection a da dda` is a `ConnectionData 4` whose
Christoffel symbols are those of `g = diag(-1, a², a², a²)` with `da` in place of `a'`, and whose
`∂Γ` entries are the time derivatives of those symbols with `dda` in place of `a''`.
No hypothesis relates `da` and `dda` to derivatives of `a`.
Under `a (x 0) ≠ 0`, the module proves `R_{00} = -3 dda/a`, `R_{ii} = a·dda + 2 da²` for
`i ∈ {1, 2, 3}`, and `R_{μν} = 0` for `μ < ν`, using the Riemann and Ricci definitions in
`CurvatureRiemann`.
It defines the diagonal trace `6 dda/a + 6 (da/a)²` as the scalar curvature, the perfect-fluid
stress-energy `diag(ρ, p a², p a², p a²)` and the two Friedmann equations, and proves that the
`00` and `11` components of `G_{μν} + Λ g_{μν} = κ T_{μν}` are equivalent to the Friedmann pair.
-/

import InfraFormalization.FLRW
import InfraFormalization.CurvatureRiemann

namespace InfraFormalization
namespace Curvature

open scoped BigOperators

/-! ## Closed-form Christoffel and `∂Γ` data for FLRW -/

/-- Christoffel symbols with non-zero entries `Γ⁰_{ii} = a · da` and
`Γⁱ_{0i} = Γⁱ_{i0} = da / a` for `i ∈ {1, 2, 3}`, evaluated at time `x 0`. All other entries
are zero. -/
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

/-- `flrwΓ a da x ρ μ ν = flrwΓ a da x ρ ν μ`. -/
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

/-- Derivative data for `flrwΓ`. Entries with `l ≠ 0` are zero. For `l = 0` the non-zero entries
are `∂_0 Γ⁰_{ii} = da² + a · dda` and `∂_0 Γⁱ_{0i} = ∂_0 Γⁱ_{i0} = (a · dda − da²) / a²` for
`i ∈ {1, 2, 3}`.
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

/-- `flrwdΓ a da dda l x ρ μ ν = flrwdΓ a da dda l x ρ ν μ`. -/
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

/-- The `ConnectionData 4` with `Γ = flrwΓ a da` and `dΓ = flrwdΓ a da dda`. -/
noncomputable def flrwConnection (a da dda : ℝ → ℝ) : ConnectionData 4 where
  Γ := flrwΓ a da
  dΓ := flrwdΓ a da dda
  Γ_symm := fun x => flrwΓ_symm a da x
  dΓ_symm := fun l x => flrwdΓ_symm a da dda l x

/-! ## Values of `flrwΓ` and `flrwdΓ` at specific indices -/

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

@[simp] theorem flrwdΓ_0_i_i0 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (i : Fin 4) (hi : i ≠ 0) :
    flrwdΓ a da dda 0 x i i 0
      = (a (x 0) * dda (x 0) - (da (x 0))^2) / (a (x 0))^2 := by
  unfold flrwdΓ
  simp [hi]

/-- `∑ l : Fin 4, f l = f 0 + f 1 + f 2 + f 3`. -/
private theorem sumFin4 {β : Type*} [AddCommMonoid β] (f : Fin 4 → β) :
    ∑ l : Fin 4, f l = f 0 + f 1 + f 2 + f 3 := by
  show ∑ l ∈ (Finset.univ : Finset (Fin 4)), f l = f 0 + f 1 + f 2 + f 3
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} from by decide]
  simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, add_assoc]

/-- `flrwΓ a da x l 0 0 = 0` for every `l`. -/
@[simp] theorem flrwΓ_l_00 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) (l : Fin 4) :
    flrwΓ a da x l 0 0 = 0 := by
  by_cases hl : l = 0
  · subst hl; rfl
  · unfold flrwΓ
    have h_ne_l : (0 : Fin 4) ≠ l := fun h => hl h.symm
    simp [hl, h_ne_l]

/-! ## Riemann components: time-time direction -/

/-- If `a (x 0) ≠ 0`, then `R^1_{010}(x) = -dda/a`. -/
theorem flrwRiemann_1_0_1_0 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 1 0 1 0 = -(dda (x 0) / a (x 0)) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 0 0),
      sumFin4 (fun l => flrwΓ a da x 1 0 l * flrwΓ a da x l 1 0)]
  -- Γ_x_l_0_0 vanishes for all l (handled by flrwΓ_l_00 simp).
  -- Γ_x_1_0_l: non-zero iff l=1 (value a'/a), zero otherwise.
  -- Γ_x_l_1_0: non-zero iff l=1 (value a'/a), zero otherwise.
  -- Specifically:
  have h10 : flrwΓ a da x 1 0 0 = 0 := flrwΓ_l_00 a da x 1
  have h12 : flrwΓ a da x 1 0 2 = 0 := by unfold flrwΓ; simp
  have h13 : flrwΓ a da x 1 0 3 = 0 := by unfold flrwΓ; simp
  have h0_10 : flrwΓ a da x 0 1 0 = 0 :=
    flrwΓ_0_diff a da x 1 0 (by decide)
  have h2_10 : flrwΓ a da x 2 1 0 = 0 := by unfold flrwΓ; simp
  have h3_10 : flrwΓ a da x 3 1 0 = 0 := by unfold flrwΓ; simp
  have h_dΓ_1_1_0_0 : flrwdΓ a da dda 1 x 1 0 0 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_0_1_1_0 : flrwdΓ a da dda 0 x 1 1 0
      = (a (x 0) * dda (x 0) - (da (x 0))^2) / (a (x 0))^2 :=
    flrwdΓ_0_i_i0 a da dda x 1 (by decide)
  have h_Γ_1_0_1 : flrwΓ a da x 1 0 1 = da (x 0) / a (x 0) :=
    flrwΓ_i_0i a da x 1 (by decide)
  have h_Γ_1_1_0 : flrwΓ a da x 1 1 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 1 (by decide)
  -- After sumFin4 + flrwΓ_l_00 simp, the goal collapses to:
  --   0 - (a a'' - (a')²)/a² + 0 - (0*Γ_0_1_0 + (a'/a)*(a'/a) + Γ_1_0_2*Γ_2_1_0 + Γ_1_0_3*Γ_3_1_0)
  -- Rewrite remaining Γ entries to zero/value, then field_simp.
  simp only [h_dΓ_1_1_0_0, h_dΓ_0_1_1_0, h12, h13, h0_10, h2_10, h3_10,
             h_Γ_1_0_1, h_Γ_1_1_0, flrwΓ_l_00, mul_zero, add_zero, zero_add]
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R^2_{020}(x) = -dda/a`. -/
theorem flrwRiemann_2_0_2_0 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 2 0 2 0 = -(dda (x 0) / a (x 0)) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 2 2 l * flrwΓ a da x l 0 0),
      sumFin4 (fun l => flrwΓ a da x 2 0 l * flrwΓ a da x l 2 0)]
  have h20 : flrwΓ a da x 2 0 0 = 0 := flrwΓ_l_00 a da x 2
  have h21 : flrwΓ a da x 2 0 1 = 0 := by unfold flrwΓ; simp
  have h23 : flrwΓ a da x 2 0 3 = 0 := by unfold flrwΓ; simp
  have h0_20 : flrwΓ a da x 0 2 0 = 0 :=
    flrwΓ_0_diff a da x 2 0 (by decide)
  have h1_20 : flrwΓ a da x 1 2 0 = 0 := by unfold flrwΓ; simp
  have h3_20 : flrwΓ a da x 3 2 0 = 0 := by unfold flrwΓ; simp
  have h_dΓ_2_2_0_0 : flrwdΓ a da dda 2 x 2 0 0 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_0_2_2_0 : flrwdΓ a da dda 0 x 2 2 0
      = (a (x 0) * dda (x 0) - (da (x 0))^2) / (a (x 0))^2 :=
    flrwdΓ_0_i_i0 a da dda x 2 (by decide)
  have h_Γ_2_0_2 : flrwΓ a da x 2 0 2 = da (x 0) / a (x 0) :=
    flrwΓ_i_0i a da x 2 (by decide)
  have h_Γ_2_2_0 : flrwΓ a da x 2 2 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 2 (by decide)
  simp only [h_dΓ_2_2_0_0, h_dΓ_0_2_2_0, h21, h23, h0_20, h1_20, h3_20,
             h_Γ_2_0_2, h_Γ_2_2_0, flrwΓ_l_00, mul_zero, add_zero, zero_add]
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R^3_{030}(x) = -dda/a`. -/
theorem flrwRiemann_3_0_3_0 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 3 0 3 0 = -(dda (x 0) / a (x 0)) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 3 3 l * flrwΓ a da x l 0 0),
      sumFin4 (fun l => flrwΓ a da x 3 0 l * flrwΓ a da x l 3 0)]
  have h30 : flrwΓ a da x 3 0 0 = 0 := flrwΓ_l_00 a da x 3
  have h31 : flrwΓ a da x 3 0 1 = 0 := by unfold flrwΓ; simp
  have h32 : flrwΓ a da x 3 0 2 = 0 := by unfold flrwΓ; simp
  have h0_30 : flrwΓ a da x 0 3 0 = 0 :=
    flrwΓ_0_diff a da x 3 0 (by decide)
  have h1_30 : flrwΓ a da x 1 3 0 = 0 := by unfold flrwΓ; simp
  have h2_30 : flrwΓ a da x 2 3 0 = 0 := by unfold flrwΓ; simp
  have h_dΓ_3_3_0_0 : flrwdΓ a da dda 3 x 3 0 0 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_0_3_3_0 : flrwdΓ a da dda 0 x 3 3 0
      = (a (x 0) * dda (x 0) - (da (x 0))^2) / (a (x 0))^2 :=
    flrwdΓ_0_i_i0 a da dda x 3 (by decide)
  have h_Γ_3_0_3 : flrwΓ a da x 3 0 3 = da (x 0) / a (x 0) :=
    flrwΓ_i_0i a da x 3 (by decide)
  have h_Γ_3_3_0 : flrwΓ a da x 3 3 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 3 (by decide)
  simp only [h_dΓ_3_3_0_0, h_dΓ_0_3_3_0, h31, h32, h0_30, h1_30, h2_30,
             h_Γ_3_0_3, h_Γ_3_3_0, flrwΓ_l_00, mul_zero, add_zero, zero_add]
  field_simp
  ring

/-! ## Riemann components: spatial-spatial direction (for `R_{ii}`) -/

/-- If `a (x 0) ≠ 0`, then `R^0_{101}(x) = a · dda`. -/
theorem flrwRiemann_0_1_0_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 0 1 0 1 = a (x 0) * dda (x 0) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 1 1),
      sumFin4 (fun l => flrwΓ a da x 0 1 l * flrwΓ a da x l 0 1)]
  -- Term 1: dΓ 0 x 0 1 1 = (da)² + a*dda.
  have h_dΓ_t1 : flrwdΓ a da dda 0 x 0 1 1 = (da (x 0))^2 + a (x 0) * dda (x 0) :=
    flrwdΓ_0_0_ii a da dda x 1 (by decide)
  -- Term 2: dΓ 1 x 0 0 1 = 0 (l=1 ≠ 0).
  have h_dΓ_t2 : flrwdΓ a da dda 1 x 0 0 1 = 0 := by unfold flrwdΓ; simp
  -- Sum 1 entries: Γ_x_0_0_l = 0 (μ=0, ν=l with ρ=0: μ=ν only when l=0; off-diag else; and l=0 case Γ_0_0_0 = 0).
  have hΓ_0_0_0 : flrwΓ a da x 0 0 0 = 0 := flrwΓ_0_00 a da x
  have hΓ_0_0_1 : flrwΓ a da x 0 0 1 = 0 := flrwΓ_0_diff a da x 0 1 (by decide)
  have hΓ_0_0_2 : flrwΓ a da x 0 0 2 = 0 := flrwΓ_0_diff a da x 0 2 (by decide)
  have hΓ_0_0_3 : flrwΓ a da x 0 0 3 = 0 := flrwΓ_0_diff a da x 0 3 (by decide)
  -- Sum 2 entries.
  -- Γ_x_0_1_l: ρ=0, μ=1, ν=l. Non-zero iff μ=ν (l=1) and μ≠0 (1≠0 true). Value a*a' for l=1.
  have hΓ_0_1_0 : flrwΓ a da x 0 1 0 = 0 :=
    flrwΓ_0_diff a da x 1 0 (by decide)
  have hΓ_0_1_1 : flrwΓ a da x 0 1 1 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 1 (by decide)
  have hΓ_0_1_2 : flrwΓ a da x 0 1 2 = 0 :=
    flrwΓ_0_diff a da x 1 2 (by decide)
  have hΓ_0_1_3 : flrwΓ a da x 0 1 3 = 0 :=
    flrwΓ_0_diff a da x 1 3 (by decide)
  -- Γ_x_l_0_1: ρ=l. l=0: μ=0,ν=1, off-diag, 0. l=1: ρ=1, (μ=0∧ν=ρ=1)=T, value a'/a. l=2,3: conditions fail, 0.
  have hΓ_0_0_1' : flrwΓ a da x 0 0 1 = 0 :=
    flrwΓ_0_diff a da x 0 1 (by decide)
  have hΓ_1_0_1 : flrwΓ a da x 1 0 1 = da (x 0) / a (x 0) :=
    flrwΓ_i_0i a da x 1 (by decide)
  have hΓ_2_0_1 : flrwΓ a da x 2 0 1 = 0 := by unfold flrwΓ; simp
  have hΓ_3_0_1 : flrwΓ a da x 3 0 1 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_0_0_0, hΓ_0_0_1, hΓ_0_0_2, hΓ_0_0_3,
             hΓ_0_1_0, hΓ_0_1_1, hΓ_0_1_2, hΓ_0_1_3,
             hΓ_0_0_1', hΓ_1_0_1, hΓ_2_0_1, hΓ_3_0_1,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R^2_{121}(x) = da²`. -/
theorem flrwRiemann_2_1_2_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 2 1 2 1 = (da (x 0))^2 := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 2 2 l * flrwΓ a da x l 1 1),
      sumFin4 (fun l => flrwΓ a da x 2 1 l * flrwΓ a da x l 2 1)]
  -- Both ∂Γ terms vanish (l = 2 or 1, both ≠ 0 → flrwdΓ returns 0).
  have h_dΓ_t1 : flrwdΓ a da dda 2 x 2 1 1 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_t2 : flrwdΓ a da dda 1 x 2 2 1 = 0 := by unfold flrwdΓ; simp
  -- Sum 1 (Γ_2_2_l * Γ_l_1_1):
  -- l=0: Γ_2_2_0 = a'/a, Γ_0_1_1 = a*a'. Product (a'/a)(a a') = (a')².
  -- l=1: Γ_2_2_1 = 0 (ρ=2, μ=ν=2 fails l=1), Γ_1_1_1 = 0. 0.
  -- l=2: Γ_2_2_2 = 0 (ρ=2, μ=ν=2: conditions need μ=0∨ν=0). 0.
  -- l=3: Γ_2_2_3 = 0. 0.
  have hΓ_2_2_0 : flrwΓ a da x 2 2 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 2 (by decide)
  have hΓ_0_1_1 : flrwΓ a da x 0 1 1 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 1 (by decide)
  have hΓ_2_2_1 : flrwΓ a da x 2 2 1 = 0 := by unfold flrwΓ; simp
  have hΓ_2_2_2 : flrwΓ a da x 2 2 2 = 0 := by unfold flrwΓ; simp
  have hΓ_2_2_3 : flrwΓ a da x 2 2 3 = 0 := by unfold flrwΓ; simp
  -- Sum 2 (Γ_2_1_l * Γ_l_2_1): all Γ_2_1_l = 0 (ρ=2, μ=1: only ν=0 or ν=2 matter, and (μ=0∨ν=ρ) needs μ=1=0 or ν=l=2; (μ=ρ∨ν=0) needs μ=1=2 or ν=l=0).
  -- Specifically Γ_2_1_0 = 0, Γ_2_1_1 = 0, Γ_2_1_2 = 0 (μ=1, ν=2: conditions fail), Γ_2_1_3 = 0.
  have hΓ_2_1_0 : flrwΓ a da x 2 1 0 = 0 := by unfold flrwΓ; simp
  have hΓ_2_1_1 : flrwΓ a da x 2 1 1 = 0 := by unfold flrwΓ; simp
  have hΓ_2_1_2 : flrwΓ a da x 2 1 2 = 0 := by unfold flrwΓ; simp
  have hΓ_2_1_3 : flrwΓ a da x 2 1 3 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_2_2_0, hΓ_0_1_1, hΓ_2_2_1, hΓ_2_2_2, hΓ_2_2_3,
             hΓ_2_1_0, hΓ_2_1_1, hΓ_2_1_2, hΓ_2_1_3,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp

/-- If `a (x 0) ≠ 0`, then `R^3_{131}(x) = da²`. -/
theorem flrwRiemann_3_1_3_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 3 1 3 1 = (da (x 0))^2 := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 3 3 l * flrwΓ a da x l 1 1),
      sumFin4 (fun l => flrwΓ a da x 3 1 l * flrwΓ a da x l 3 1)]
  have h_dΓ_t1 : flrwdΓ a da dda 3 x 3 1 1 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_t2 : flrwdΓ a da dda 1 x 3 3 1 = 0 := by unfold flrwdΓ; simp
  have hΓ_3_3_0 : flrwΓ a da x 3 3 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 3 (by decide)
  have hΓ_0_1_1 : flrwΓ a da x 0 1 1 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 1 (by decide)
  have hΓ_3_3_1 : flrwΓ a da x 3 3 1 = 0 := by unfold flrwΓ; simp
  have hΓ_3_3_2 : flrwΓ a da x 3 3 2 = 0 := by unfold flrwΓ; simp
  have hΓ_3_3_3 : flrwΓ a da x 3 3 3 = 0 := by unfold flrwΓ; simp
  have hΓ_3_1_0 : flrwΓ a da x 3 1 0 = 0 := by unfold flrwΓ; simp
  have hΓ_3_1_1 : flrwΓ a da x 3 1 1 = 0 := by unfold flrwΓ; simp
  have hΓ_3_1_2 : flrwΓ a da x 3 1 2 = 0 := by unfold flrwΓ; simp
  have hΓ_3_1_3 : flrwΓ a da x 3 1 3 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_3_3_0, hΓ_0_1_1, hΓ_3_3_1, hΓ_3_3_2, hΓ_3_3_3,
             hΓ_3_1_0, hΓ_3_1_1, hΓ_3_1_2, hΓ_3_1_3,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp

/-! ## Ricci tensor: time-time component -/

/-- If `a (x 0) ≠ 0`, then `R_{00}(x) = -3 dda/a`. The proof sums `R^ρ_{0ρ0}` over `ρ`, with
`R^0_{000} = 0` by antisymmetry. -/
theorem flrwRicci_0_0 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 0 0 = -3 * dda (x 0) / a (x 0) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 0 ρ 0)]
  -- ρ = 0: R^0_{000} = 0 by antisymmetry in (μ, ν).
  have h0 : (flrwConnection a da dda).riemann x 0 0 0 0 = 0 := by
    have := (flrwConnection a da dda).riemann_antisymm x 0 0 0 0
    linarith
  rw [h0,
      flrwRiemann_1_0_1_0 a da dda x hv,
      flrwRiemann_2_0_2_0 a da dda x hv,
      flrwRiemann_3_0_3_0 a da dda x hv]
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R_{11}(x) = a · dda + 2 da²`. The summands are `R^0_{101} = a · dda`,
`R^2_{121} = R^3_{131} = da²` and `R^1_{111} = 0`. -/
theorem flrwRicci_1_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 1 1
      = a (x 0) * dda (x 0) + 2 * (da (x 0))^2 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 1 ρ 1)]
  -- ρ = 1: R^1_{111} = 0 (antisymmetric in (μ, ν) when μ = ν).
  have h1 : (flrwConnection a da dda).riemann x 1 1 1 1 = 0 := by
    have := (flrwConnection a da dda).riemann_antisymm x 1 1 1 1
    linarith
  rw [h1,
      flrwRiemann_0_1_0_1 a da dda x hv,
      flrwRiemann_2_1_2_1 a da dda x hv,
      flrwRiemann_3_1_3_1 a da dda x hv]
  ring

/-- If `a (x 0) ≠ 0`, then `R^0_{202}(x) = a · dda`. -/
theorem flrwRiemann_0_2_0_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 0 2 0 2 = a (x 0) * dda (x 0) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 2 2),
      sumFin4 (fun l => flrwΓ a da x 0 2 l * flrwΓ a da x l 0 2)]
  have h_dΓ_t1 : flrwdΓ a da dda 0 x 0 2 2 = (da (x 0))^2 + a (x 0) * dda (x 0) :=
    flrwdΓ_0_0_ii a da dda x 2 (by decide)
  have h_dΓ_t2 : flrwdΓ a da dda 2 x 0 0 2 = 0 := by unfold flrwdΓ; simp
  have hΓ_0_0_0 : flrwΓ a da x 0 0 0 = 0 := flrwΓ_0_00 a da x
  have hΓ_0_0_1 : flrwΓ a da x 0 0 1 = 0 := flrwΓ_0_diff a da x 0 1 (by decide)
  have hΓ_0_0_2 : flrwΓ a da x 0 0 2 = 0 := flrwΓ_0_diff a da x 0 2 (by decide)
  have hΓ_0_0_3 : flrwΓ a da x 0 0 3 = 0 := flrwΓ_0_diff a da x 0 3 (by decide)
  have hΓ_0_2_0 : flrwΓ a da x 0 2 0 = 0 := flrwΓ_0_diff a da x 2 0 (by decide)
  have hΓ_0_2_1 : flrwΓ a da x 0 2 1 = 0 := flrwΓ_0_diff a da x 2 1 (by decide)
  have hΓ_0_2_2 : flrwΓ a da x 0 2 2 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 2 (by decide)
  have hΓ_0_2_3 : flrwΓ a da x 0 2 3 = 0 := flrwΓ_0_diff a da x 2 3 (by decide)
  have hΓ_2_0_2 : flrwΓ a da x 2 0 2 = da (x 0) / a (x 0) :=
    flrwΓ_i_0i a da x 2 (by decide)
  have hΓ_1_0_2 : flrwΓ a da x 1 0 2 = 0 := by unfold flrwΓ; simp
  have hΓ_3_0_2 : flrwΓ a da x 3 0 2 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_0_0_0, hΓ_0_0_1, hΓ_0_0_2, hΓ_0_0_3,
             hΓ_0_2_0, hΓ_0_2_1, hΓ_0_2_2, hΓ_0_2_3,
             hΓ_2_0_2, hΓ_1_0_2, hΓ_3_0_2,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R^1_{212}(x) = da²`. -/
theorem flrwRiemann_1_2_1_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 1 2 1 2 = (da (x 0))^2 := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 2 2),
      sumFin4 (fun l => flrwΓ a da x 1 2 l * flrwΓ a da x l 1 2)]
  have h_dΓ_t1 : flrwdΓ a da dda 1 x 1 2 2 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_t2 : flrwdΓ a da dda 2 x 1 1 2 = 0 := by unfold flrwdΓ; simp
  have hΓ_1_1_0 : flrwΓ a da x 1 1 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 1 (by decide)
  have hΓ_0_2_2 : flrwΓ a da x 0 2 2 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 2 (by decide)
  have hΓ_1_1_1 : flrwΓ a da x 1 1 1 = 0 := by unfold flrwΓ; simp
  have hΓ_1_1_2 : flrwΓ a da x 1 1 2 = 0 := by unfold flrwΓ; simp
  have hΓ_1_1_3 : flrwΓ a da x 1 1 3 = 0 := by unfold flrwΓ; simp
  have hΓ_1_2_0 : flrwΓ a da x 1 2 0 = 0 := by unfold flrwΓ; simp
  have hΓ_1_2_1 : flrwΓ a da x 1 2 1 = 0 := by unfold flrwΓ; simp
  have hΓ_1_2_2 : flrwΓ a da x 1 2 2 = 0 := by unfold flrwΓ; simp
  have hΓ_1_2_3 : flrwΓ a da x 1 2 3 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_1_1_0, hΓ_0_2_2, hΓ_1_1_1, hΓ_1_1_2, hΓ_1_1_3,
             hΓ_1_2_0, hΓ_1_2_1, hΓ_1_2_2, hΓ_1_2_3,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp

/-- If `a (x 0) ≠ 0`, then `R^3_{232}(x) = da²`. -/
theorem flrwRiemann_3_2_3_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 3 2 3 2 = (da (x 0))^2 := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 3 3 l * flrwΓ a da x l 2 2),
      sumFin4 (fun l => flrwΓ a da x 3 2 l * flrwΓ a da x l 3 2)]
  have h_dΓ_t1 : flrwdΓ a da dda 3 x 3 2 2 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_t2 : flrwdΓ a da dda 2 x 3 3 2 = 0 := by unfold flrwdΓ; simp
  have hΓ_3_3_0 : flrwΓ a da x 3 3 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 3 (by decide)
  have hΓ_0_2_2 : flrwΓ a da x 0 2 2 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 2 (by decide)
  have hΓ_3_3_1 : flrwΓ a da x 3 3 1 = 0 := by unfold flrwΓ; simp
  have hΓ_3_3_2 : flrwΓ a da x 3 3 2 = 0 := by unfold flrwΓ; simp
  have hΓ_3_3_3 : flrwΓ a da x 3 3 3 = 0 := by unfold flrwΓ; simp
  have hΓ_3_2_0 : flrwΓ a da x 3 2 0 = 0 := by unfold flrwΓ; simp
  have hΓ_3_2_1 : flrwΓ a da x 3 2 1 = 0 := by unfold flrwΓ; simp
  have hΓ_3_2_2 : flrwΓ a da x 3 2 2 = 0 := by unfold flrwΓ; simp
  have hΓ_3_2_3 : flrwΓ a da x 3 2 3 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_3_3_0, hΓ_0_2_2, hΓ_3_3_1, hΓ_3_3_2, hΓ_3_3_3,
             hΓ_3_2_0, hΓ_3_2_1, hΓ_3_2_2, hΓ_3_2_3,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp

/-- If `a (x 0) ≠ 0`, then `R_{22}(x) = a · dda + 2 da²`. -/
theorem flrwRicci_2_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 2 2
      = a (x 0) * dda (x 0) + 2 * (da (x 0))^2 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 2 ρ 2)]
  have h2 : (flrwConnection a da dda).riemann x 2 2 2 2 = 0 := by
    have := (flrwConnection a da dda).riemann_antisymm x 2 2 2 2
    linarith
  rw [h2,
      flrwRiemann_0_2_0_2 a da dda x hv,
      flrwRiemann_1_2_1_2 a da dda x hv,
      flrwRiemann_3_2_3_2 a da dda x hv]
  ring

/-- If `a (x 0) ≠ 0`, then `R^0_{303}(x) = a · dda`. -/
theorem flrwRiemann_0_3_0_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 0 3 0 3 = a (x 0) * dda (x 0) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 3 3),
      sumFin4 (fun l => flrwΓ a da x 0 3 l * flrwΓ a da x l 0 3)]
  have h_dΓ_t1 : flrwdΓ a da dda 0 x 0 3 3 = (da (x 0))^2 + a (x 0) * dda (x 0) :=
    flrwdΓ_0_0_ii a da dda x 3 (by decide)
  have h_dΓ_t2 : flrwdΓ a da dda 3 x 0 0 3 = 0 := by unfold flrwdΓ; simp
  have hΓ_0_0_0 : flrwΓ a da x 0 0 0 = 0 := flrwΓ_0_00 a da x
  have hΓ_0_0_1 : flrwΓ a da x 0 0 1 = 0 := flrwΓ_0_diff a da x 0 1 (by decide)
  have hΓ_0_0_2 : flrwΓ a da x 0 0 2 = 0 := flrwΓ_0_diff a da x 0 2 (by decide)
  have hΓ_0_0_3 : flrwΓ a da x 0 0 3 = 0 := flrwΓ_0_diff a da x 0 3 (by decide)
  have hΓ_0_3_0 : flrwΓ a da x 0 3 0 = 0 := flrwΓ_0_diff a da x 3 0 (by decide)
  have hΓ_0_3_1 : flrwΓ a da x 0 3 1 = 0 := flrwΓ_0_diff a da x 3 1 (by decide)
  have hΓ_0_3_2 : flrwΓ a da x 0 3 2 = 0 := flrwΓ_0_diff a da x 3 2 (by decide)
  have hΓ_0_3_3 : flrwΓ a da x 0 3 3 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 3 (by decide)
  have hΓ_3_0_3 : flrwΓ a da x 3 0 3 = da (x 0) / a (x 0) :=
    flrwΓ_i_0i a da x 3 (by decide)
  have hΓ_1_0_3 : flrwΓ a da x 1 0 3 = 0 := by unfold flrwΓ; simp
  have hΓ_2_0_3 : flrwΓ a da x 2 0 3 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_0_0_0, hΓ_0_0_1, hΓ_0_0_2, hΓ_0_0_3,
             hΓ_0_3_0, hΓ_0_3_1, hΓ_0_3_2, hΓ_0_3_3,
             hΓ_3_0_3, hΓ_1_0_3, hΓ_2_0_3,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R^1_{313}(x) = da²`. -/
theorem flrwRiemann_1_3_1_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 1 3 1 3 = (da (x 0))^2 := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 3 3),
      sumFin4 (fun l => flrwΓ a da x 1 3 l * flrwΓ a da x l 1 3)]
  have h_dΓ_t1 : flrwdΓ a da dda 1 x 1 3 3 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_t2 : flrwdΓ a da dda 3 x 1 1 3 = 0 := by unfold flrwdΓ; simp
  have hΓ_1_1_0 : flrwΓ a da x 1 1 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 1 (by decide)
  have hΓ_0_3_3 : flrwΓ a da x 0 3 3 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 3 (by decide)
  have hΓ_1_1_1 : flrwΓ a da x 1 1 1 = 0 := by unfold flrwΓ; simp
  have hΓ_1_1_2 : flrwΓ a da x 1 1 2 = 0 := by unfold flrwΓ; simp
  have hΓ_1_1_3 : flrwΓ a da x 1 1 3 = 0 := by unfold flrwΓ; simp
  have hΓ_1_3_0 : flrwΓ a da x 1 3 0 = 0 := by unfold flrwΓ; simp
  have hΓ_1_3_1 : flrwΓ a da x 1 3 1 = 0 := by unfold flrwΓ; simp
  have hΓ_1_3_2 : flrwΓ a da x 1 3 2 = 0 := by unfold flrwΓ; simp
  have hΓ_1_3_3 : flrwΓ a da x 1 3 3 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_1_1_0, hΓ_0_3_3, hΓ_1_1_1, hΓ_1_1_2, hΓ_1_1_3,
             hΓ_1_3_0, hΓ_1_3_1, hΓ_1_3_2, hΓ_1_3_3,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp

/-- If `a (x 0) ≠ 0`, then `R^2_{323}(x) = da²`. -/
theorem flrwRiemann_2_3_2_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).riemann x 2 3 2 3 = (da (x 0))^2 := by
  have ha_ne : a (x 0) ≠ 0 := hv
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 2 2 l * flrwΓ a da x l 3 3),
      sumFin4 (fun l => flrwΓ a da x 2 3 l * flrwΓ a da x l 2 3)]
  have h_dΓ_t1 : flrwdΓ a da dda 2 x 2 3 3 = 0 := by unfold flrwdΓ; simp
  have h_dΓ_t2 : flrwdΓ a da dda 3 x 2 2 3 = 0 := by unfold flrwdΓ; simp
  have hΓ_2_2_0 : flrwΓ a da x 2 2 0 = da (x 0) / a (x 0) :=
    flrwΓ_i_i0 a da x 2 (by decide)
  have hΓ_0_3_3 : flrwΓ a da x 0 3 3 = a (x 0) * da (x 0) :=
    flrwΓ_0_ii a da x 3 (by decide)
  have hΓ_2_2_1 : flrwΓ a da x 2 2 1 = 0 := by unfold flrwΓ; simp
  have hΓ_2_2_2 : flrwΓ a da x 2 2 2 = 0 := by unfold flrwΓ; simp
  have hΓ_2_2_3 : flrwΓ a da x 2 2 3 = 0 := by unfold flrwΓ; simp
  have hΓ_2_3_0 : flrwΓ a da x 2 3 0 = 0 := by unfold flrwΓ; simp
  have hΓ_2_3_1 : flrwΓ a da x 2 3 1 = 0 := by unfold flrwΓ; simp
  have hΓ_2_3_2 : flrwΓ a da x 2 3 2 = 0 := by unfold flrwΓ; simp
  have hΓ_2_3_3 : flrwΓ a da x 2 3 3 = 0 := by unfold flrwΓ; simp
  simp only [h_dΓ_t1, h_dΓ_t2, hΓ_2_2_0, hΓ_0_3_3, hΓ_2_2_1, hΓ_2_2_2, hΓ_2_2_3,
             hΓ_2_3_0, hΓ_2_3_1, hΓ_2_3_2, hΓ_2_3_3,
             zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  field_simp

/-- If `a (x 0) ≠ 0`, then `R_{33}(x) = a · dda + 2 da²`. -/
theorem flrwRicci_3_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 3 3
      = a (x 0) * dda (x 0) + 2 * (da (x 0))^2 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 3 ρ 3)]
  have h3 : (flrwConnection a da dda).riemann x 3 3 3 3 = 0 := by
    have := (flrwConnection a da dda).riemann_antisymm x 3 3 3 3
    linarith
  rw [h3,
      flrwRiemann_0_3_0_3 a da dda x hv,
      flrwRiemann_1_3_1_3 a da dda x hv,
      flrwRiemann_2_3_2_3 a da dda x hv]
  ring

/-! ## Scalar curvature and Einstein tensor

The inverse metric `diag(-1, a⁻², a⁻², a⁻²)` is diagonal, so the trace `g^{μν} R_{μν}` uses only
the diagonal Ricci components. -/

/-- The expression `6 dda/a + 6 da²/a²` at time `x 0`. -/
noncomputable def flrwScalarCurvatureClosed (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  6 * dda (x 0) / a (x 0) + 6 * (da (x 0))^2 / (a (x 0))^2

/-- The diagonal trace `-R_{00} + (1/a²)(R_{11} + R_{22} + R_{33})` of the Ricci tensor of
`flrwConnection a da dda`. -/
noncomputable def flrwScalarCurvatureDiag (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -(flrwConnection a da dda).ricci x 0 0
    + (1 / (a (x 0))^2)
        * ((flrwConnection a da dda).ricci x 1 1
          + (flrwConnection a da dda).ricci x 2 2
          + (flrwConnection a da dda).ricci x 3 3)

/-- If `a (x 0) ≠ 0`, then `flrwScalarCurvatureDiag a da dda x = 6 dda/a + 6 da²/a²`. -/
theorem flrwScalarCurvatureDiag_eq (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    flrwScalarCurvatureDiag a da dda x = flrwScalarCurvatureClosed a da dda x := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  unfold flrwScalarCurvatureDiag flrwScalarCurvatureClosed
  rw [flrwRicci_0_0 a da dda x hv,
      flrwRicci_1_1 a da dda x hv,
      flrwRicci_2_2 a da dda x hv,
      flrwRicci_3_3 a da dda x hv]
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R_{00} - ½ R · (-1) = 3 da²/a²`, with `R` given by
`flrwScalarCurvatureClosed`. -/
theorem flrwEinstein_0_0 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 0 0
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (-1)
      = 3 * (da (x 0))^2 / (a (x 0))^2 := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  rw [flrwRicci_0_0 a da dda x hv]
  unfold flrwScalarCurvatureClosed
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R_{11} - ½ R · a² = -(2 a · dda + da²)`, with `R` given by
`flrwScalarCurvatureClosed`. -/
theorem flrwEinstein_1_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 1 1
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (a (x 0))^2
      = -(2 * a (x 0) * dda (x 0) + (da (x 0))^2) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  rw [flrwRicci_1_1 a da dda x hv]
  unfold flrwScalarCurvatureClosed
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R_{22} - ½ R · a² = -(2 a · dda + da²)`. -/
theorem flrwEinstein_2_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 2 2
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (a (x 0))^2
      = -(2 * a (x 0) * dda (x 0) + (da (x 0))^2) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  rw [flrwRicci_2_2 a da dda x hv]
  unfold flrwScalarCurvatureClosed
  field_simp
  ring

/-- If `a (x 0) ≠ 0`, then `R_{33} - ½ R · a² = -(2 a · dda + da²)`. -/
theorem flrwEinstein_3_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    (flrwConnection a da dda).ricci x 3 3
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (a (x 0))^2
      = -(2 * a (x 0) * dda (x 0) + (da (x 0))^2) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  rw [flrwRicci_3_3 a da dda x hv]
  unfold flrwScalarCurvatureClosed
  field_simp
  ring

/-! ## Perfect-fluid stress-energy and the Friedmann equations -/

/-- The diagonal tensor with `T_{00} = ρ`, `T_{ii} = p · a²` for `i ∈ {1, 2, 3}`, and zero
off-diagonal entries, evaluated at time `x 0`. -/
noncomputable def flrwPerfectFluidT (a ρ p : ℝ → ℝ) (x : Fin 4 → ℝ)
    (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else if μ = 0 then ρ (x 0)
  else p (x 0) * (a (x 0))^2

/-- `3 da²/a² = κ ρ + Λ` at time `t`. -/
def flrwFriedmann1 (a da : ℝ → ℝ) (ρ : ℝ → ℝ) (Λ κ : ℝ) (t : ℝ) : Prop :=
  3 * (da t)^2 / (a t)^2 = κ * ρ t + Λ

/-- `2 dda/a + da²/a² = -κ p + Λ` at time `t`. -/
def flrwFriedmann2 (a da dda : ℝ → ℝ) (p : ℝ → ℝ) (Λ κ : ℝ) (t : ℝ) : Prop :=
  2 * dda t / a t + (da t)^2 / (a t)^2 = -(κ * p t) + Λ

/-- If `a (x 0) ≠ 0`, then `R_{00} - ½ R · (-1) + Λ · (-1) = κ T_{00}` holds if and only if
`flrwFriedmann1` holds at `x 0`. -/
theorem flrwEinstein_00_iff_friedmann1
    (a da dda ρ p : ℝ → ℝ) (Λ κ : ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    ((flrwConnection a da dda).ricci x 0 0
      - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (-1 : ℝ)
      + Λ * (-1 : ℝ)
      = κ * flrwPerfectFluidT a ρ p x 0 0)
    ↔ flrwFriedmann1 a da ρ Λ κ (x 0) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  rw [flrwEinstein_0_0 a da dda x hv]
  unfold flrwPerfectFluidT flrwFriedmann1
  simp
  constructor
  · intro h; linarith
  · intro h; linarith

/-- If `a (x 0) ≠ 0`, then `R_{11} - ½ R · a² + Λ · a² = κ T_{11}` holds if and only if
`flrwFriedmann2` holds at `x 0`. -/
theorem flrwEinstein_11_iff_friedmann2
    (a da dda ρ p : ℝ → ℝ) (Λ κ : ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    ((flrwConnection a da dda).ricci x 1 1
      - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (a (x 0))^2
      + Λ * (a (x 0))^2
      = κ * flrwPerfectFluidT a ρ p x 1 1)
    ↔ flrwFriedmann2 a da dda p Λ κ (x 0) := by
  have ha_ne : a (x 0) ≠ 0 := hv
  have ha_sq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero _ ha_ne
  have ha_sq_pos : 0 < (a (x 0))^2 := by positivity
  rw [flrwEinstein_1_1 a da dda x hv]
  unfold flrwPerfectFluidT flrwFriedmann2
  -- The if-then-else simplifies to the spatial branch (μ = ν = 1).
  show -(2 * a (x 0) * dda (x 0) + (da (x 0))^2) + Λ * (a (x 0))^2
       = κ * (if (1 : Fin 4) ≠ 1 then 0
              else if (1 : Fin 4) = 0 then ρ (x 0)
              else p (x 0) * (a (x 0))^2)
       ↔ 2 * dda (x 0) / a (x 0) + (da (x 0))^2 / (a (x 0))^2
         = -(κ * p (x 0)) + Λ
  simp only [show ((1 : Fin 4) ≠ 1) = False from by decide,
             show ((1 : Fin 4) = 0) = False from by decide,
             if_false]
  -- Now goal is: -(2 a a'' + (a')²) + Λ a² = κ (p a²) ↔ 2 a''/a + (a')²/a² = -κ p + Λ.
  -- Both sides are equivalent to: 2 a''/a + (a')²/a² + κ p = Λ.
  constructor
  · intro h
    -- From h: -(2 a a'' + (a')²) + Λ a² = κ p a²
    -- ⟹ 2 a a'' + (a')² = (Λ - κ p) a²
    have hreorg : 2 * a (x 0) * dda (x 0) + (da (x 0))^2
        = (Λ - κ * p (x 0)) * (a (x 0))^2 := by linarith
    -- Divide by a²: (2 a a'' + (a')²)/a² = Λ - κ p.
    have hdivd : (2 * a (x 0) * dda (x 0) + (da (x 0))^2) / (a (x 0))^2
        = Λ - κ * p (x 0) := by
      rw [hreorg]; field_simp
    -- Split the fraction: 2 a a''/a² + (a')²/a² = 2 a''/a + (a')²/a².
    have hsplit : (2 * a (x 0) * dda (x 0) + (da (x 0))^2) / (a (x 0))^2
        = 2 * dda (x 0) / a (x 0) + (da (x 0))^2 / (a (x 0))^2 := by
      field_simp
    linarith
  · intro h
    -- From h: 2 a''/a + (a')²/a² = -κ p + Λ
    -- Combine fractions: (2 a a'' + (a')²)/a² = Λ - κ p.
    have hsplit : 2 * dda (x 0) / a (x 0) + (da (x 0))^2 / (a (x 0))^2
        = (2 * a (x 0) * dda (x 0) + (da (x 0))^2) / (a (x 0))^2 := by
      field_simp
    have hcombined : (2 * a (x 0) * dda (x 0) + (da (x 0))^2) / (a (x 0))^2
        = -(κ * p (x 0)) + Λ := by linarith
    -- Multiply by a² ≠ 0.
    have hmul : 2 * a (x 0) * dda (x 0) + (da (x 0))^2
        = (-(κ * p (x 0)) + Λ) * (a (x 0))^2 := by
      rw [← hcombined]; field_simp
    linarith

/-! ## Off-diagonal Ricci components

This section proves `R_{μν}(x) = 0` for `μ < ν`. Each entry is a sum of four Riemann components,
and each of these is shown to be zero. -/

/-- `flrwΓ a da x ρ ρ 1 = 0` for every `ρ`. -/
private theorem flrwΓ_ρ_ρ_1 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) (ρ : Fin 4) :
    flrwΓ a da x ρ ρ 1 = 0 := by
  fin_cases ρ <;> (unfold flrwΓ; simp)

/-- `flrwΓ a da x l 1 0 = 0` for `l ≠ 1`. -/
private theorem flrwΓ_l_1_0_zero (a da : ℝ → ℝ) (x : Fin 4 → ℝ)
    (l : Fin 4) (h : l ≠ 1) :
    flrwΓ a da x l 1 0 = 0 := by
  fin_cases l
  · unfold flrwΓ; simp
  · exact absurd rfl h
  · unfold flrwΓ; simp
  · unfold flrwΓ; simp


/-- `R^0_{001}(x) = 0`. -/
private theorem flrwRiemann_0_0_0_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 0 0 0 1 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 1 0),
      sumFin4 (fun l => flrwΓ a da x 0 1 l * flrwΓ a da x l 0 0)]
  -- All Γ_x_0_0_l vanish (μ=0, ν=l with ρ=0, condition False except diagonal which is also 0).
  have h00_l : ∀ l : Fin 4, flrwΓ a da x 0 0 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  -- All Γ_x_l_0_0 vanish (handled by flrwΓ_l_00).
  have d1 : flrwdΓ a da dda 0 x 0 1 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 1 x 0 0 0 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [h00_l, flrwΓ_l_00]

/-- `R^1_{011}(x) = 0`, by antisymmetry in the last two indices. -/
private theorem flrwRiemann_1_0_1_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 1 0 1 1 = 0 := by
  have := (flrwConnection a da dda).riemann_antisymm x 1 0 1 1
  linarith

/-- `R^2_{021}(x) = 0`. -/
private theorem flrwRiemann_2_0_2_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 2 0 2 1 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 2 2 l * flrwΓ a da x l 1 0),
      sumFin4 (fun l => flrwΓ a da x 2 1 l * flrwΓ a da x l 2 0)]
  have d1 : flrwdΓ a da dda 2 x 2 1 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 1 x 2 2 0 = 0 := by unfold flrwdΓ; simp
  -- Γ_2_2_l: l=0 gives a'/a; l=1,2,3 give 0.
  have h22_1 : flrwΓ a da x 2 2 1 = 0 := by unfold flrwΓ; simp
  have h22_2 : flrwΓ a da x 2 2 2 = 0 := by unfold flrwΓ; simp
  have h22_3 : flrwΓ a da x 2 2 3 = 0 := by unfold flrwΓ; simp
  -- Γ_l_1_0: l=1 gives a'/a; l=0,2,3 give 0.
  have h_l_1_0_0 : flrwΓ a da x 0 1 0 = 0 := flrwΓ_0_diff a da x 1 0 (by decide)
  have h_l_1_0_2 : flrwΓ a da x 2 1 0 = 0 := by unfold flrwΓ; simp
  have h_l_1_0_3 : flrwΓ a da x 3 1 0 = 0 := by unfold flrwΓ; simp
  -- Γ_2_1_l: all vanish (ρ=2, μ=1, conditions need μ=0 or ν=0 with the right partner).
  have h21_l : ∀ l : Fin 4, flrwΓ a da x 2 1 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  rw [d1, d2, h22_1, h22_2, h22_3, h_l_1_0_0, h_l_1_0_2, h_l_1_0_3]
  simp [h21_l, flrwΓ_l_00]

/-- `R^3_{031}(x) = 0`. -/
private theorem flrwRiemann_3_0_3_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 3 0 3 1 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 3 3 l * flrwΓ a da x l 1 0),
      sumFin4 (fun l => flrwΓ a da x 3 1 l * flrwΓ a da x l 3 0)]
  have d1 : flrwdΓ a da dda 3 x 3 1 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 1 x 3 3 0 = 0 := by unfold flrwdΓ; simp
  have h33_1 : flrwΓ a da x 3 3 1 = 0 := by unfold flrwΓ; simp
  have h33_2 : flrwΓ a da x 3 3 2 = 0 := by unfold flrwΓ; simp
  have h33_3 : flrwΓ a da x 3 3 3 = 0 := by unfold flrwΓ; simp
  have h_l_1_0_0 : flrwΓ a da x 0 1 0 = 0 := flrwΓ_0_diff a da x 1 0 (by decide)
  have h_l_1_0_2 : flrwΓ a da x 2 1 0 = 0 := by unfold flrwΓ; simp
  have h_l_1_0_3 : flrwΓ a da x 3 1 0 = 0 := by unfold flrwΓ; simp
  have h31_l : ∀ l : Fin 4, flrwΓ a da x 3 1 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  rw [d1, d2, h33_1, h33_2, h33_3, h_l_1_0_0, h_l_1_0_2, h_l_1_0_3]
  simp [h31_l, flrwΓ_l_00]

/-- `R_{01}(x) = 0`. -/
theorem flrwRicci_0_1 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).ricci x 0 1 = 0 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 0 ρ 1)]
  rw [flrwRiemann_0_0_0_1, flrwRiemann_1_0_1_1, flrwRiemann_2_0_2_1, flrwRiemann_3_0_3_1]
  ring

/-! The remaining off-diagonal Ricci components are proved in the same way as `flrwRicci_0_1`. -/

/-- `R^0_{002}(x) = 0`. -/
private theorem flrwRiemann_0_0_0_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 0 0 0 2 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 2 0),
      sumFin4 (fun l => flrwΓ a da x 0 2 l * flrwΓ a da x l 0 0)]
  have h00_l : ∀ l : Fin 4, flrwΓ a da x 0 0 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 0 x 0 2 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 2 x 0 0 0 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [h00_l, flrwΓ_l_00]

private theorem flrwRiemann_0_0_0_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 0 0 0 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 3 0),
      sumFin4 (fun l => flrwΓ a da x 0 3 l * flrwΓ a da x l 0 0)]
  have h00_l : ∀ l : Fin 4, flrwΓ a da x 0 0 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 0 x 0 3 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 0 0 0 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [h00_l, flrwΓ_l_00]

private theorem flrwRiemann_1_0_1_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 1 0 1 2 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 2 0),
      sumFin4 (fun l => flrwΓ a da x 1 2 l * flrwΓ a da x l 1 0)]
  have d1 : flrwdΓ a da dda 1 x 1 2 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 2 x 1 1 0 = 0 := by unfold flrwdΓ; simp
  have h12_l : ∀ l : Fin 4, flrwΓ a da x 1 2 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  -- Sum 1 entries: Γ_1_1_l for l = 0 → a'/a (i_i0); l = 1, 2, 3 → 0.
  have h11_1 : flrwΓ a da x 1 1 1 = 0 := by unfold flrwΓ; simp
  have h11_2 : flrwΓ a da x 1 1 2 = 0 := by unfold flrwΓ; simp
  have h11_3 : flrwΓ a da x 1 1 3 = 0 := by unfold flrwΓ; simp
  -- Γ_l_2_0: l=0 → 0; l=1 → 0; l=2 → a'/a; l=3 → 0.
  have h_0_2_0 : flrwΓ a da x 0 2 0 = 0 := flrwΓ_0_diff a da x 2 0 (by decide)
  have h_1_2_0 : flrwΓ a da x 1 2 0 = 0 := by unfold flrwΓ; simp
  have h_3_2_0 : flrwΓ a da x 3 2 0 = 0 := by unfold flrwΓ; simp
  rw [d1, d2, h11_1, h11_2, h11_3, h_0_2_0, h_1_2_0, h_3_2_0]
  simp [h12_l, flrwΓ_l_00]

private theorem flrwRiemann_2_0_2_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 2 0 2 2 = 0 := by
  have := (flrwConnection a da dda).riemann_antisymm x 2 0 2 2
  linarith

private theorem flrwRiemann_3_0_3_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 3 0 3 2 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 3 3 l * flrwΓ a da x l 2 0),
      sumFin4 (fun l => flrwΓ a da x 3 2 l * flrwΓ a da x l 3 0)]
  have d1 : flrwdΓ a da dda 3 x 3 2 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 2 x 3 3 0 = 0 := by unfold flrwdΓ; simp
  have h32_l : ∀ l : Fin 4, flrwΓ a da x 3 2 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h33_1 : flrwΓ a da x 3 3 1 = 0 := by unfold flrwΓ; simp
  have h33_2 : flrwΓ a da x 3 3 2 = 0 := by unfold flrwΓ; simp
  have h33_3 : flrwΓ a da x 3 3 3 = 0 := by unfold flrwΓ; simp
  have h_0_2_0 : flrwΓ a da x 0 2 0 = 0 := flrwΓ_0_diff a da x 2 0 (by decide)
  have h_1_2_0 : flrwΓ a da x 1 2 0 = 0 := by unfold flrwΓ; simp
  have h_3_2_0 : flrwΓ a da x 3 2 0 = 0 := by unfold flrwΓ; simp
  rw [d1, d2, h33_1, h33_2, h33_3, h_0_2_0, h_1_2_0, h_3_2_0]
  simp [h32_l, flrwΓ_l_00]

/-- `R_{02}(x) = 0`. -/
theorem flrwRicci_0_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).ricci x 0 2 = 0 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 0 ρ 2)]
  rw [flrwRiemann_0_0_0_2, flrwRiemann_1_0_1_2, flrwRiemann_2_0_2_2, flrwRiemann_3_0_3_2]
  ring

private theorem flrwRiemann_1_0_1_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 1 0 1 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 3 0),
      sumFin4 (fun l => flrwΓ a da x 1 3 l * flrwΓ a da x l 1 0)]
  have d1 : flrwdΓ a da dda 1 x 1 3 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 1 1 0 = 0 := by unfold flrwdΓ; simp
  have h13_l : ∀ l : Fin 4, flrwΓ a da x 1 3 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h11_1 : flrwΓ a da x 1 1 1 = 0 := by unfold flrwΓ; simp
  have h11_2 : flrwΓ a da x 1 1 2 = 0 := by unfold flrwΓ; simp
  have h11_3 : flrwΓ a da x 1 1 3 = 0 := by unfold flrwΓ; simp
  have h_0_3_0 : flrwΓ a da x 0 3 0 = 0 := flrwΓ_0_diff a da x 3 0 (by decide)
  have h_1_3_0 : flrwΓ a da x 1 3 0 = 0 := by unfold flrwΓ; simp
  have h_2_3_0 : flrwΓ a da x 2 3 0 = 0 := by unfold flrwΓ; simp
  rw [d1, d2, h11_1, h11_2, h11_3, h_0_3_0, h_1_3_0, h_2_3_0]
  simp [h13_l, flrwΓ_l_00]

private theorem flrwRiemann_2_0_2_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 2 0 2 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 2 2 l * flrwΓ a da x l 3 0),
      sumFin4 (fun l => flrwΓ a da x 2 3 l * flrwΓ a da x l 2 0)]
  have d1 : flrwdΓ a da dda 2 x 2 3 0 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 2 2 0 = 0 := by unfold flrwdΓ; simp
  have h23_l : ∀ l : Fin 4, flrwΓ a da x 2 3 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h22_1 : flrwΓ a da x 2 2 1 = 0 := by unfold flrwΓ; simp
  have h22_2 : flrwΓ a da x 2 2 2 = 0 := by unfold flrwΓ; simp
  have h22_3 : flrwΓ a da x 2 2 3 = 0 := by unfold flrwΓ; simp
  have h_0_3_0 : flrwΓ a da x 0 3 0 = 0 := flrwΓ_0_diff a da x 3 0 (by decide)
  have h_1_3_0 : flrwΓ a da x 1 3 0 = 0 := by unfold flrwΓ; simp
  have h_2_3_0 : flrwΓ a da x 2 3 0 = 0 := by unfold flrwΓ; simp
  rw [d1, d2, h22_1, h22_2, h22_3, h_0_3_0, h_1_3_0, h_2_3_0]
  simp [h23_l, flrwΓ_l_00]

private theorem flrwRiemann_3_0_3_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 3 0 3 3 = 0 := by
  have := (flrwConnection a da dda).riemann_antisymm x 3 0 3 3
  linarith

/-- `R_{03}(x) = 0`. -/
theorem flrwRicci_0_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).ricci x 0 3 = 0 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 0 ρ 3)]
  rw [flrwRiemann_0_0_0_3, flrwRiemann_1_0_1_3, flrwRiemann_2_0_2_3, flrwRiemann_3_0_3_3]
  ring

private theorem flrwRiemann_0_1_0_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 0 1 0 2 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 2 1),
      sumFin4 (fun l => flrwΓ a da x 0 2 l * flrwΓ a da x l 0 1)]
  have h00_l : ∀ l : Fin 4, flrwΓ a da x 0 0 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  -- `Γ^l_{01}` is non-zero only for `l = 1`, and `Γ^0_{2l}` is non-zero only for `l = 2`, so
  -- every product in the second sum is zero.
  have h_0_2_0 : flrwΓ a da x 0 2 0 = 0 := flrwΓ_0_diff a da x 2 0 (by decide)
  have h_0_2_1 : flrwΓ a da x 0 2 1 = 0 := flrwΓ_0_diff a da x 2 1 (by decide)
  have h_0_2_2 : flrwΓ a da x 0 2 2 = a (x 0) * da (x 0) := flrwΓ_0_ii a da x 2 (by decide)
  have h_0_2_3 : flrwΓ a da x 0 2 3 = 0 := flrwΓ_0_diff a da x 2 3 (by decide)
  -- Γ_x_2_0_1 (l=2 case in Sum 2): ρ=2, μ=0, ν=1: condition (μ=0∧ν=ρ)=(0=0∧1=2)=F; (μ=ρ∧ν=0)=(0=2∧1=0)=F. So 0.
  have h_2_0_1 : flrwΓ a da x 2 0 1 = 0 := by unfold flrwΓ; simp
  have d1 : flrwdΓ a da dda 0 x 0 2 1 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 2 x 0 0 1 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2, h_0_2_0, h_0_2_1, h_0_2_2, h_0_2_3, h_2_0_1]
  simp [h00_l]

private theorem flrwRiemann_1_1_1_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 1 1 1 2 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 2 1),
      sumFin4 (fun l => flrwΓ a da x 1 2 l * flrwΓ a da x l 1 1)]
  -- All Γ_x_l_2_1 = 0.
  have hl21 : ∀ l : Fin 4, flrwΓ a da x l 2 1 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  -- All Γ_x_1_2_l = 0 (ρ=1, μ=2, conditions fail).
  have h12_l : ∀ l : Fin 4, flrwΓ a da x 1 2 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 1 x 1 2 1 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 2 x 1 1 1 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [hl21, h12_l]

private theorem flrwRiemann_2_1_2_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 2 1 2 2 = 0 := by
  have := (flrwConnection a da dda).riemann_antisymm x 2 1 2 2
  linarith

private theorem flrwRiemann_3_1_3_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 3 1 3 2 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 3 3 l * flrwΓ a da x l 2 1),
      sumFin4 (fun l => flrwΓ a da x 3 2 l * flrwΓ a da x l 3 1)]
  have hl21 : ∀ l : Fin 4, flrwΓ a da x l 2 1 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have hl31 : ∀ l : Fin 4, flrwΓ a da x l 3 1 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h32_l : ∀ l : Fin 4, flrwΓ a da x 3 2 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 3 x 3 2 1 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 2 x 3 3 1 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [hl21, hl31, h32_l]

/-- `R_{12}(x) = 0`. -/
theorem flrwRicci_1_2 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).ricci x 1 2 = 0 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 1 ρ 2)]
  rw [flrwRiemann_0_1_0_2, flrwRiemann_1_1_1_2, flrwRiemann_2_1_2_2, flrwRiemann_3_1_3_2]
  ring

private theorem flrwRiemann_0_1_0_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 0 1 0 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 3 1),
      sumFin4 (fun l => flrwΓ a da x 0 3 l * flrwΓ a da x l 0 1)]
  have h00_l : ∀ l : Fin 4, flrwΓ a da x 0 0 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h_0_3_0 : flrwΓ a da x 0 3 0 = 0 := flrwΓ_0_diff a da x 3 0 (by decide)
  have h_0_3_1 : flrwΓ a da x 0 3 1 = 0 := flrwΓ_0_diff a da x 3 1 (by decide)
  have h_0_3_2 : flrwΓ a da x 0 3 2 = 0 := flrwΓ_0_diff a da x 3 2 (by decide)
  have h_0_3_3 : flrwΓ a da x 0 3 3 = a (x 0) * da (x 0) := flrwΓ_0_ii a da x 3 (by decide)
  have h_3_0_1 : flrwΓ a da x 3 0 1 = 0 := by unfold flrwΓ; simp
  have d1 : flrwdΓ a da dda 0 x 0 3 1 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 0 0 1 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2, h_0_3_0, h_0_3_1, h_0_3_2, h_0_3_3, h_3_0_1]
  simp [h00_l]

private theorem flrwRiemann_1_1_1_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 1 1 1 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 3 1),
      sumFin4 (fun l => flrwΓ a da x 1 3 l * flrwΓ a da x l 1 1)]
  have hl31 : ∀ l : Fin 4, flrwΓ a da x l 3 1 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h13_l : ∀ l : Fin 4, flrwΓ a da x 1 3 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 1 x 1 3 1 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 1 1 1 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [hl31, h13_l]

private theorem flrwRiemann_2_1_2_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 2 1 2 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 2 2 l * flrwΓ a da x l 3 1),
      sumFin4 (fun l => flrwΓ a da x 2 3 l * flrwΓ a da x l 2 1)]
  have hl31 : ∀ l : Fin 4, flrwΓ a da x l 3 1 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have hl21 : ∀ l : Fin 4, flrwΓ a da x l 2 1 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h23_l : ∀ l : Fin 4, flrwΓ a da x 2 3 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 2 x 2 3 1 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 2 2 1 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [hl31, hl21, h23_l]

private theorem flrwRiemann_3_1_3_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 3 1 3 3 = 0 := by
  have := (flrwConnection a da dda).riemann_antisymm x 3 1 3 3
  linarith

/-- `R_{13}(x) = 0`. -/
theorem flrwRicci_1_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).ricci x 1 3 = 0 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 1 ρ 3)]
  rw [flrwRiemann_0_1_0_3, flrwRiemann_1_1_1_3, flrwRiemann_2_1_2_3, flrwRiemann_3_1_3_3]
  ring

private theorem flrwRiemann_0_2_0_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 0 2 0 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 0 0 l * flrwΓ a da x l 3 2),
      sumFin4 (fun l => flrwΓ a da x 0 3 l * flrwΓ a da x l 0 2)]
  have h00_l : ∀ l : Fin 4, flrwΓ a da x 0 0 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h_0_3_0 : flrwΓ a da x 0 3 0 = 0 := flrwΓ_0_diff a da x 3 0 (by decide)
  have h_0_3_1 : flrwΓ a da x 0 3 1 = 0 := flrwΓ_0_diff a da x 3 1 (by decide)
  have h_0_3_2 : flrwΓ a da x 0 3 2 = 0 := flrwΓ_0_diff a da x 3 2 (by decide)
  have h_0_3_3 : flrwΓ a da x 0 3 3 = a (x 0) * da (x 0) := flrwΓ_0_ii a da x 3 (by decide)
  have h_3_0_2 : flrwΓ a da x 3 0 2 = 0 := by unfold flrwΓ; simp
  have d1 : flrwdΓ a da dda 0 x 0 3 2 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 0 0 2 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2, h_0_3_0, h_0_3_1, h_0_3_2, h_0_3_3, h_3_0_2]
  simp [h00_l]

private theorem flrwRiemann_1_2_1_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 1 2 1 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 1 1 l * flrwΓ a da x l 3 2),
      sumFin4 (fun l => flrwΓ a da x 1 3 l * flrwΓ a da x l 1 2)]
  have hl32 : ∀ l : Fin 4, flrwΓ a da x l 3 2 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h13_l : ∀ l : Fin 4, flrwΓ a da x 1 3 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 1 x 1 3 2 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 1 1 2 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [hl32, h13_l]

private theorem flrwRiemann_2_2_2_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 2 2 2 3 = 0 := by
  unfold ConnectionData.riemann flrwConnection
  simp only
  rw [sumFin4 (fun l => flrwΓ a da x 2 2 l * flrwΓ a da x l 3 2),
      sumFin4 (fun l => flrwΓ a da x 2 3 l * flrwΓ a da x l 2 2)]
  have hl32 : ∀ l : Fin 4, flrwΓ a da x l 3 2 = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have h23_l : ∀ l : Fin 4, flrwΓ a da x 2 3 l = 0 := by
    intro l; fin_cases l <;> (unfold flrwΓ; simp)
  have d1 : flrwdΓ a da dda 2 x 2 3 2 = 0 := by unfold flrwdΓ; simp
  have d2 : flrwdΓ a da dda 3 x 2 2 2 = 0 := by unfold flrwdΓ; simp
  rw [d1, d2]
  simp [hl32, h23_l]

private theorem flrwRiemann_3_2_3_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).riemann x 3 2 3 3 = 0 := by
  have := (flrwConnection a da dda).riemann_antisymm x 3 2 3 3
  linarith

/-- `R_{23}(x) = 0`. -/
theorem flrwRicci_2_3 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwConnection a da dda).ricci x 2 3 = 0 := by
  unfold ConnectionData.ricci
  rw [sumFin4 (fun ρ => (flrwConnection a da dda).riemann x ρ 2 ρ 3)]
  rw [flrwRiemann_0_2_0_3, flrwRiemann_1_2_1_3, flrwRiemann_2_2_2_3, flrwRiemann_3_2_3_3]
  ring

/-- If `a (x 0) ≠ 0`, the `00` and `11` components of `G_{μν} + Λ g_{μν} = κ T_{μν}` with
perfect-fluid `T` hold together if and only if `flrwFriedmann1` and `flrwFriedmann2` hold at
`x 0`. The `22` and `33` components are not part of the statement. -/
theorem flrwEFE_diag_iff_friedmann
    (a da dda ρ p : ℝ → ℝ) (Λ κ : ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    ((flrwConnection a da dda).ricci x 0 0
      - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (-1 : ℝ)
      + Λ * (-1 : ℝ)
      = κ * flrwPerfectFluidT a ρ p x 0 0)
    ∧ ((flrwConnection a da dda).ricci x 1 1
      - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (a (x 0))^2
      + Λ * (a (x 0))^2
      = κ * flrwPerfectFluidT a ρ p x 1 1)
    ↔ flrwFriedmann1 a da ρ Λ κ (x 0)
      ∧ flrwFriedmann2 a da dda p Λ κ (x 0) := by
  rw [flrwEinstein_00_iff_friedmann1 a da dda ρ p Λ κ x hv,
      flrwEinstein_11_iff_friedmann2 a da dda ρ p Λ κ x hv]

/-! ## The two directions of `flrwEFE_diag_iff_friedmann` -/

/-- If `a (x 0) ≠ 0` and the Friedmann pair holds at `x 0`, then the `00` and `11` components of
`G_{μν} + Λ g_{μν} = κ T_{μν}` hold for `flrwConnection a da dda` with
`T = flrwPerfectFluidT a ρ p`. -/
theorem flrw_satisfies_EFE_00_11_of_friedmann
    (a da dda ρ p : ℝ → ℝ) (Λ κ : ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x)
    (hF1 : flrwFriedmann1 a da ρ Λ κ (x 0))
    (hF2 : flrwFriedmann2 a da dda p Λ κ (x 0)) :
    (flrwConnection a da dda).ricci x 0 0
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (-1 : ℝ)
        + Λ * (-1 : ℝ)
      = κ * flrwPerfectFluidT a ρ p x 0 0
    ∧ (flrwConnection a da dda).ricci x 1 1
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (a (x 0))^2
        + Λ * (a (x 0))^2
      = κ * flrwPerfectFluidT a ρ p x 1 1 :=
  (flrwEFE_diag_iff_friedmann a da dda ρ p Λ κ x hv).mpr ⟨hF1, hF2⟩

/-- If `a (x 0) ≠ 0` and the `00` and `11` components of `G_{μν} + Λ g_{μν} = κ T_{μν}` hold,
then the Friedmann pair holds at `x 0`. -/
theorem flrw_friedmann_of_EFE
    (a da dda ρ p : ℝ → ℝ) (Λ κ : ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x)
    (hEFE : (flrwConnection a da dda).ricci x 0 0
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (-1 : ℝ)
        + Λ * (-1 : ℝ)
      = κ * flrwPerfectFluidT a ρ p x 0 0
    ∧ (flrwConnection a da dda).ricci x 1 1
        - (1 / 2) * flrwScalarCurvatureClosed a da dda x * (a (x 0))^2
        + Λ * (a (x 0))^2
      = κ * flrwPerfectFluidT a ρ p x 1 1) :
    flrwFriedmann1 a da ρ Λ κ (x 0)
    ∧ flrwFriedmann2 a da dda p Λ κ (x 0) :=
  (flrwEFE_diag_iff_friedmann a da dda ρ p Λ κ x hv).mp hEFE

/-! ### Vacuum and matter-dominated specializations -/

/-- With `ρ = p = 0`, the Friedmann pair at `t` is equivalent to `3 da²/a² = Λ` and
`2 dda/a + da²/a² = Λ`. -/
theorem flrw_vacuum_friedmann_iff
    (a da dda : ℝ → ℝ) (Λ κ : ℝ) (t : ℝ) :
    (flrwFriedmann1 a da (fun _ => 0) Λ κ t
      ∧ flrwFriedmann2 a da dda (fun _ => 0) Λ κ t)
    ↔ (3 * (da t)^2 / (a t)^2 = Λ
      ∧ 2 * dda t / a t + (da t)^2 / (a t)^2 = Λ) := by
  unfold flrwFriedmann1 flrwFriedmann2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · linarith
    · linarith

/-- With `p = 0`, the Friedmann pair at `t` is equivalent to `3 da²/a² = κ ρ + Λ` and
`2 dda/a + da²/a² = Λ`. -/
theorem flrw_dust_friedmann_iff
    (a da dda ρ : ℝ → ℝ) (Λ κ : ℝ) (t : ℝ) :
    (flrwFriedmann1 a da ρ Λ κ t
      ∧ flrwFriedmann2 a da dda (fun _ => 0) Λ κ t)
    ↔ (3 * (da t)^2 / (a t)^2 = κ * ρ t + Λ
      ∧ 2 * dda t / a t + (da t)^2 / (a t)^2 = Λ) := by
  unfold flrwFriedmann1 flrwFriedmann2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩

end Curvature
end InfraFormalization
