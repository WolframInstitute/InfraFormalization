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

@[simp] theorem flrwdΓ_0_i_i0 (a da dda : ℝ → ℝ) (x : Fin 4 → ℝ)
    (i : Fin 4) (hi : i ≠ 0) :
    flrwdΓ a da dda 0 x i i 0
      = (a (x 0) * dda (x 0) - (da (x 0))^2) / (a (x 0))^2 := by
  unfold flrwdΓ
  simp [hi]

/-- **Sum over `Fin 4`** unfolds explicitly: `∑ l : Fin 4, f l = f 0 + f 1 + f 2 + f 3`. -/
private theorem sumFin4 {β : Type*} [AddCommMonoid β] (f : Fin 4 → β) :
    ∑ l : Fin 4, f l = f 0 + f 1 + f 2 + f 3 := by
  show ∑ l ∈ (Finset.univ : Finset (Fin 4)), f l = f 0 + f 1 + f 2 + f 3
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} from by decide]
  simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, add_assoc]

/-- All Γ entries with `μ = ν = 0` vanish. -/
@[simp] theorem flrwΓ_l_00 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) (l : Fin 4) :
    flrwΓ a da x l 0 0 = 0 := by
  by_cases hl : l = 0
  · subst hl; rfl
  · unfold flrwΓ
    have h_ne_l : (0 : Fin 4) ≠ l := fun h => hl h.symm
    simp [hl, h_ne_l]

/-! ## Riemann components: time-time direction -/

/-- **`R^1_{010}(x) = -a''(t)/a(t)`** on FLRW (assuming `a(t) ≠ 0`).
The first non-vanishing Riemann component on a non-flat FLRW spacetime;
each spatial direction `i ∈ {1,2,3}` gives the same value. -/
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

/-- **`R^2_{020}(x) = -a''(t)/a(t)`** on FLRW (assuming `a(t) ≠ 0`).
By spatial isotropy, same form as `flrwRiemann_1_0_1_0`. -/
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

/-- **`R^3_{030}(x) = -a''(t)/a(t)`** on FLRW (assuming `a(t) ≠ 0`).
By spatial isotropy, same form as `flrwRiemann_1_0_1_0`. -/
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

/-- **`R^0_{101}(x) = a(t) a''(t)`** on FLRW (assuming `a(t) ≠ 0`).
Time-index Riemann component contributing to the spatial Ricci
`R_{11}`. -/
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

/-- **`R^2_{121}(x) = (a'(t))²`** on FLRW (assuming `a(t) ≠ 0`).
Spatial-spatial Riemann component contributing to `R_{11}`. -/
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

/-- **`R^3_{131}(x) = (a'(t))²`** on FLRW. By spatial isotropy, same
form as `flrwRiemann_2_1_2_1`. -/
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

/-! ## Ricci tensor: time-time component R_{00} = -3 a''/a -/

/-- **`R_{00}(x) = -3 a''(t)/a(t)`** on FLRW (assuming `a(t) ≠ 0`).
The time-time Ricci component, sum of three identical spatial-direction
Riemann components plus the vanishing `R^0_{000}` (by antisymmetry).
This is the textbook FLRW Ricci diagonal-time entry that drives the
**first Friedmann equation** when contracted against the inverse
metric. -/
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

/-- **`R_{11}(x) = a(t) a''(t) + 2 (a'(t))²`** on FLRW (assuming
`a(t) ≠ 0`). The spatial Ricci component, sum of the time-index
contribution `R^0_{101} = a a''` plus two identical spatial-index
contributions `R^j_{1j1} = (a')²`. The vanishing `R^1_{111}` follows
from antisymmetry. This is the textbook spatial-spatial Ricci entry
that drives the **second Friedmann equation**. -/
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

/-- **`R^0_{202}(x) = a(t) a''(t)`** on FLRW (assuming `a(t) ≠ 0`).
Spatial-isotropy copy of `flrwRiemann_0_1_0_1`. -/
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

/-- **`R^1_{212}(x) = (a'(t))²`** on FLRW (assuming `a(t) ≠ 0`). -/
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

/-- **`R^3_{232}(x) = (a'(t))²`** on FLRW (assuming `a(t) ≠ 0`). -/
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

/-- **`R_{22}(x) = a(t) a''(t) + 2 (a'(t))²`** on FLRW. By spatial
isotropy, identical to `R_{11}`. -/
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

/-- **`R^0_{303}(x) = a(t) a''(t)`** on FLRW. -/
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

/-- **`R^1_{313}(x) = (a'(t))²`** on FLRW (assuming `a(t) ≠ 0`). -/
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

/-- **`R^2_{323}(x) = (a'(t))²`** on FLRW (assuming `a(t) ≠ 0`). -/
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

/-- **`R_{33}(x) = a(t) a''(t) + 2 (a'(t))²`** on FLRW. By spatial
isotropy, identical to `R_{11}` and `R_{22}`. -/
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

end Curvature
end InfraFormalization
