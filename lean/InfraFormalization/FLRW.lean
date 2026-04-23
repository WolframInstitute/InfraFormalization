/-
**Friedmann-Lemaître-Robertson-Walker (FLRW) metric** (B6 / #26 partial).

The FLRW metric on ℝ⁴ with scale factor `a(t)`:

  `ds² = -dt² + a(t)² (dx² + dy² + dz²)`

In diagonal form:
  * `g_{00}(x) = -1`
  * `g_{ii}(x) = a(x_0)²` for `i = 1, 2, 3`
  * off-diagonal = 0

**Validity.** FLRW is valid wherever the scale factor `a` is
non-zero; at big-bang singularities `a → 0` and the metric becomes
degenerate. So FLRW is naturally a `PartialMetricData 4` rather than
a full `MetricData 4`.

**Connection to hypergraphs.** Same anchor as `Schwarzschild`:
continuum-target side. A future hypergraph trajectory with the
"expanding universe" signature would pair with this via the FLRW
bridge theorem.

Full F5 (Einstein equations with perfect-fluid matter) requires a
stress-energy tensor + connection infrastructure for FLRW; here we
provide the metric side only.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- **FLRW metric components** with scale factor `a : ℝ → ℝ` (a
function of cosmological time `x 0`). Diagonal in FLRW coordinates
`(t, x, y, z)`:
  * `g_{00} = -1`
  * `g_{ii} = a(t)²` for `i ∈ {1, 2, 3}`
  * off-diagonal = 0
-/
noncomputable def flrwG (a : ℝ → ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then -1
  else (a (x 0))^2

/-- **FLRW inverse metric**: `g^{00} = -1`, `g^{ii} = 1/a(t)²`. -/
noncomputable def flrwGinv (a : ℝ → ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then -1
  else 1 / (a (x 0))^2

/-- **FLRW first partial derivatives** `∂_l g_{μν}`. Only `∂_0 g_{ii}`
for `i ≥ 1` is non-zero: it equals `2 a(t) a'(t) = (a²)'(t)`. User
supplies `da : ℝ → ℝ` as the derivative of `a`. -/
noncomputable def flrwDg (a da : ℝ → ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else if l.val = 0 ∧ μ.val ≠ 0 then 2 * a (x 0) * da (x 0)
  else 0

/-- **FLRW validity**: scale factor is non-zero at `x 0`. -/
def FLRWValid (a : ℝ → ℝ) (x : Fin 4 → ℝ) : Prop :=
  a (x 0) ≠ 0

/-- **FLRW as a `PartialMetricData 4`** with validity `a(t) ≠ 0`. -/
noncomputable def flrwPartial (a da : ℝ → ℝ) : PartialMetricData 4 where
  g := flrwG a
  ginv := flrwGinv a
  dg := flrwDg a da
  valid := FLRWValid a
  g_symm := by
    intros x _ μ ν
    unfold flrwG
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]
  ginv_symm := by
    intros x _ μ ν
    unfold flrwGinv
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]
  ginv_mul := by
    intros x hx μ ν
    by_cases h : μ = ν
    · subst h
      rw [Finset.sum_eq_single μ]
      · rw [if_pos rfl]
        unfold flrwGinv flrwG
        simp only [ne_eq, not_true_eq_false, if_false]
        by_cases h0 : μ.val = 0
        · simp [h0]
        · have ha_ne : a (x 0) ≠ 0 := hx
          have hsq_ne : (a (x 0))^2 ≠ 0 := pow_ne_zero 2 ha_ne
          simp [h0]
          field_simp
      · intros α _ hα
        unfold flrwGinv
        simp [Ne.symm hα]
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intros α _
      by_cases hαμ : α = μ
      · subst hαμ
        unfold flrwG
        have hne : α ≠ ν := h
        simp [hne]
      · unfold flrwGinv
        have hne : μ ≠ α := fun heq => hαμ heq.symm
        simp [hne]
  dg_symm := by
    intros l x _ μ ν
    unfold flrwDg
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]

/-- **FLRW Christoffel at `μ=0, ν=ν, ρ=0` vanishes** when the time
derivative involves a spatial index only. Specifically,
`Γ^0_{0ν} = 0` for `ν` spatial, because the only non-zero `∂_l g` is
`∂_0 g_{ii}` and `g^{00}` pairs with `g_{00}` (constant = −1),
which has zero time derivative. -/
theorem flrwChristoffel_0_00 (a da : ℝ → ℝ) (x : Fin 4 → ℝ) :
    (flrwPartial a da).christoffel x 0 0 0 = 0 := by
  unfold PartialMetricData.christoffel
  simp only [flrwPartial]
  -- Every flrwDg term with ν = 0 vanishes.
  have h_dg_μ0 : ∀ l μ : Fin 4,
      flrwDg a da l x μ 0 = 0 := by
    intro l μ
    unfold flrwDg
    by_cases hμ : μ = 0
    · subst hμ; simp
    · simp [hμ]
  have h_sum : (∑ σ : Fin 4, flrwGinv a x 0 σ
      * (flrwDg a da 0 x σ 0 + flrwDg a da 0 x σ 0 - flrwDg a da σ x 0 0)) = 0 := by
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    rw [h_dg_μ0 0 σ, h_dg_μ0 σ 0]
    ring
  rw [h_sum]; ring

/-- **FLRW metric is Lorentzian where scale factor is non-zero.**
`flrwG a x` satisfies the diagonal Lorentzian signature (`g_00 < 0`,
`g_ii > 0`, off-diagonal zero) at every point where `a(x 0) ≠ 0`.

This uses a weaker predicate than `DiagLorentzianMetric` (which
quantifies over all `x`), since the FLRW metric is only Lorentzian
on the non-singular region. -/
theorem flrwG_lorentzian_pointwise (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hv : FLRWValid a x) :
    flrwG a x 0 0 < 0
    ∧ (∀ i : Fin 4, 0 < i.val → 0 < flrwG a x i i)
    ∧ (∀ μ ν : Fin 4, μ ≠ ν → flrwG a x μ ν = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- g_00 = -1 < 0.
    unfold flrwG
    simp
  · -- g_ii = a(t)^2 > 0.
    intro i hi
    unfold flrwG
    have hi_ne_zero : i.val ≠ 0 := Nat.pos_iff_ne_zero.mp hi
    simp [hi_ne_zero]
    have ha : a (x 0) ≠ 0 := hv
    have h_sq_pos : 0 < (a (x 0))^2 := by positivity
    exact h_sq_pos
  · -- off-diagonal zero.
    intros μ ν h
    unfold flrwG
    simp [h]

end Curvature
end InfraFormalization
