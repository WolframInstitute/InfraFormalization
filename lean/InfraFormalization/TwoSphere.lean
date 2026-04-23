/-
**Round 2-sphere S² metric** — an explicit curved target for R4
(curved discrete-Ricci bridge).

In polar coordinates `(θ, φ)` the round unit 2-sphere has metric:

  `ds² = dθ² + sin²θ dφ²`

So `g_{00} = 1`, `g_{11} = sin²θ`, off-diagonal = 0. Validity: `sin θ ≠ 0`
(away from the poles).

This is the simplest positively-curved Riemannian target. Pairs with
the 3-regular-graph discrete signature in `CurvedRicciBridge.lean`
via the "beyond flat" bridge.

**Connection to hypergraphs.** Same anchor as `CurvedRicciBridge`:
continuum side. A hypergraph rule producing S² curvature would pair
with this via the discrete → continuum Ricci bridge.
-/

import InfraFormalization.PartialMetricData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- **2-sphere metric components**: `g_{00} = 1`, `g_{11} = sin²θ`,
off-diagonal zero. Here `x 0 = θ`. -/
noncomputable def sphereG (x : Fin 2 → ℝ) (μ ν : Fin 2) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then 1
  else (Real.sin (x 0))^2

/-- **2-sphere inverse metric**: `g^{00} = 1`, `g^{11} = 1/sin²θ`,
off-diagonal zero. -/
noncomputable def sphereGinv (x : Fin 2 → ℝ) (μ ν : Fin 2) : ℝ :=
  if μ ≠ ν then 0
  else if μ.val = 0 then 1
  else 1 / (Real.sin (x 0))^2

/-- **2-sphere first partials**: only `∂_0 g_{11} = 2 sin θ cos θ` is
nonzero (and its symmetric counterpart). -/
noncomputable def sphereDg (l : Fin 2) (x : Fin 2 → ℝ) (μ ν : Fin 2) : ℝ :=
  if μ ≠ ν then 0
  else if l.val = 0 ∧ μ.val = 1 then
    2 * Real.sin (x 0) * Real.cos (x 0)
  else 0

/-- **2-sphere validity**: `sin θ ≠ 0` (away from poles). -/
def SphereValid (x : Fin 2 → ℝ) : Prop :=
  Real.sin (x 0) ≠ 0

/-- **2-sphere metric is symmetric.** -/
theorem sphereG_symm (x : Fin 2 → ℝ) (μ ν : Fin 2) :
    sphereG x μ ν = sphereG x ν μ := by
  unfold sphereG
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- **2-sphere inverse metric is symmetric.** -/
theorem sphereGinv_symm (x : Fin 2 → ℝ) (μ ν : Fin 2) :
    sphereGinv x μ ν = sphereGinv x ν μ := by
  unfold sphereGinv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- **2-sphere as a `PartialMetricData 2`** on the validity domain. -/
noncomputable def spherePartial : PartialMetricData 2 where
  g := sphereG
  ginv := sphereGinv
  dg := sphereDg
  valid := SphereValid
  g_symm := fun x _ μ ν => sphereG_symm x μ ν
  ginv_symm := fun x _ μ ν => sphereGinv_symm x μ ν
  ginv_mul := by
    intros x hx μ ν
    by_cases h : μ = ν
    · subst h
      rw [Finset.sum_eq_single μ]
      · rw [if_pos rfl]
        unfold sphereGinv sphereG
        simp only [ne_eq, not_true_eq_false, if_false]
        by_cases h0 : μ.val = 0
        · simp [h0]
        · have hs_ne : Real.sin (x 0) ≠ 0 := hx
          have hsq_ne : (Real.sin (x 0))^2 ≠ 0 := pow_ne_zero 2 hs_ne
          simp [h0]
          field_simp
      · intros α _ hα
        unfold sphereGinv
        simp [Ne.symm hα]
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intros α _
      by_cases hαμ : α = μ
      · subst hαμ
        unfold sphereG
        have hne : α ≠ ν := h
        simp [hne]
      · unfold sphereGinv
        have hne : μ ≠ α := fun heq => hαμ heq.symm
        simp [hne]
  dg_symm := by
    intros l x _ μ ν
    unfold sphereDg
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]

/-- **2-sphere has non-vanishing Christoffel `Γ⁰_{11}` at generic points.**
Specifically, `Γ⁰_{11}(x) = -sin θ cos θ`, which is non-zero whenever
`sin θ ≠ 0 ∧ cos θ ≠ 0`. This confirms S² is a genuinely curved
target — the continuum side of the curved Ricci bridge beyond the
flat circle case. -/
theorem sphereChristoffel_0_1_1 (x : Fin 2 → ℝ) :
    spherePartial.christoffel x 0 1 1 = -(Real.sin (x 0) * Real.cos (x 0)) := by
  unfold PartialMetricData.christoffel
  simp only [spherePartial, sphereGinv, sphereDg, sphereG]
  simp
  ring

end Curvature
end InfraFormalization
