/-
Ollivier's coarse Ricci identity (Y. Ollivier, JFA 2009, Example 7), stated algebraically.

Let (M, g) be a smooth n-dimensional Riemannian manifold, p, q ∈ M with δ := d(p, q) small, v the
unit vector from p to q, and m_p^ε, m_q^ε the uniform probability measures on the geodesic balls
B_ε(p), B_ε(q). Ollivier's identity is

    W₁(m_p^ε, m_q^ε) = δ · (1 - ε² · Ric(v, v) / (2 · (n + 2)) + O(ε⁴ + ε² · δ²)),

where Ric(v, v) is the directional Ricci curvature and W₁ the 1-Wasserstein distance. G1 (Eq 48), G2
(Eqs 1668, 1882) and G3 (Eq 344) state this identity with the scalar curvature R in place of
Ric(v, v). Mathlib has no Riemannian curvature tensors, so this module states both forms as
equations between real parameters and proves that their leading terms differ by δ · ε² · (R -
Ric(v, v)) / (2(n + 2)). The comparison is in `results/phase2_continuum/eq344_verdict.md`.
-/

import Mathlib.Topology.MetricSpace.Basic

namespace InfraFormalization
namespace Infra

/-- Ollivier's identity as an equation between real parameters:
`W1 = δ · (1 - ε² · Ric_vv / (2(n + 2))) + error`. Here `n` is the dimension, `δ` and `ε` are the
two small parameters, `Ric_vv` is the directional Ricci curvature, `W1` is the value of
W₁(m_p^ε, m_q^ε), and `error` is the remainder term. -/
def OllivierIdentityLeading
    (n : Nat) (δ ε Ric_vv W1 : ℝ) (error : ℝ) : Prop :=
  W1 = δ * (1 - ε^2 * Ric_vv / (2 * (n + 2))) + error

/-- The form of the identity stated by Gorard, with the scalar curvature `R` in place of `Ric_vv`:
`W = δ · (1 - ε² · R / (2(n + 2))) + error`. -/
def GorardMisstatedForm
    (n : Nat) (δ ε R W : ℝ) (error : ℝ) : Prop :=
  W = δ * (1 - ε^2 * R / (2 * (n + 2))) + error

/-- If `OllivierIdentityLeading` and `GorardMisstatedForm` both hold with the same `W1` and the same
`error`, then their leading terms are equal:
`δ · (1 - ε² · Ric_vv / (2(n + 2))) = δ · (1 - ε² · R / (2(n + 2)))`. -/
theorem ollivier_gorard_leading_terms_eq_of_both
    (n : Nat) (δ ε R Ric_vv W1 : ℝ) (error : ℝ) :
    OllivierIdentityLeading n δ ε Ric_vv W1 error ∧
    GorardMisstatedForm n δ ε R W1 error →
    δ * (1 - ε^2 * Ric_vv / (2 * (n + 2))) =
    δ * (1 - ε^2 * R / (2 * (n + 2))) := by
  intro ⟨h1, h2⟩
  unfold OllivierIdentityLeading at h1
  unfold GorardMisstatedForm at h2
  linarith

/-- The Ollivier leading term minus the leading term with scalar curvature equals
`δ · ε² · (R - Ric_vv) / (2(n + 2))`. -/
theorem ollivier_minus_gorard_leading
    (n : Nat) (δ ε R Ric_vv : ℝ) :
    δ * (1 - ε^2 * Ric_vv / (2 * (n + 2)))
      - δ * (1 - ε^2 * R / (2 * (n + 2)))
      = δ * ε^2 * (R - Ric_vv) / (2 * (n + 2)) := by
  ring

/-- For `δ ≠ 0` and `ε ≠ 0`, the two leading terms are equal if and only if `R = Ric_vv`. On the
unit sphere S², `R = 2` and `Ric_vv = 1`, so the leading terms differ. -/
theorem ollivier_gorard_agree_iff (n : Nat) (δ ε R Ric_vv : ℝ)
    (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    δ * (1 - ε^2 * Ric_vv / (2 * (n + 2)))
      = δ * (1 - ε^2 * R / (2 * (n + 2))) ↔
    R = Ric_vv := by
  constructor
  · intro h
    have hn2_pos : (0 : ℝ) < 2 * ((n : ℝ) + 2) := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hn2_ne : (2 * ((n : ℝ) + 2)) ≠ 0 := ne_of_gt hn2_pos
    have hε2_ne : ε^2 ≠ 0 := pow_ne_zero 2 hε
    -- Multiply both sides by 2(n+2)/(δ·ε²) to isolate R = Ric_vv.
    have h_factor : δ * ε^2 * (R - Ric_vv) = 0 := by
      have h_ring : δ * (1 - ε^2 * Ric_vv / (2 * (n + 2)))
            - δ * (1 - ε^2 * R / (2 * (n + 2)))
          = δ * ε^2 * (R - Ric_vv) / (2 * (n + 2)) := by ring
      have h_sub : δ * (1 - ε^2 * Ric_vv / (2 * (n + 2)))
            - δ * (1 - ε^2 * R / (2 * (n + 2))) = 0 := by linarith
      rw [h_ring] at h_sub
      exact (div_eq_zero_iff.mp h_sub).resolve_right hn2_ne
    have hδε : δ * ε^2 ≠ 0 := mul_ne_zero hδ hε2_ne
    have h_zero : R - Ric_vv = 0 := (mul_eq_zero.mp h_factor).resolve_left hδε
    linarith
  · intro h
    rw [h]

/-- On the unit sphere S², with `R = 2`, `Ric_vv = 1` and `n = 2`, the two leading terms differ by
`δ · ε² / 8`. -/
theorem s2_gorard_error (δ ε : ℝ) :
    δ * (1 - ε^2 * 1 / (2 * (2 + 2)))
      - δ * (1 - ε^2 * 2 / (2 * (2 + 2)))
      = δ * ε^2 / 8 := by
  ring

/-- For `δ > 0` and `ε > 0`, the S² difference `δ · ε² / 8` is positive. -/
theorem s2_gorard_error_pos (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    0 < δ * ε^2 / 8 := by
  positivity

end Infra
end InfraFormalization
