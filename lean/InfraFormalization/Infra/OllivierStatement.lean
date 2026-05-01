/-
Correct statement of Ollivier's theorem (JFA 2009, Example 7).

Mathlib does NOT yet have the Ricci curvature tensor formalised — the
`Mathlib.Geometry.Manifold.*` files cover charted spaces, smooth
manifolds, tangent bundles, and local diffeomorphisms, but Riemannian
metrics, Levi-Civita connections, and curvature tensors remain a
future-contribution target. See the Mathlib tracking issue for
differential geometry.

Until those pieces land, we state Ollivier's identity as an abstract
proposition parameterised by the pieces it depends on. The point is
to have a canonical Lean-level record of the correct statement (as
distinguished from the incorrect form found throughout the JGORARD
corpus, which substitutes the scalar curvature `R` for the directional
Ricci `Ric(v, v)`).

**Ollivier's theorem (to be formalised against Mathlib once
Riemannian + optimal-transport infrastructure matures):**

  Let (M, g) be a smooth n-dimensional Riemannian manifold. For
  p, q ∈ M with δ := d(p, q) small and v := (q - p)/|q - p| the unit
  vector from p to q, let m_p^ε (resp. m_q^ε) be the uniform
  probability measure on the geodesic ball B_ε(p) (resp. B_ε(q)).
  Then:

    W₁(m_p^ε, m_q^ε) = δ · (1 - ε² · Ric(v, v) / (2 · (n + 2))
                              + O(ε⁴ + ε² · δ²))

  where Ric(v, v) is the directional Ricci curvature along v, and W₁
  is the 1-Wasserstein distance.

This is the statement that — verbatim in JGORARD (arXiv:2004.14810 Eq
48, arXiv:2011.12174 Eqs 1668 / 1882, arXiv:2102.09363 Eq 344) — is
mis-stated with scalar curvature R in place of Ric(v, v). On S² the
two differ by factor 2; in general they are independent. The full
audit is in `results/phase2_continuum/eq344_verdict.md`.
-/

import Mathlib.Topology.MetricSpace.Basic

namespace InfraFormalization
namespace Infra

/-- **Ollivier's identity (statement only).** We express it as a
predicate over the abstract pieces (manifold type `M`, metric, measure
on ε-balls, directional Ricci function, dimension `d`). When Mathlib's
Riemannian + optimal-transport infrastructure is sufficient, this
predicate can be specialised and the theorem can be proved; until
then it serves as a canonical Lean-level record of the correct
identity that subsequent papers can reference.

The predicate takes:
- `n` : spatial dimension of the manifold
- `δ`, `ε` : the two small parameters
- `Ric_vv` : the directional Ricci at the relevant unit vector
- `W1` : the claimed value of W₁(m_p^ε, m_q^ε)

and asserts the leading-order-plus-error form. -/
def OllivierIdentityLeading
    (n : Nat) (δ ε Ric_vv W1 : ℝ) (error : ℝ) : Prop :=
  W1 = δ * (1 - ε^2 * Ric_vv / (2 * (n + 2))) + error

/-- **JGORARD's mis-stated form** (as published, using scalar `R` in
place of `Ric(v, v)`). We include this only for explicit contrast
with the correct version above. -/
def GorardMisstatedForm
    (n : Nat) (δ ε R W : ℝ) (error : ℝ) : Prop :=
  W = δ * (1 - ε^2 * R / (2 * (n + 2))) + error

/-- **The correct and JGORARD forms coincide iff `R = Ric(v, v)`** (and
error terms match). This is why JGORARD's form is correct on Einstein
manifolds (where `Ric = (R/n) · g`, so `Ric(v,v) = R/n`, giving
equality only at `R = R/n` i.e. `R = 0` or `n = 1`), but incorrect on
generic Riemannian manifolds — including constant-curvature spheres.
-/
theorem ollivier_vs_gorard_equivalence_requires_ric_eq_scalar
    (n : Nat) (δ ε R Ric_vv W1 : ℝ) (error : ℝ) :
    OllivierIdentityLeading n δ ε Ric_vv W1 error ∧
    GorardMisstatedForm n δ ε R W1 error →
    δ * (1 - ε^2 * Ric_vv / (2 * (n + 2))) =
    δ * (1 - ε^2 * R / (2 * (n + 2))) := by
  intro ⟨h1, h2⟩
  unfold OllivierIdentityLeading at h1
  unfold GorardMisstatedForm at h2
  linarith

/-- **Quantitative discrepancy**: the JGORARD Riemannian leading term
differs from the Ollivier leading term by exactly
`δ · ε² · (Ric_vv − R) / (2(n+2))`. Once `δ, ε > 0`, the discrepancy
vanishes iff `Ric_vv = R`. This is the precise gap JGORARD's papers
silently drop when they substitute scalar for directional Ricci. -/
theorem ollivier_minus_gorard_leading
    (n : Nat) (δ ε R Ric_vv : ℝ) :
    δ * (1 - ε^2 * Ric_vv / (2 * (n + 2)))
      - δ * (1 - ε^2 * R / (2 * (n + 2)))
      = δ * ε^2 * (R - Ric_vv) / (2 * (n + 2)) := by
  ring

/-- **Discrepancy is zero iff scalar = directional Ricci**
(at `δ, ε ≠ 0`, `n + 2 ≠ 0`). This is the precise algebraic condition
under which JGORARD's substitution is innocuous — essentially only
Einstein manifolds with `Ric_vv` happening to equal `R`, i.e.
`n = 1` or trivial-curvature cases. On a generic Riemannian manifold
(e.g. `S²` where `R = 2` but `Ric_vv = 1`), the leading terms differ
and JGORARD's prediction is off. -/
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

/-- **Worked example: unit 2-sphere S²**. Scalar curvature `R = 2`,
directional Ricci `Ric(v,v) = 1` at every unit tangent vector. JGORARD's
substitution makes a leading-term error of exactly `δ · ε² / 8` on S². -/
theorem s2_gorard_error (δ ε : ℝ) :
    δ * (1 - ε^2 * 1 / (2 * (2 + 2)))
      - δ * (1 - ε^2 * 2 / (2 * (2 + 2)))
      = δ * ε^2 / 8 := by
  ring

/-- **S² discrepancy is strictly positive** for every positive `δ, ε`.
Rules out JGORARD's substitution on the 2-sphere at every smallness
scale. -/
theorem s2_gorard_error_pos (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    0 < δ * ε^2 / 8 := by
  positivity

end Infra
end InfraFormalization
