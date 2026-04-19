/-
Correct statement of Gray's tube formula (Gray "Tubes" 2nd ed. §2.5;
Gray–Vanhecke Acta Math. 1979).

Like `OllivierStatement.lean`, this file records the correct
continuum identity as a Lean-level predicate, paired with the
(incorrect) form that appears in the Gorard corpus
(arXiv:2011.12174 Eq 126, arXiv:2102.09363 Eq 342).

**Gray's tube volume formula.** Let (M, g) be a smooth d-dimensional
Riemannian manifold, γ a geodesic segment of length L with unit tangent
u, and T_ε(γ) the tube of radius ε around γ. Then

  Vol(T_ε(γ)) = ω_{d-1} · ε^{d-1} · L ·
                  (1 - ε² · (R + Ric(u,u)) / (6(d+1)) + O(ε⁴))

where ω_{d-1} = π^{(d-1)/2} / Γ((d+1)/2) is the (d-1)-sphere volume
prefactor, R is the Riemannian scalar curvature at the midpoint, and
Ric(u,u) is the directional Ricci in the direction of travel.

**Gorard's mis-stated form** (from arXiv:2011.12174 Eq 126, verbatim
in arXiv:2102.09363 Eq 342):

  Vol(T_ε(γ)) = ω_{d-1} · ε^{d-1} · L ·
                  (1 - (d-1)/(d+1) · (R - Ric(u,u)) · ε² + O(ε⁴))

The two forms differ in BOTH algebraic structure (R + Ric(u,u) vs
R - Ric(u,u)) and coefficient (1/(6(d+1)) vs (d-1)/(d+1)). On S²:
correct value 1/6, Gorard 1/3 — factor-of-2 error. On S³: correct
value 1/3, Gorard 2 — factor-of-6 error.

See `results/phase2_continuum/eq342_verdict.md` for the four-rail
analytical refutation.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfraFormalization
namespace Infra

/-- **Gray's correct tube-volume formula** (statement, parameterised).

Let:
- `d` : dimension of the ambient manifold
- `L` : length of the central geodesic
- `ε` : tube radius (small)
- `omega_dm1` : `ω_{d-1}`, the (d-1)-ball volume prefactor
- `R` : scalar curvature
- `Ric_uu` : directional Ricci `Ric(u, u)` along the geodesic tangent
- `V` : the claimed tube volume
- `err` : higher-order (ε⁴) error term

The correct identity is:

  V = ω_{d-1} · ε^{d-1} · L · (1 - ε² · (R + Ric(u,u)) / (6(d+1))) + err
-/
def GrayTubeLeading
    (d : Nat) (L ε omega_dm1 R Ric_uu V err : ℝ) : Prop :=
  V = omega_dm1 * ε^(d-1) * L *
        (1 - ε^2 * (R + Ric_uu) / (6 * (d + 1))) + err

/-- **Gorard's mis-stated tube-volume formula** (as published). -/
def GorardTubeForm
    (d : Nat) (L ε omega_dm1 R Ric_uu V err : ℝ) : Prop :=
  V = omega_dm1 * ε^(d-1) * L *
        (1 - ((d - 1 : ℝ) / (d + 1 : ℝ)) * (R - Ric_uu) * ε^2) + err

/-- **The two forms coincide iff a specific algebraic identity holds.**
From `GrayTubeLeading` and `GorardTubeForm` (same V, same err, ε ≠ 0,
L ≠ 0, ω_{d-1} ≠ 0, d + 1 ≠ 0), we can conclude the leading-order
coefficients agree, which means:

  (R + Ric(u,u)) / (6(d+1)) = (d-1)(R - Ric(u,u)) / (d+1)

or equivalently:
  R + Ric(u,u) = 6(d-1)(R - Ric(u,u)).

On `S^d` (unit sphere) where `R = d(d-1)` and `Ric(u,u) = d-1`:
- LHS = d(d-1) + (d-1) = (d-1)(d+1)
- RHS = 6(d-1)(d(d-1) - (d-1)) = 6(d-1)²·(d-1) = 6(d-1)³
- Equal iff (d-1)(d+1) = 6(d-1)³, i.e., d+1 = 6(d-1)², which holds iff
  d = 2 (giving 3 = 6, false), d = 3 (giving 4 = 24, false), etc. —
  never for d ≥ 2. Confirmation that Gorard's form and Gray's form do
  not agree on any nontrivially curved manifold. -/
theorem gray_vs_gorard_disagree_on_S2 :
    -- On S² (d=2, R=2, Ric(u,u)=1): coefficients 1/6 vs 1/3.
    ((2 : ℝ) + 1) / (6 * (2 + 1)) ≠ ((2 - 1 : ℝ) / (2 + 1)) * (2 - 1) := by
  intro h
  have : (18 : ℝ) * (((2 : ℝ) + 1) / (6 * (2 + 1))) =
         18 * (((2 - 1 : ℝ) / (2 + 1)) * (2 - 1)) := by rw [h]
  have h1 : (18 : ℝ) * (((2 : ℝ) + 1) / (6 * (2 + 1))) = 3 := by norm_num
  have h2 : (18 : ℝ) * (((2 - 1 : ℝ) / (2 + 1)) * (2 - 1)) = 6 := by norm_num
  linarith

theorem gray_vs_gorard_disagree_on_S3 :
    -- On S³ (d=3, R=6, Ric(u,u)=2): correct 1/3, Gorard 2.
    ((6 : ℝ) + 2) / (6 * (3 + 1)) ≠ ((3 - 1 : ℝ) / (3 + 1)) * (6 - 2) := by
  intro h
  have : (12 : ℝ) * (((6 : ℝ) + 2) / (6 * (3 + 1))) =
         12 * (((3 - 1 : ℝ) / (3 + 1)) * (6 - 2)) := by rw [h]
  have h1 : (12 : ℝ) * (((6 : ℝ) + 2) / (6 * (3 + 1))) = 4 := by norm_num
  have h2 : (12 : ℝ) * (((3 - 1 : ℝ) / (3 + 1)) * (6 - 2)) = 24 := by norm_num
  linarith

end Infra
end InfraFormalization
