/-
Gray's tube-volume formula and the form in G2 Eq. 126 and G3 Eq. 342.

For a geodesic segment γ of length L with unit tangent u in a d-dimensional Riemannian
manifold, Gray ("Tubes", 2nd ed., §2.5; Gray–Vanhecke, Acta Math. 1979) gives
  Vol(T_ε(γ)) = ω_{d-1} · ε^{d-1} · L · (1 - ε² · (R + Ric(u,u)) / (6(d+1)) + O(ε⁴)),
with ω_{d-1} the volume of the unit (d-1)-ball, R the scalar curvature and Ric(u,u) the
Ricci curvature in the direction u. G2 Eq. 126 and G3 Eq. 342 give the ε² coefficient as
(d-1)/(d+1) · (R - Ric(u,u)). The module defines both identities as predicates on real
parameters and proves that the two ε² coefficients differ on the unit spheres S² (1/6 and
1/3) and S³ (1/3 and 2). The derivation is in `results/phase2_continuum/eq342_verdict.md`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfraFormalization
namespace Infra

/-- The predicate `V = ω_{d-1} · ε^{d-1} · L · (1 - ε² · (R + Ric(u,u)) / (6(d+1))) + err`
on real parameters: dimension `d`, geodesic length `L`, tube radius `ε`, ball-volume factor
`omega_dm1`, scalar curvature `R`, directional Ricci curvature `Ric_uu`, volume `V` and
remainder `err`. This is Gray's formula with the remainder written as `err`. -/
def GrayTubeLeading
    (d : Nat) (L ε omega_dm1 R Ric_uu V err : ℝ) : Prop :=
  V = omega_dm1 * ε^(d-1) * L *
        (1 - ε^2 * (R + Ric_uu) / (6 * (d + 1))) + err

/-- The predicate
`V = ω_{d-1} · ε^{d-1} · L · (1 - (d-1)/(d+1) · (R - Ric(u,u)) · ε²) + err`,
the tube-volume formula of G2 Eq. 126 and G3 Eq. 342 with the remainder written as `err`. -/
def GorardTubeForm
    (d : Nat) (L ε omega_dm1 R Ric_uu V err : ℝ) : Prop :=
  V = omega_dm1 * ε^(d-1) * L *
        (1 - ((d - 1 : ℝ) / (d + 1 : ℝ)) * (R - Ric_uu) * ε^2) + err

/-- On the unit sphere S² (d = 2, R = 2, Ric(u,u) = 1), the ε² coefficient of
`GrayTubeLeading`, 1/6, differs from that of `GorardTubeForm`, 1/3. -/
theorem gray_vs_gorard_disagree_on_S2 :
    ((2 : ℝ) + 1) / (6 * (2 + 1)) ≠ ((2 - 1 : ℝ) / (2 + 1)) * (2 - 1) := by
  intro h
  have : (18 : ℝ) * (((2 : ℝ) + 1) / (6 * (2 + 1))) =
         18 * (((2 - 1 : ℝ) / (2 + 1)) * (2 - 1)) := by rw [h]
  have h1 : (18 : ℝ) * (((2 : ℝ) + 1) / (6 * (2 + 1))) = 3 := by norm_num
  have h2 : (18 : ℝ) * (((2 - 1 : ℝ) / (2 + 1)) * (2 - 1)) = 6 := by norm_num
  linarith

/-- On the unit sphere S³ (d = 3, R = 6, Ric(u,u) = 2), the ε² coefficient of
`GrayTubeLeading`, 1/3, differs from that of `GorardTubeForm`, 2. -/
theorem gray_vs_gorard_disagree_on_S3 :
    ((6 : ℝ) + 2) / (6 * (3 + 1)) ≠ ((3 - 1 : ℝ) / (3 + 1)) * (6 - 2) := by
  intro h
  have : (12 : ℝ) * (((6 : ℝ) + 2) / (6 * (3 + 1))) =
         12 * (((3 - 1 : ℝ) / (3 + 1)) * (6 - 2)) := by rw [h]
  have h1 : (12 : ℝ) * (((6 : ℝ) + 2) / (6 * (3 + 1))) = 4 := by norm_num
  have h2 : (12 : ℝ) * (((3 - 1 : ℝ) / (3 + 1)) * (6 - 2)) = 24 := by norm_num
  linarith

end Infra
end InfraFormalization
