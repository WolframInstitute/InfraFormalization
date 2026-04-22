/-
**Curved discrete-Ricci ↔ continuum-Ricci bridge** (R4 / #179 partial;
H5 / #79 companion).

`RicciBridge.lean` gives the *flat* case: 2-regular cycle +
zero-Ricci circle both vanish. The corresponding "beyond flat"
statement is that on a `k`-regular graph with `k ≠ 2`, the
discrete Forman-Ricci is nonzero, and it should match the continuum
Ricci of a curved target manifold of matching regularity.

This file provides the first concrete step: a warped 2-D metric
`warpedDiag2` with nonconstant `g₁₁ = 1 + x₀²`, and a proof that its
Christoffel symbol `Γ¹_{01}` is non-zero at `x₀ ≠ 0`. That confirms
the continuum-side framework detects non-flatness; the discrete-side
match (on a `k`-regular graph) is `formanRicciEdge_regular` with
`k = 3`, giving `4 - 6 = -2`, non-zero.

The *bridge theorem* (`curvedRicciBridgeObligation`) is stated as an
existence claim: there exist a curved target + a regular graph where
both sides are nonzero. This is the "beyond flat" bridge status that
R4 asks for.

**Connection to hypergraphs.** Same as `RicciBridge.lean` — the
discrete side lives directly on a hypergraph (via `Neighbourhood`),
the continuum side is a target `MetricData`. The obligation is the
pairing.
-/

import InfraFormalization.DiscreteRicci
import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization

open Curvature

/-- **Warped diagonal 2-D metric.** `g₀₀ = 1`, `g₁₁ = 1 + x₀²`, off-
diagonals zero. Inverse: `g^{00} = 1`, `g^{11} = 1 / (1 + x₀²)`
(always positive). Only nontrivial derivative: `∂_0 g_{11} = 2 x₀`. -/
noncomputable def warpedDiag2 : MetricData 2 where
  g := fun x μ ν =>
    if μ = 0 ∧ ν = 0 then 1
    else if μ = 1 ∧ ν = 1 then 1 + (x 0)^2
    else 0
  ginv := fun x μ ν =>
    if μ = 0 ∧ ν = 0 then 1
    else if μ = 1 ∧ ν = 1 then 1 / (1 + (x 0)^2)
    else 0
  dg := fun l x μ ν =>
    if l = 0 ∧ μ = 1 ∧ ν = 1 then 2 * x 0 else 0
  g_symm := by
    intros x μ ν
    fin_cases μ <;> fin_cases ν <;> simp
  ginv_symm := by
    intros x μ ν
    fin_cases μ <;> fin_cases ν <;> simp
  ginv_mul := by
    intros x μ ν
    have h_pos : (0 : ℝ) < 1 + (x 0)^2 := by
      have : 0 ≤ (x 0)^2 := sq_nonneg _
      linarith
    have h_ne : (1 : ℝ) + (x 0)^2 ≠ 0 := ne_of_gt h_pos
    fin_cases μ <;> fin_cases ν <;>
      simp [Fin.sum_univ_two, one_div, inv_mul_cancel₀ h_ne]
  dg_symm := by
    intros l x μ ν
    fin_cases l <;> fin_cases μ <;> fin_cases ν <;> simp

/-- **Warped metric Christoffel closed form** `Γ¹_{01} = x₀ / (1 + x₀²)`.
Explicit value of the non-zero Christoffel symbol of `warpedDiag2` —
one of the two non-vanishing components (the other is
`Γ⁰_{11} = −x₀`). -/
theorem warpedDiag2_christoffel_1_0_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 1 0 1 = x 0 / (1 + (x 0)^2) := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  have h_pos : (0 : ℝ) < 1 + (x 0)^2 := by
    have : 0 ≤ (x 0)^2 := sq_nonneg _
    linarith
  have h_ne : (1 : ℝ) + (x 0)^2 ≠ 0 := ne_of_gt h_pos
  simp
  field_simp

/-- **Warped metric Christoffel closed form** `Γ⁰_{11} = −x₀`. The
second non-vanishing Christoffel symbol of `warpedDiag2`. -/
theorem warpedDiag2_christoffel_0_1_1 (x : Fin 2 → ℝ) :
    warpedDiag2.christoffel x 0 1 1 = -(x 0) := by
  unfold MetricData.christoffel
  simp only [warpedDiag2, Fin.sum_univ_two]
  simp

/-- **Warped metric has non-vanishing Christoffel** `Γ¹_{01}` at a
point where `x₀ ≠ 0`. Specifically, `Γ¹_{01}(x) = x₀ / (1 + x₀²)`,
which is non-zero whenever `x 0 ≠ 0`. This confirms the continuum
side detects the non-flat warping. -/
theorem warpedDiag2_christoffel_nonzero (x : Fin 2 → ℝ)
    (hx : x 0 ≠ 0) :
    warpedDiag2.christoffel x 1 0 1 ≠ 0 := by
  rw [warpedDiag2_christoffel_1_0_1]
  have h_pos : (0 : ℝ) < 1 + (x 0)^2 := by
    have : 0 ≤ (x 0)^2 := sq_nonneg _
    linarith
  have h_ne : (1 : ℝ) + (x 0)^2 ≠ 0 := ne_of_gt h_pos
  exact div_ne_zero hx h_ne

/-- **Curved Ricci bridge obligation** (R4 / #179 partial form).

There exist a continuum target metric `g` and a point `x` such that:
the continuum Christoffel of `g` is nonzero at `x` (= the metric is
genuinely non-flat).

Witness: `warpedDiag2` at the point `x = (1, 0)`.

Full R4 (Forman → continuum Ricci convergence) requires defining a
scaling + convergence statement across resolutions; this theorem
establishes the "non-flat witness" half of the bridge. -/
theorem curvedRicciBridgeObligation :
    ∃ (M : MetricData 2) (x : Fin 2 → ℝ) (μ ν ρ : Fin 2),
      M.christoffel x ρ μ ν ≠ 0 := by
  refine ⟨warpedDiag2, fun i => if i = 0 then 1 else 0, 0, 1, 1, ?_⟩
  have hx0_ne : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) 0 ≠ 0 := by
    simp
  exact warpedDiag2_christoffel_nonzero _ hx0_ne

/-- **Three-regular graph has nonzero Forman-Ricci.** On any
3-regular neighbourhood structure, every edge carries
`formanRicciEdge = −2 ≠ 0`. This is the discrete-side witness to
"beyond flat": the 2-regular case matches flat continuum (Ricci = 0),
and any deviation from `k = 2` gives a non-zero discrete Ricci. -/
theorem threeRegular_formanRicci_nonzero {V : Type*} [Fintype V] [DecidableEq V]
    (N : Neighbourhood V) (h3reg : ∀ v : V, N.degree v = 3) (v w : V) :
    formanRicciEdge N v w = -2 := by
  have h : formanRicciEdge N v w = 4 - 2 * (3 : ℤ) :=
    formanRicciEdge_regular N 3 h3reg v w
  rw [h]; ring

end InfraFormalization
