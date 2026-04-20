/-
Schwarzschild metric component formulas — the first non-trivial
curved metric we formalise.

**Why a separate component-level file and not a `MetricData 4`
instance?** The Schwarzschild metric components `1/(1 − 2M/r)` and
`1/(r² sin²θ)` are singular at `r = 2M`, `r = 0`, and
`sin θ = 0`. Our `MetricData n` structure requires the axiom
`∑_α g^{μα} g_{αν} = δ^μ_ν` pointwise for all `x : Fin n → ℝ`. That
axiom fails at the coordinate singularities (Lean's total division
returns `0` there, breaking `X · (1/X) = 1`).

So we formalise Schwarzschild as **component-level functions with
explicit exterior-region theorems**. `SchwarzschildValid M x` is the
predicate "the Schwarzschild metric is non-singular at `x`"; the key
theorems carry it as a hypothesis. The full `MetricData` packaging
is deferred until a `PartialMetricData` / domain-restricted variant
is added (tracked in `MILESTONES.md`).

**Scope.** Defines `sgg`, `sginv`, `sdg` (component functions),
`schwarzschildValid` (exterior predicate), and proves the key
inverse identity on the exterior. Christoffel computation and vacuum
`Ric = 0` are substantial follow-ups.

**Hypergraph anchor (pending, prioritised).** Per the grounding
principle: Schwarzschild must be reachable from a discrete-side
construction + convergence. This is the open Wolfram-physics problem
(F6/F7 both relate) — recorded as a target here.
-/

import InfraFormalization.CurvatureLocalCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

namespace InfraFormalization
namespace Curvature

/-- **Schwarzschild metric components** `g_{μν}(x; M)`. Diagonal in
Schwarzschild coordinates `(t, r, θ, φ)`. -/
noncomputable def sgg (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -(1 - 2 * M / r)
    else if μ.val = 1 then 1 / (1 - 2 * M / r)
    else if μ.val = 2 then r^2
    else r^2 * (Real.sin θ)^2

/-- **Schwarzschild inverse metric** `g^{μν}(x; M)`. Diagonal
reciprocal of `sgg`. -/
noncomputable def sginv (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if μ.val = 0 then -1 / (1 - 2 * M / r)
    else if μ.val = 1 then 1 - 2 * M / r
    else if μ.val = 2 then 1 / r^2
    else 1 / (r^2 * (Real.sin θ)^2)

/-- **First partial derivatives** `∂_l g_{μν}(x; M)`. Non-zero only
for `l = 1 (r)` on diagonal components, and for `l = 2 (θ)` on the
`φφ` component. -/
noncomputable def sdg (M : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ ≠ ν then 0
  else
    let r := x 1
    let θ := x 2
    if l.val = 1 then
      if μ.val = 0 then -(2 * M / r^2)
      else if μ.val = 1 then -(2 * M / r^2) / (1 - 2 * M / r)^2
      else if μ.val = 2 then 2 * r
      else 2 * r * (Real.sin θ)^2
    else if l.val = 2 then
      if μ.val = 3 then 2 * r^2 * Real.sin θ * Real.cos θ
      else 0
    else 0

/-- **Schwarzschild exterior region predicate.** Non-zero components,
non-singular metric. Requires `r > 2M` (strictly outside the event
horizon), `r ≠ 0`, and `sin θ ≠ 0` (outside the axis). -/
def SchwarzschildValid (M : ℝ) (x : Fin 4 → ℝ) : Prop :=
  x 1 > 2 * M ∧ x 1 > 0 ∧ Real.sin (x 2) ≠ 0

/-- The Schwarzschild metric is symmetric. -/
theorem sgg_symm (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    sgg M x μ ν = sgg M x ν μ := by
  unfold sgg
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- The Schwarzschild inverse metric is symmetric. -/
theorem sginv_symm (M : ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    sginv M x μ ν = sginv M x ν μ := by
  unfold sginv
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- The Schwarzschild partials preserve the metric's lower-index
symmetry. -/
theorem sdg_symm (M : ℝ) (l : Fin 4) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    sdg M l x μ ν = sdg M l x ν μ := by
  unfold sdg
  by_cases h : μ = ν
  · rw [h]
  · simp [h, Ne.symm h]

/-- **Diagonal inverse identity in the exterior.** For `x` in the
Schwarzschild exterior, `g · g⁻¹ = g^{μμ} g_{μμ} = 1` at every
diagonal component. -/
theorem sginv_mul_sgg_diagonal {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) (μ : Fin 4) :
    sginv M x μ μ * sgg M x μ μ = 1 := by
  unfold sginv sgg
  simp only [ne_eq, not_true_eq_false, if_false]
  obtain ⟨hr_gt_2M, hr_pos, hsinθ⟩ := hx
  have hr_ne_zero : x 1 ≠ 0 := ne_of_gt hr_pos
  have h_one_minus : (1 - 2 * M / x 1) ≠ 0 := by
    intro heq
    have : 1 = 2 * M / x 1 := by linarith
    have : x 1 = 2 * M := by
      rw [eq_comm, div_eq_iff hr_ne_zero] at this
      linarith
    linarith
  have h_r_minus_2M_ne : x 1 - 2 * M ≠ 0 := by
    intro heq
    have : x 1 = 2 * M := by linarith
    linarith
  fin_cases μ
  · -- μ = 0: (-1/(1 - 2M/r)) · (-(1 - 2M/r)) = 1.
    simp only [Fin.val_zero, if_true, if_false]
    field_simp
  · -- μ = 1: (1 - 2M/r) · (1/(1 - 2M/r)) = 1.
    simp only [Fin.val_one, if_true, if_false, reduceCtorEq]
    field_simp
  · -- μ = 2: (1/r²) · r² = 1.
    have hne1 : (2 : ℕ) ≠ 1 := by decide
    simp only [if_true, if_false, reduceCtorEq, hne1, if_neg hne1]
    have hr_sq : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne_zero
    field_simp
  · -- μ = 3: (1/(r² sin²θ)) · (r² sin²θ) = 1.
    have hne1 : (3 : ℕ) ≠ 1 := by decide
    have hne2 : (3 : ℕ) ≠ 2 := by decide
    simp only [if_true, if_false, reduceCtorEq, if_neg hne1, if_neg hne2]
    have hr_sq : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne_zero
    have hsin_sq : (Real.sin (x 2))^2 ≠ 0 := pow_ne_zero _ hsinθ
    field_simp

/-- **Schwarzschild full inverse identity in the exterior.** The
matrix product `g^{μα} g_{αν}` equals `δ^μ_ν` at any exterior point.
This is the axiom `ginv_mul` of `MetricData`, established here as a
theorem conditional on `SchwarzschildValid`. -/
theorem sginv_mul_sgg {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) (μ ν : Fin 4) :
    (∑ α : Fin 4, sginv M x μ α * sgg M x α ν)
    = if μ = ν then 1 else 0 := by
  by_cases h : μ = ν
  · subst h
    -- Diagonal: sum collapses at α = μ, value = 1.
    rw [Finset.sum_eq_single μ]
    · rw [if_pos rfl]
      exact sginv_mul_sgg_diagonal hx μ
    · intros α _ hα
      -- ginv μ α = 0 for α ≠ μ.
      unfold sginv
      simp [Ne.symm hα]
    · intro hne
      exact absurd (Finset.mem_univ μ) hne
  · -- Off-diagonal: all summands zero.
    rw [if_neg h]
    apply Finset.sum_eq_zero
    intros α _
    by_cases hαμ : α = μ
    · subst hαμ
      unfold sgg
      have hne : α ≠ ν := h
      simp [hne]
    · unfold sginv
      have hne : μ ≠ α := fun heq => hαμ heq.symm
      simp [hne]

/-! ## Schwarzschild Christoffel symbols

Direct computation using the Christoffel formula with Schwarzschild's
`sginv`, `sdg`. We define `schwarzschildChristoffel M x ρ μ ν` and
prove specific non-zero entries.

The textbook non-zero Schwarzschild Christoffel symbols (up to lower-
index symmetry) are:

  Γ^0_{01} = Γ^0_{10} = M / (r² (1 − 2M/r)) = M / (r(r−2M))
  Γ^1_{00} = M (r − 2M) / r³
  Γ^1_{11} = −M / (r² (1 − 2M/r)) = −M / (r(r−2M))
  Γ^1_{22} = −(r − 2M)
  Γ^1_{33} = −(r − 2M) sin²θ
  Γ^2_{12} = Γ^2_{21} = 1/r
  Γ^2_{33} = −sin θ cos θ
  Γ^3_{13} = Γ^3_{31} = 1/r
  Γ^3_{23} = Γ^3_{32} = cos θ / sin θ

All others vanish.

We prove `Γ^1_{00} = M (r − 2M) / r³` as the worked example,
illustrating the formalism. The rest follow by analogous computations
(tedious but mechanical).
-/

/-- **Schwarzschild Christoffel symbols** (via the standard formula). -/
noncomputable def schwarzschildChristoffel (M : ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) : ℝ :=
  (1 / 2) * ∑ σ : Fin 4,
    sginv M x ρ σ *
      (sdg M μ x σ ν + sdg M ν x σ μ - sdg M σ x μ ν)

/-- **Lower-index symmetry of Schwarzschild Christoffel**. -/
theorem schwarzschildChristoffel_symm (M : ℝ) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) :
    schwarzschildChristoffel M x ρ μ ν = schwarzschildChristoffel M x ρ ν μ := by
  unfold schwarzschildChristoffel
  congr 1
  apply Finset.sum_congr rfl
  intros σ _
  have h1 : sdg M μ x σ ν + sdg M ν x σ μ - sdg M σ x μ ν
          = sdg M ν x σ μ + sdg M μ x σ ν - sdg M σ x ν μ := by
    rw [sdg_symm M σ x μ ν]
    ring
  rw [h1]

/-- **Worked example: `Γ^1_{00}` = M(r − 2M)/r³ in the exterior.**
Demonstrates the Schwarzschild Christoffel computation on a specific
non-zero entry. The proof uses the three component computations:
`sginv M x 1 1 = 1 − 2M/r`, `sdg M 0 x 1 0 = 0` (time-derivative
of off-diagonal), `sdg M 1 x 0 0 = −2M/r²`. -/
theorem schwarzschildChristoffel_1_00 {M : ℝ} {x : Fin 4 → ℝ}
    (hx : SchwarzschildValid M x) :
    schwarzschildChristoffel M x (⟨1, by decide⟩ : Fin 4)
                                 (⟨0, by decide⟩ : Fin 4)
                                 (⟨0, by decide⟩ : Fin 4)
    = M * (x 1 - 2 * M) / (x 1)^3 := by
  unfold schwarzschildChristoffel
  obtain ⟨hr_gt_2M, hr_pos, _⟩ := hx
  have hr_ne : x 1 ≠ 0 := ne_of_gt hr_pos
  have hr_sq_ne : x 1 ^ 2 ≠ 0 := pow_ne_zero _ hr_ne
  have hr_cube_ne : x 1 ^ 3 ≠ 0 := pow_ne_zero _ hr_ne
  -- Compute the three specific entries needed.
  have h_sginv_11 : sginv M x (⟨1, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4)
                  = 1 - 2 * M / x 1 := by
    unfold sginv
    simp
  have h_sdg_0_10 : sdg M (⟨0, by decide⟩ : Fin 4) x
                         (⟨1, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4) = 0 := by
    unfold sdg
    have h10ne : (⟨1, by decide⟩ : Fin 4) ≠ (⟨0, by decide⟩ : Fin 4) := by decide
    simp [h10ne]
  have h_sdg_1_00 : sdg M (⟨1, by decide⟩ : Fin 4) x
                         (⟨0, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4)
                  = -(2 * M / x 1^2) := by
    unfold sdg
    simp
  -- The sum over σ collapses to σ = 1.
  rw [Finset.sum_eq_single (⟨1, by decide⟩ : Fin 4)]
  · -- Only the σ = 1 summand. Compute directly.
    rw [h_sginv_11, h_sdg_0_10, h_sdg_1_00]
    field_simp
    ring
  · -- For α ≠ 1, sginv M x 1 α = 0.
    intros α _ hα
    have hne : (⟨1, by decide⟩ : Fin 4) ≠ α := fun heq => hα heq.symm
    have h_sginv_1α : sginv M x (⟨1, by decide⟩ : Fin 4) α = 0 := by
      unfold sginv
      rw [if_pos hne]
    rw [h_sginv_1α]
    ring
  · intro hne
    exact absurd (Finset.mem_univ _) hne

end Curvature
end InfraFormalization
