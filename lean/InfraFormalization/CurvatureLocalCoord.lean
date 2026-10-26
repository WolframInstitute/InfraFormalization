/-
Metric data and Christoffel symbols in local coordinates on `ℝⁿ`.

This module defines `MetricData n`: components `g`, a left inverse
`ginv`, and a separately supplied first-derivative array `dg`, with
symmetry conditions. The array `dg` is not required to be the
derivative of `g`. It defines the Christoffel symbols of the second
kind from these data, proves their symmetry in the lower indices,
defines the Minkowski metric `minkowski4` with signature `(−, +, +, +)`,
and proves that its Christoffel symbols vanish.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace InfraFormalization
namespace Curvature

/-- Metric data on `ℝⁿ`: components `g_{μν}(x)`, inverse components
`g^{μν}(x)` with `g^{-1} g = I`, and an array `dg` standing for
`∂_λ g_{μν}(x)`, with `g`, `ginv` and `dg` symmetric in `μ, ν`. No
smoothness of `g` and no relation between `dg` and `g` is required.
The signature is unrestricted. -/
structure MetricData (n : Nat) where
  /-- Metric components `g_{μν}(x)`. -/
  g : (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- Inverse metric components `g^{μν}(x)`. -/
  ginv : (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- First partial derivatives `∂_l g_{μν}(x)`, indexed by `l : Fin n`. -/
  dg : Fin n → (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- `g` is symmetric. -/
  g_symm : ∀ x μ ν, g x μ ν = g x ν μ
  /-- `ginv` is symmetric. -/
  ginv_symm : ∀ x μ ν, ginv x μ ν = ginv x ν μ
  /-- `ginv` is the matrix inverse of `g`. -/
  ginv_mul : ∀ x μ ν, (∑ α : Fin n, ginv x μ α * g x α ν)
                      = if μ = ν then 1 else 0
  /-- `dg` is symmetric: `∂_l g_{μν} = ∂_l g_{νμ}`. -/
  dg_symm : ∀ l x μ ν, dg l x μ ν = dg l x ν μ

namespace MetricData

variable {n : Nat} (M : MetricData n)

/-- Christoffel symbols of the second kind,
`Γ^ρ_{μν}(x) = ½ ∑_σ g^{ρσ}(x) · (∂_μ g_{σν}(x) + ∂_ν g_{σμ}(x) − ∂_σ g_{μν}(x))`,
with the derivatives taken from `dg`. -/
noncomputable def christoffel (x : Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (1 / 2) * ∑ σ : Fin n,
    M.ginv x ρ σ *
      (M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν)

/-- `Γ^ρ_{μν} = Γ^ρ_{νμ}`, by `dg_symm`. -/
theorem christoffel_symm (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    M.christoffel x ρ μ ν = M.christoffel x ρ ν μ := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intros σ _
  have h1 : M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν
          = M.dg ν x σ μ + M.dg μ x σ ν - M.dg σ x ν μ := by
    rw [M.dg_symm σ x μ ν]
    ring
  rw [h1]

end MetricData

/-- The Minkowski metric on `ℝ⁴` with signature `(−, +, +, +)`:
`g_{00} = −1`, `g_{11} = g_{22} = g_{33} = 1`, `g_{μν} = 0` for `μ ≠ ν`,
and `dg = 0`. -/
noncomputable def minkowski4 : MetricData 4 where
  g := fun _ μ ν =>
    if μ = ν then
      if μ.val = 0 then -1 else 1
    else 0
  ginv := fun _ μ ν =>
    -- For a diagonal ±1 metric, the inverse equals the metric itself.
    if μ = ν then
      if μ.val = 0 then -1 else 1
    else 0
  dg := fun _ _ _ _ => 0
  g_symm := by
    intros x μ ν
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]
  ginv_symm := by
    intros x μ ν
    by_cases h : μ = ν
    · rw [h]
    · simp [h, Ne.symm h]
  ginv_mul := by
    intros x μ ν
    -- Pick the unique non-zero summand at α = μ (since ginv is diagonal).
    by_cases h : μ = ν
    · subst h
      rw [Finset.sum_eq_single μ
            (fun α _ hα => by simp [hα.symm])
            (fun hne => absurd (Finset.mem_univ μ) hne)]
      by_cases hμ : μ.val = 0
      · simp [hμ]
      · simp [hμ]
    · -- Each summand `(if μ = α then ±1 else 0) * (if α = ν then ±1 else 0)`
      -- vanishes since `μ ≠ ν` forces a 0 factor.
      rw [if_neg h]
      apply Finset.sum_eq_zero
      intros α _
      by_cases hαμ : α = μ
      · subst hαμ
        have hne_αν : α ≠ ν := h
        simp [hne_αν]
      · have hne : μ ≠ α := fun heq => hαμ heq.symm
        simp [hne]
  dg_symm := by
    intros l x μ ν; rfl

/-- All Christoffel symbols of `minkowski4` are 0. -/
theorem minkowski4_christoffel_zero (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    minkowski4.christoffel x ρ μ ν = 0 := by
  unfold MetricData.christoffel minkowski4
  simp

end Curvature
end InfraFormalization
