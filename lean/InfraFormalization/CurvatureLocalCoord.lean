/-
Curvature tensors in local coordinates (Rung 5 of the bridge ladder).

We formalise the Christoffel symbols, Riemann tensor, Ricci tensor,
scalar curvature, and Einstein tensor as **explicit formulas in local
coordinates**, sidestepping the coordinate-free bundle machinery that
Mathlib doesn't yet have.

**Representation.** A metric on `ℝⁿ` is an `n × n` symmetric
invertible matrix-valued function of position, together with its first
partial derivatives (given as data, not derived from smoothness). This
lets us write Christoffel symbols, curvature tensors, etc. as
algebraic expressions in the components.

**Scope.** This file stops at the Christoffel symbols and first
identities. Riemann and Ricci require second partial derivatives of
the metric (or first derivatives of Christoffels) as additional data,
and are in a follow-up file.

**Why this route.** A full bundle-theoretic Riemannian formalisation
(Rung 4) is a multi-month Mathlib project. The local-coordinate
approach gives us usable curvature objects for explicit metrics
(Minkowski, Schwarzschild in Schwarzschild coords, FLRW) now, without
waiting for the full infrastructure.
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

/-- **Metric-with-derivatives data** on `ℝⁿ`. Carries:
  * the metric components `g_{μν}(x)`,
  * the inverse metric components `g^{μν}(x)`,
  * the first partial derivatives `∂_λ g_{μν}(x)`,
  * symmetry and inverse axioms.

We do NOT require `g` to be smooth (we treat `∂_λ g` as a separate
user-supplied function). Nondegeneracy is enforced via the inverse
axiom. Signature is unrestricted — both Riemannian and Lorentzian
data fit. -/
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
  /-- Partial derivatives inherit symmetry from the metric:
      `∂_l g_{μν} = ∂_l g_{νμ}`. -/
  dg_symm : ∀ l x μ ν, dg l x μ ν = dg l x ν μ

namespace MetricData

variable {n : Nat} (M : MetricData n)

/-- **Christoffel symbols of the second kind.**

  `Γ^ρ_{μν}(x) = ½ g^{ρσ}(x) · (∂_μ g_{σν}(x) + ∂_ν g_{σμ}(x) − ∂_σ g_{μν}(x))`.

Sum over `σ` is implicit (summation over repeated index). We write
it explicitly using `Finset.sum`. -/
noncomputable def christoffel (x : Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (1 / 2) * ∑ σ : Fin n,
    M.ginv x ρ σ *
      (M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν)

/-- **Symmetry of Christoffel symbols in the lower indices.**
  `Γ^ρ_{μν} = Γ^ρ_{νμ}`.

Follows directly from `dg_symm` and the expression's symmetry in
`μ ↔ ν`. -/
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

/-- **Minkowski metric** on `ℝ⁴` with signature `(−, +, +, +)`:
  `g_{00} = −1, g_{11} = g_{22} = g_{33} = +1, g_{μν} = 0` for `μ ≠ ν`.

Partial derivatives are identically zero (the metric is
position-independent). -/
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

/-- For Minkowski, all Christoffel symbols vanish identically. -/
theorem minkowski4_christoffel_zero (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    minkowski4.christoffel x ρ μ ν = 0 := by
  unfold MetricData.christoffel minkowski4
  simp

end Curvature
end InfraFormalization
