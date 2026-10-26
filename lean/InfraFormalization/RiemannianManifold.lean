import InfraFormalization.CurvatureLocalCoord

/-!
Diagonal Riemannian metrics in coordinates.

This module defines `DiagRiemannianMetric M` for `M : MetricData n` (all
diagonal components positive and all off-diagonal components 0 at every
point), the bundled structure `DiagRiemannianManifold n`, and the Euclidean
metric `euclidean n` with `g = I`. It proves that `euclidean n` satisfies
`DiagRiemannianMetric`. Metrics are component functions on `ℝⁿ`, not
sections of a bundle over a Mathlib manifold.
-/

namespace InfraFormalization
namespace Curvature

/-- `M` is diagonal with positive diagonal components at every point. -/
structure DiagRiemannianMetric {n : Nat} (M : MetricData n) : Prop where
  /-- `g_{ii}(x) > 0` for every `x` and every `i`. -/
  g_ii_pos : ∀ (x : Fin n → ℝ) (i : Fin n), 0 < M.g x i i
  /-- `g` is diagonal: off-diagonal components vanish. -/
  g_off_diag : ∀ (x : Fin n → ℝ) (μ ν : Fin n), μ ≠ ν → M.g x μ ν = 0

/-- A `MetricData n` with a proof of `DiagRiemannianMetric`. -/
structure DiagRiemannianManifold (n : Nat) where
  /-- Underlying metric data. -/
  toMetric : MetricData n
  /-- Proof that the metric is diagonal with positive diagonal. -/
  riemannian : DiagRiemannianMetric toMetric

/-- The metric data with `g_{μν} = δ_{μν}`, `g^{μν} = δ_{μν}` and all
partial derivatives 0. -/
noncomputable def euclidean (n : Nat) : MetricData n where
  g    _ i j := if i = j then 1 else 0
  ginv _ i j := if i = j then 1 else 0
  dg _ _ _ _ := 0
  g_symm := by
    intros x μ ν
    by_cases h : μ = ν
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  ginv_symm := by
    intros x μ ν
    by_cases h : μ = ν
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  ginv_mul := by
    intros x μ ν
    by_cases hμν : μ = ν
    · subst hμν
      rw [Finset.sum_eq_single μ]
      · simp
      · intros b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ μ) h
    · rw [if_neg hμν]
      rw [Finset.sum_eq_zero]
      intros b _
      by_cases hμb : μ = b
      · subst hμb
        have : μ ≠ ν := hμν
        simp [this]
      · simp [hμb]
  dg_symm := by intros; rfl

/-- `euclidean n` is diagonal with diagonal components 1. -/
theorem euclidean_diagRiemannian (n : Nat) :
    DiagRiemannianMetric (euclidean n) where
  g_ii_pos := by
    intros x i
    unfold euclidean
    simp
  g_off_diag := by
    intros x μ ν hμν
    unfold euclidean
    simp [hμν]

/-- `euclidean n` as a `DiagRiemannianManifold n`. -/
noncomputable def euclideanManifold (n : Nat) : DiagRiemannianManifold n where
  toMetric := euclidean n
  riemannian := euclidean_diagRiemannian n

/-- The diagonal components of a `DiagRiemannianMetric` are positive. -/
theorem DiagRiemannianMetric.g_ii_pos_of {n : Nat} {M : MetricData n}
    (R : DiagRiemannianMetric M) (x : Fin n → ℝ) (i : Fin n) :
    0 < M.g x i i :=
  R.g_ii_pos x i

/-- For `n > 0`, the component `g_{00}` of a `DiagRiemannianMetric` is
positive at every point. -/
theorem DiagRiemannianMetric.g00_pos_at_zero {n : Nat}
    {M : MetricData n} (R : DiagRiemannianMetric M) (h : 0 < n)
    (x : Fin n → ℝ) : 0 < M.g x ⟨0, h⟩ ⟨0, h⟩ :=
  R.g_ii_pos x ⟨0, h⟩

end Curvature
end InfraFormalization
