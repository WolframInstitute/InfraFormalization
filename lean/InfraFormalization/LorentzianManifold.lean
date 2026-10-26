/-
Diagonal metrics of Lorentzian signature.

This module defines `DiagLorentzianMetric M` for `M : MetricData n`: the metric is diagonal with
`g_{00} < 0` and `g_{ii} > 0` for `i ≥ 1` at every point. It defines the bundled structure
`DiagLorentzianManifold n`, proves that `minkowski4` satisfies the predicate, and provides accessors
for the sign conditions. Non-diagonal metrics of signature `(−, +, …, +)` are not covered.
-/

import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- The metric is diagonal, `g_{00} < 0` and `g_{ii} > 0` for `i ≥ 1`, at every point. -/
structure DiagLorentzianMetric {n : Nat} (M : MetricData n) : Prop where
  /-- `g_{00}(x) < 0` for every `x`. -/
  g_00_neg : ∀ x : Fin n → ℝ, ∀ h : 0 < n, M.g x ⟨0, h⟩ ⟨0, h⟩ < 0
  /-- `g_{ii}(x) > 0` for every `x` and every `i ≥ 1`. -/
  g_ii_pos : ∀ (x : Fin n → ℝ) (i : Fin n), 0 < i.val → 0 < M.g x i i
  /-- `g` is diagonal: off-diagonal components vanish. -/
  g_off_diag : ∀ (x : Fin n → ℝ) (μ ν : Fin n), μ ≠ ν → M.g x μ ν = 0

/-- A `MetricData n` together with a proof of `DiagLorentzianMetric`. -/
structure DiagLorentzianManifold (n : Nat) where
  /-- Underlying metric data. -/
  toMetric : MetricData n
  /-- Lorentzian-signature witness. -/
  lorentzian : DiagLorentzianMetric toMetric

/-- `minkowski4` satisfies `DiagLorentzianMetric`: `g_{00} = −1`, `g_{ii} = 1` for `i ∈ {1, 2, 3}`,
and the off-diagonal components are 0. -/
theorem minkowski4_diagLorentzian : DiagLorentzianMetric minkowski4 where
  g_00_neg := by
    intros x _
    unfold minkowski4
    simp
  g_ii_pos := by
    intros x i hi
    unfold minkowski4
    -- On minkowski4, g x i i = if i.val = 0 then -1 else 1.
    fin_cases i <;> simp_all
  g_off_diag := by
    intros x μ ν hμν
    unfold minkowski4
    fin_cases μ <;> fin_cases ν <;> simp_all

/-- `minkowski4` as a `DiagLorentzianManifold 4`. -/
noncomputable def minkowski4Manifold : DiagLorentzianManifold 4 where
  toMetric := minkowski4
  lorentzian := minkowski4_diagLorentzian

/-- `g_{00}(x) < 0`. -/
theorem DiagLorentzianManifold.g_00_neg {n : Nat} (h : 0 < n)
    (L : DiagLorentzianManifold n) (x : Fin n → ℝ) :
    L.toMetric.g x ⟨0, h⟩ ⟨0, h⟩ < 0 :=
  L.lorentzian.g_00_neg x h

/-- `g_{ii}(x) > 0` for `i ≥ 1`. -/
theorem DiagLorentzianManifold.g_ii_pos {n : Nat}
    (L : DiagLorentzianManifold n) (x : Fin n → ℝ) (i : Fin n) (hi : 0 < i.val) :
    0 < L.toMetric.g x i i :=
  L.lorentzian.g_ii_pos x i hi

/-- `g_{μν}(x) = 0` for `μ ≠ ν`. -/
theorem DiagLorentzianManifold.g_off_diag {n : Nat}
    (L : DiagLorentzianManifold n) (x : Fin n → ℝ) (μ ν : Fin n) (h : μ ≠ ν) :
    L.toMetric.g x μ ν = 0 :=
  L.lorentzian.g_off_diag x μ ν h

/-- `g_{00}(x) ≠ 0`. -/
theorem DiagLorentzianMetric.g_00_ne_zero {n : Nat} {M : MetricData n}
    (L : DiagLorentzianMetric M) (x : Fin n → ℝ) (h : 0 < n) :
    M.g x ⟨0, h⟩ ⟨0, h⟩ ≠ 0 :=
  ne_of_lt (L.g_00_neg x h)

end Curvature
end InfraFormalization
