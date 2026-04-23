/-
**Lorentzian manifold structure** (E1 / #53).

A Lorentzian manifold is a `MetricData n` whose metric has signature
`(-, +, +, ..., +)` at every point. The minus sign on the `0`-th
eigenvalue corresponds to the time direction; the rest are spatial.

This file provides:

  * `LorentzianMetric M` — the Lorentzian-signature predicate.
  * `LorentzianManifold n` — the bundled structure: `MetricData n` +
    the Lorentzian-signature witness.
  * `minkowski4_isLorentzian` — Minkowski 4-space is Lorentzian.
  * `lorentzian_g_00_neg` and `lorentzian_g_ii_pos` accessors.

**Connection to hypergraphs.** Same anchor as `CurvatureRiemann`: on
the continuum side. A future discrete Lorentzian structure on
hypergraph trajectories would pair with this via the Lorentzian
GH-limit bridge (E6 / E7, still open).

**Why this is useful.** `EinsteinEqLambda` is agnostic to signature;
`LorentzianManifold` is the data for the Lorentzian version of EFE
(the physical one).
-/

import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- **Lorentzian-signature predicate**. For a diagonal metric (our
only case of interest here), this asserts
`g_{00} < 0` and `g_{ii} > 0` for `i ≥ 1` at every point. Off-diagonal
values are required to be zero.

Real Lorentzian structure is signature-(−,+,...,+) via eigenvalue
analysis; we use the diagonal form since that's what `minkowski4`
and common exact solutions satisfy. -/
structure DiagLorentzianMetric {n : Nat} (M : MetricData n) : Prop where
  /-- `g_{00}(x) < 0` for every `x`. -/
  g_00_neg : ∀ x : Fin n → ℝ, ∀ h : 0 < n, M.g x ⟨0, h⟩ ⟨0, h⟩ < 0
  /-- `g_{ii}(x) > 0` for every `x` and every `i ≥ 1`. -/
  g_ii_pos : ∀ (x : Fin n → ℝ) (i : Fin n), 0 < i.val → 0 < M.g x i i
  /-- `g` is diagonal: off-diagonal components vanish. -/
  g_off_diag : ∀ (x : Fin n → ℝ) (μ ν : Fin n), μ ≠ ν → M.g x μ ν = 0

/-- **Lorentzian manifold structure**: a `MetricData n` together with
the Lorentzian-signature witness. -/
structure DiagLorentzianManifold (n : Nat) where
  /-- Underlying metric data. -/
  toMetric : MetricData n
  /-- Lorentzian-signature witness. -/
  lorentzian : DiagLorentzianMetric toMetric

/-- **Minkowski 4-space is Lorentzian.** `g_{00} = −1 < 0`,
`g_{ii} = +1 > 0` for `i ∈ {1,2,3}`, off-diagonal zero. -/
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

/-- **Minkowski as a `DiagLorentzianManifold`.** -/
noncomputable def minkowski4Manifold : DiagLorentzianManifold 4 where
  toMetric := minkowski4
  lorentzian := minkowski4_diagLorentzian

/-- **Timelike direction accessor**: on a Lorentzian manifold, the
time-time metric component is strictly negative. -/
theorem DiagLorentzianManifold.g_00_neg {n : Nat} (h : 0 < n)
    (L : DiagLorentzianManifold n) (x : Fin n → ℝ) :
    L.toMetric.g x ⟨0, h⟩ ⟨0, h⟩ < 0 :=
  L.lorentzian.g_00_neg x h

/-- **Spacelike components accessor**. -/
theorem DiagLorentzianManifold.g_ii_pos {n : Nat}
    (L : DiagLorentzianManifold n) (x : Fin n → ℝ) (i : Fin n) (hi : 0 < i.val) :
    0 < L.toMetric.g x i i :=
  L.lorentzian.g_ii_pos x i hi

/-- **Off-diagonal zero accessor.** -/
theorem DiagLorentzianManifold.g_off_diag {n : Nat}
    (L : DiagLorentzianManifold n) (x : Fin n → ℝ) (μ ν : Fin n) (h : μ ≠ ν) :
    L.toMetric.g x μ ν = 0 :=
  L.lorentzian.g_off_diag x μ ν h

/-- **On a diagonal-Lorentzian metric, the time-time component is
non-zero at every point.** Follows from strict negativity. -/
theorem DiagLorentzianMetric.g_00_ne_zero {n : Nat} {M : MetricData n}
    (L : DiagLorentzianMetric M) (x : Fin n → ℝ) (h : 0 < n) :
    M.g x ⟨0, h⟩ ⟨0, h⟩ ≠ 0 :=
  ne_of_lt (L.g_00_neg x h)

end Curvature
end InfraFormalization
