import InfraFormalization.CurvatureLocalCoord

/-!
**Riemannian manifold structure** (C1 / #34).

A Riemannian manifold is a `MetricData n` whose metric is
positive-definite at every point. Unlike `DiagLorentzianMetric` (signature
`(-, +, ..., +)`), the Riemannian version requires all diagonal
entries to be positive.

This module provides:

* `DiagRiemannianMetric M`: diagonal + positive-definite predicate.
* `DiagRiemannianManifold n`: bundled structure (MetricData + Riemannian witness).
* `euclidean n`: the flat Euclidean metric on `ℝⁿ` (`g = I`).
* `euclidean_diagRiemannian`: Euclidean space is Riemannian.

**Design note.** The task description (C1) asks for
`RiemannianMetric M` as "a smooth section of Sym²(T*M) for a smooth
manifold M (via Mathlib's charted-space + bundle API)". Project policy
(see `project_overview.md`) uses `MetricData n` — Christoffel-level
raw components on `ℝⁿ` — as the working substrate, matching how
`DiagLorentzianMetric`, `Schwarzschild`, `FLRW`, etc. are all stated.
The Mathlib `ChartedSpace`/`VectorBundle`/`TensorProduct` integration
is deferred as a separate future task; it would sit *above* this
predicate, not replace it.

**Connection to hypergraphs.** The same anchor pattern as
`LorentzianManifold`: continuum side. A concrete hypergraph →
Riemannian-metric bridge needs a positive-definite discrete analog
(e.g. scaled graph metric), out of scope here.
-/

namespace InfraFormalization
namespace Curvature

/-- **Riemannian-signature predicate**: diagonal and strictly positive
`g_{μμ}(x) > 0` at every point, off-diagonal zero. Matches the
shape of `DiagLorentzianMetric` (diagonal + fixed-signature) but
with all-positive eigenvalues instead of signature `(-,+,...,+)`. -/
structure DiagRiemannianMetric {n : Nat} (M : MetricData n) : Prop where
  /-- `g_{ii}(x) > 0` for every `x` and every `i`. -/
  g_ii_pos : ∀ (x : Fin n → ℝ) (i : Fin n), 0 < M.g x i i
  /-- `g` is diagonal: off-diagonal components vanish. -/
  g_off_diag : ∀ (x : Fin n → ℝ) (μ ν : Fin n), μ ≠ ν → M.g x μ ν = 0

/-- **Riemannian manifold structure**: a `MetricData n` together with
the Riemannian positive-definite witness. -/
structure DiagRiemannianManifold (n : Nat) where
  /-- Underlying metric data. -/
  toMetric : MetricData n
  /-- Positive-definite-signature witness. -/
  riemannian : DiagRiemannianMetric toMetric

/-- **Euclidean metric on ℝⁿ**: `g_{μν} = δ_{μν}` (identity matrix
at every point). Represents flat Euclidean space. -/
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

/-- **Euclidean is Riemannian** (positive-definite). `g_{ii} = 1 > 0`,
off-diagonal zero. -/
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

/-- **Euclidean as a `DiagRiemannianManifold`.** -/
noncomputable def euclideanManifold (n : Nat) : DiagRiemannianManifold n where
  toMetric := euclidean n
  riemannian := euclidean_diagRiemannian n

/-- **Diagonal entries of a Riemannian metric are positive.** Accessor
for the common use case. -/
theorem DiagRiemannianMetric.g_ii_pos_of {n : Nat} {M : MetricData n}
    (R : DiagRiemannianMetric M) (x : Fin n → ℝ) (i : Fin n) :
    0 < M.g x i i :=
  R.g_ii_pos x i

/-- **A Riemannian metric has no mixed signature**: at every point and
every diagonal entry, the sign is positive (vs. Lorentzian which has
one negative and the rest positive). This theorem asserts the
sign-distinction at the definitional level. -/
theorem DiagRiemannianMetric.not_lorentzian_at_zero {n : Nat}
    {M : MetricData n} (R : DiagRiemannianMetric M) (h : 0 < n)
    (x : Fin n → ℝ) : 0 < M.g x ⟨0, h⟩ ⟨0, h⟩ :=
  R.g_ii_pos x ⟨0, h⟩

end Curvature
end InfraFormalization
