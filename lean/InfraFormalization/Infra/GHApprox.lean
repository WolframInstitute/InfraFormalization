/-
Abstract Gromov–Hausdorff approximation structure.

The cycle → circle and path → interval theorems share a common
form: there is a map from a (discrete) index type to a continuum
metric space, the map is distance-preserving (up to a fixed scaling
factor), and its image is ε-Hausdorff-dense in the target.

This file packages that common form as a single structure
`GHApproximation`, giving us a template for all future
continuum-limit theorems in the infrageometry programme.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfraFormalization
namespace Infra

/-- A **Gromov–Hausdorff approximation** of a target metric structure
by a finite discrete one.

Concretely: a map `f : α → Y` (the "embedding"), a scaling factor
`1 / scale` such that
`targetDist (f i) (f j) = sourceDist i j / scale`, and an
ε-Hausdorff-cover property: every point of `Y` (satisfying a
`inTarget` predicate) is within `targetDist` ε of some `f i`.

This is a direct-form ε-GH bound: `GH_dist(source, target) ≤ ε`.

Abstractions chosen for portability:
- `inTarget y` marks which `y : Y` values are considered "in the
  target space" (needed for the cover condition);
- `sourceDist : α → α → Nat` and `scale : ℝ` encode the scaling of
  the source metric (e.g., the graph distance on `Fin n` divided by
  `n`);
- `targetDist : Y → Y → ℝ` is the target metric (e.g., circle or
  interval distance).
-/
structure GHApproximation
    (α : Type*) (Y : Type*)
    (sourceDist : α → α → Nat)
    (targetDist : Y → Y → ℝ)
    (inTarget : Y → Prop)
    where
  f : α → Y
  scale : ℝ
  scale_pos : 0 < scale
  f_in_target : ∀ a, inTarget (f a)
  isometry : ∀ a b, targetDist (f a) (f b) = (sourceDist a b : ℝ) / scale
  ε : ℝ
  ε_nonneg : 0 ≤ ε
  covers : ∀ y, inTarget y → ∃ a, targetDist y (f a) ≤ ε

/-- The existence of a GHApproximation with error `ε = 1/(2·scale)`
is the universal form of both `cycle_circle_gh_bound` and
`path_interval_gh_bound`. -/
theorem ghApprox_of_half_scale
    {α Y : Type*}
    {sourceDist : α → α → Nat}
    {targetDist : Y → Y → ℝ}
    {inTarget : Y → Prop}
    (a : GHApproximation α Y sourceDist targetDist inTarget)
    (h_ε : a.ε = 1 / (2 * a.scale)) :
    ∃ (f : α → Y),
      (∀ x, inTarget (f x)) ∧
      (∀ x y, targetDist (f x) (f y) = (sourceDist x y : ℝ) / a.scale) ∧
      (∀ y, inTarget y → ∃ x, targetDist y (f x) ≤ 1 / (2 * a.scale)) :=
  ⟨a.f, a.f_in_target, a.isometry, fun y hy => by
    obtain ⟨x, hx⟩ := a.covers y hy
    exact ⟨x, h_ε ▸ hx⟩⟩

end Infra
end InfraFormalization
