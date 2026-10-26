/-
A structure for scaled isometric embeddings with an ε-dense image.

`GHApproximation` records a map from an index type with a natural-number distance into a
space with a real distance, such that the target distance equals the source distance
divided by `scale`, and every point of the target lies within `ε` of the image. The
cycle-to-circle and path-to-interval results have this form.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfraFormalization
namespace Infra

/-- A map `f : α → Y` with values in `inTarget`, a positive `scale` with
`targetDist (f a) (f b) = sourceDist a b / scale`, and a nonnegative `ε` such that every
`y` with `inTarget y` satisfies `targetDist y (f a) ≤ ε` for some `a`.

The distances are arbitrary functions; no metric axioms are assumed. -/
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

end Infra
end InfraFormalization
