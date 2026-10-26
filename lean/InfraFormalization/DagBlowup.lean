/-
The path hypergraph on `Fin n` and its forward difference.

This module defines `dagAsBlowupOfInterval n`, the hypergraph on `Fin n`
with edges `[k, k+1]` for `k < n − 1`, and the forward difference
`dagDerivative f i = f(i+1) − f(i)`. It proves that the forward difference
is additive, commutes with scalar multiplication, and vanishes on constants.
No limit `n → ∞` is stated.
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace InfraFormalization

/-- The hyperedge `[k, k+1]` in `Fin n`, for `k + 1 < n`. -/
def dagEdge (n : Nat) (k : Nat) (hk : k + 1 < n) : Hyperedge (Fin n) :=
  { verts := [⟨k, by omega⟩, ⟨k + 1, hk⟩],
    nonempty := by simp }

/-- The hypergraph on `Fin n` whose edges are `[k, k+1]` for
`0 ≤ k < n−1`. -/
def dagAsBlowupOfInterval (n : Nat) : Hypergraph (Fin n) :=
  { edges := ((List.range (n - 1)).attach.map
      (fun ⟨k, hk⟩ =>
        dagEdge n k (by
          have : k < n - 1 := List.mem_range.mp hk
          omega))) }

/-- The forward difference `f(i+1) − f(i)`, for `i + 1 < n`. -/
def dagDerivative {n : Nat} (f : Fin n → ℝ) (i : Fin n)
    (hi : i.val + 1 < n) : ℝ :=
  f ⟨i.val + 1, hi⟩ - f i

/-- The forward difference of `f + g` is the sum of the forward
differences. -/
theorem dagDerivative_add {n : Nat} (f g : Fin n → ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    dagDerivative (fun v => f v + g v) i hi
    = dagDerivative f i hi + dagDerivative g i hi := by
  unfold dagDerivative
  ring

/-- The forward difference of `c * f` is `c` times the forward difference
of `f`. -/
theorem dagDerivative_smul {n : Nat} (c : ℝ) (f : Fin n → ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    dagDerivative (fun v => c * f v) i hi = c * dagDerivative f i hi := by
  unfold dagDerivative
  ring

/-- The forward difference of a constant function is 0. -/
theorem dagDerivative_const {n : Nat} (c : ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    dagDerivative (fun _ => c) i hi = 0 := by
  unfold dagDerivative
  ring

end InfraFormalization
