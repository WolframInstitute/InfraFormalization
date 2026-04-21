/-
**DAG-as-blowup-of-interval** (Group IA / #109).

Infraanalysis treats a 1-dimensional oriented hypergraph as a
*blowup* of the real interval `[0, 1]`: the `n`-vertex path
hypergraph, with edges oriented left→right, is the minimal model of
an interval at resolution `n`. Calculus on this DAG (forward
differences) reproduces classical 1D calculus in the `n → ∞` limit.

This file formalises:

  * `dagAsBlowupOfInterval n : Hypergraph (Fin n)` — the linear
    chain `0 → 1 → 2 → ... → n−1`.
  * `dagDerivative f i` — forward difference `f(i+1) − f(i)`.
  * Linearity.

The integral (telescoping sum) and fundamental theorem are deferred
to `Mathlib.Data.Nat.Interval` availability in follow-up work.

**Connection to hypergraphs.** Native. `dagAsBlowupOfInterval n` is
a concrete `Hypergraph (Fin n)` state; `dagDerivative` acts on
vertex-functions.
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace InfraFormalization

/-- **The `k`-th directed edge of the DAG**: `[k, k+1]` in `Fin n`
(for `k + 1 < n`). -/
def dagEdge (n : Nat) (k : Nat) (hk : k + 1 < n) : Hyperedge (Fin n) :=
  { verts := [⟨k, by omega⟩, ⟨k + 1, hk⟩],
    nonempty := by simp }

/-- **The DAG-as-blowup-of-interval `[0, 1]`** at resolution `n`:
a `Hypergraph (Fin n)` whose edges are `[k, k+1]` for `0 ≤ k < n−1`.
Directed (left-to-right) by the ordering of `verts`. -/
def dagAsBlowupOfInterval (n : Nat) : Hypergraph (Fin n) :=
  { edges := ((List.range (n - 1)).attach.map
      (fun ⟨k, hk⟩ =>
        dagEdge n k (by
          have : k < n - 1 := List.mem_range.mp hk
          omega))) }

/-- **Forward difference** at vertex `i` (for `i + 1 < n`):
`Δf(i) := f(i+1) − f(i)`. -/
def dagDerivative {n : Nat} (f : Fin n → ℝ) (i : Fin n)
    (hi : i.val + 1 < n) : ℝ :=
  f ⟨i.val + 1, hi⟩ - f i

/-- **Forward difference is additive.** -/
theorem dagDerivative_add {n : Nat} (f g : Fin n → ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    dagDerivative (fun v => f v + g v) i hi
    = dagDerivative f i hi + dagDerivative g i hi := by
  unfold dagDerivative
  ring

/-- **Forward difference is linear.** -/
theorem dagDerivative_smul {n : Nat} (c : ℝ) (f : Fin n → ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    dagDerivative (fun v => c * f v) i hi = c * dagDerivative f i hi := by
  unfold dagDerivative
  ring

/-- **Constants have zero forward difference.** -/
theorem dagDerivative_const {n : Nat} (c : ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    dagDerivative (fun _ => c) i hi = 0 := by
  unfold dagDerivative
  ring

end InfraFormalization
