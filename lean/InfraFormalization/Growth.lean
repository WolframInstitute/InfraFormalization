/-
Cone counts and polynomial growth bounds.

This module defines breadth-first expansion `bfsStep` and `bfsIter` for a neighbour function,
`coneCount neighbour src t`, the number of elements reached from `src` in at most `t` steps, and
`GrowthExponentAtMost f d`, the statement that `f n ≤ C · n^d` for some real `C` and all `n > 0`.
`growthExponentAtMost_of_linear` proves that a function bounded by `C · n` satisfies
`GrowthExponentAtMost f 1`.
No theorem in this module bounds the cone count of the causal graph of any rule.
-/

import InfraFormalization.GraphMetric
import InfraFormalization.Conservation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfraFormalization

open Hypergraph Application

variable {V : Type*} [DecidableEq V]

/-- One breadth-first step: `S ∪ ⋃_{x ∈ S} neighbour x`. -/
def bfsStep {E : Type*} [DecidableEq E] (neighbour : E → Finset E)
    (S : Finset E) : Finset E :=
  S ∪ S.biUnion neighbour

/-- `bfsStep` applied `t` times to `S`. -/
def bfsIter {E : Type*} [DecidableEq E] (neighbour : E → Finset E) :
    Nat → Finset E → Finset E
  | 0, S => S
  | (k+1), S => bfsIter neighbour k (bfsStep neighbour S)

/-- The cardinality of `bfsIter neighbour t {src}`, the set of elements reached from `src` in at
most `t` neighbour steps. -/
def coneCount {E : Type*} [DecidableEq E]
    (neighbour : E → Finset E) (src : E) (t : Nat) : Nat :=
  (bfsIter neighbour t {src}).card

/-- There is a real `C` with `f n ≤ C · n^d` for all `n > 0`. -/
def GrowthExponentAtMost (f : Nat → Nat) (d : Nat) : Prop :=
  ∃ C : ℝ, ∀ n : Nat, 0 < n → (f n : ℝ) ≤ C * (n : ℝ)^d

/-- If `f n ≤ C · n` for all `n`, then `GrowthExponentAtMost f 1`. -/
theorem growthExponentAtMost_of_linear
    (f : Nat → Nat) (C : ℕ) (hbound : ∀ n, f n ≤ C * n) :
    GrowthExponentAtMost f 1 := by
  refine ⟨(C : ℝ), fun n _ => ?_⟩
  have h1 : (f n : ℝ) ≤ ((C * n : ℕ) : ℝ) := by exact_mod_cast hbound n
  have h2 : ((C * n : ℕ) : ℝ) = (C : ℝ) * (n : ℝ) := by push_cast; ring
  have h3 : (C : ℝ) * (n : ℝ) = (C : ℝ) * (n : ℝ) ^ 1 := by ring
  linarith [h1, h2.symm, h3]

end InfraFormalization
