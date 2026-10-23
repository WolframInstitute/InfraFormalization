/-
Ball-count and cone-count functions for hypergraphs and causal graphs.

For a spatial hypergraph `H`, `N_H(v, r) = |B_r(v)|` is the number of
vertices within distance `r` of `v`. For a causal graph,
`C(t)` is the number of events within directed distance `t` of a
source event (`coneCount`). `GrowthExponentAtMost f d` states that
`f n ≤ C · n^d` for some constant `C` and all `n > 0`.

`growthExponentAtMost_of_linear` proves that a function bounded by
`C · n` has growth exponent at most 1. No theorem in this file bounds
the cone count of the causal graph of any rule. The statement such a
bound needs for the rule of arXiv:2102.09363 is listed as OPEN in
`STATUS_OF_GORARD_CLAIMS.md`.
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

/-- BFS expansion step. -/
def bfsStep {E : Type*} [DecidableEq E] (neighbour : E → Finset E)
    (S : Finset E) : Finset E :=
  S ∪ S.biUnion neighbour

/-- Iterated BFS. After `t` iterations, contains every element reachable
from the starting set within `t` neighbour-steps. -/
def bfsIter {E : Type*} [DecidableEq E] (neighbour : E → Finset E) :
    Nat → Finset E → Finset E
  | 0, S => S
  | (k+1), S => bfsIter neighbour k (bfsStep neighbour S)

/-- **Cone count.** For a causal graph (here represented abstractly as
a function assigning each event a neighbour set), `C(src, t)` is the
number of events at directed distance ≤ `t` from `src`. -/
def coneCount {E : Type*} [DecidableEq E]
    (neighbour : E → Finset E) (src : E) (t : Nat) : Nat :=
  (bfsIter neighbour t {src}).card

/-- **Dimension-at-rate**. A function `f : ℕ → ℕ` has "growth exponent
at most d" iff `f n / n^d` is bounded. Used to say "the causal graph
has cone dimension at most d". -/
def GrowthExponentAtMost (f : Nat → Nat) (d : Nat) : Prop :=
  ∃ C : ℝ, ∀ n : Nat, 0 < n → (f n : ℝ) ≤ C * (n : ℝ)^d

/-- Trivial bound: any function bounded by `C n` has growth exponent ≤ 1. -/
theorem growthExponentAtMost_of_linear
    (f : Nat → Nat) (C : ℕ) (hbound : ∀ n, f n ≤ C * n) :
    GrowthExponentAtMost f 1 := by
  refine ⟨(C : ℝ), fun n _ => ?_⟩
  have h1 : (f n : ℝ) ≤ ((C * n : ℕ) : ℝ) := by exact_mod_cast hbound n
  have h2 : ((C * n : ℕ) : ℝ) = (C : ℝ) * (n : ℝ) := by push_cast; ring
  have h3 : (C : ℝ) * (n : ℝ) = (C : ℝ) * (n : ℝ) ^ 1 := by ring
  linarith [h1, h2.symm, h3]

end InfraFormalization
