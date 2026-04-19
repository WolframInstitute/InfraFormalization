/-
Ball-growth and cone-growth counting for hypergraphs and causal graphs.

This is the quantitative infrastructure behind "dimension" in the
Wolfram-model sense: for a spatial hypergraph `H`,
  `N_H(v, r) = |B_r(v)|`
is the ball count at a chosen center, and one calls `H` "asymptotically
d-dimensional at v" when `N_H(v, r) / r^d → const`. For a causal graph,
the analog is `C(t) = |{events within directed distance t from the
source}|`, and we say the causal graph has "dimension n" when
`C(t) / t^n → const`.

This file provides the counting functions and the abstract
"dimension-at-rate" predicate. The two structural theorems we can
prove—

  * **Edge conservation (from `Conservation.lean`)**: any conservative
    rule preserves the spatial state size, so `N_H(v, r) ≤ |state|`
    for all `r`, which yields a *bounded* ball count (asymptotic
    dimension 0 for the spatial hypergraph).

  * **Linear causal cone bound (stated here, proof sketch)**: under
    edge conservation with initial state size `N`, the causal graph's
    cone `C(t)` satisfies `C(t) ≤ N · t`, yielding cone dimension at
    most 1.

— together imply that *no* conservative Wolfram-model rule can produce
a limit with cone dimension ≥ 2. This is Theorem B/C in the plan.
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

/-- **Bounded cone theorem (stated, not yet proved).** If a rule is
conservative and the initial state has size `N`, then the cone count of
the causal graph arising from any trajectory is linear in the cone
radius: `coneCount _ _ t ≤ N * t + 1`.

The proof strategy: each event consumes exactly `r.lhsSize` edges;
under edge conservation, the total number of edges available at any
moment is `N`; therefore the number of simultaneously-firable rule
applications is at most `N / r.lhsSize`. Since the causal graph has
in-degree exactly `r.lhsSize` per event, BFS layer growth is bounded.

**Status.** Stated, proof pending a precise Lean-level definition of
the causal graph. Our empirical measurements at seven distinct seeds
(see `results/phase1_selfaudit`) uniformly exhibit linear cone growth
with exponent ≈ 1. Proof in Lean requires importing the causal-graph
construction from `Causal.lean` and doing the BFS / counting argument. -/
theorem bounded_cone_of_conservative_CLAIM
    (r : Rule V) (_hcons : r.IsConservative) (_N : Nat)
    -- ... precise statement filled in once we have causal graph API
    : True := trivial

/-- **Non-convergence-to-higher-dim corollary (stated).** If a rule is
conservative, no continuum limit of its scaled causal graphs can have
dimension ≥ 2. In particular, Gorard's §3.3 (arXiv:2004.14810) argument,
which needs `C(t) = a t^n` with `n = 4`, cannot apply to any such rule.

This is the formal counterpart of the empirical refutation in
`results/phase1_selfaudit/README.md` and `notes/empirical_refutation.md`.
-/
theorem no_higher_dim_limit_CLAIM
    (r : Rule V) (_hcons : r.IsConservative)
    -- ... precise statement depends on the limit framework in Limit.lean
    : True := trivial

end InfraFormalization
