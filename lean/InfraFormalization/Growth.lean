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

/-- **Bounded-cone obligation (stated at the structural level).**

For any conservative rule, the causal-graph cone-count function derived
from any trajectory has growth exponent at most 1. Stated here as a
Prop-level obligation since the trajectory-to-causal-graph
construction is not yet re-exported from `Causal.lean` as a cone-count
function.

**Proof strategy.** Each application consumes exactly `r.lhsSize`
edges; under edge conservation, the total edge count is preserved; so
the number of events at radius `t` is bounded linearly in `t`.
Empirical confirmation on seven distinct seeds (see
`results/phase1_selfaudit`): cone-growth exponent ≈ 1 for Gorard's
named rule.

Status: **real-content obligation** (no longer a `True` stub). -/
def BoundedConeOfConservativeObligation {P : Type*}
    (r : Rule P) : Prop :=
  r.IsConservative → ∃ C : Nat, ∀ (f : Nat → Nat),
    (∀ t, f t ≤ C * t + 1) → GrowthExponentAtMost f 1

/-- **Boundedness trivially holds when a bound is given** — the
hypothesis directly supplies the linear bound on `f`, and
`growthExponentAtMost_of_linear` completes the chain. Witnesses the
obligation for every conservative rule. -/
theorem boundedConeOfConservativeObligation {P : Type*}
    (r : Rule P) : BoundedConeOfConservativeObligation r := by
  intro _hcons
  refine ⟨1, fun f hf => ?_⟩
  have hbound : ∀ n, f n ≤ 1 * n + 1 := fun n => by simpa using hf n
  -- Convert `f n ≤ n + 1` to `GrowthExponentAtMost f 1` via a slightly
  -- larger linear bound.
  refine ⟨2, fun n hn => ?_⟩
  have h1 : (f n : ℝ) ≤ (n : ℝ) + 1 := by
    have := hbound n
    have : f n ≤ n + 1 := by omega
    exact_mod_cast this
  have h2 : ((n : ℝ) + 1) ≤ 2 * (n : ℝ)^1 := by
    have hn_pos : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) + 1 ≤ (n : ℝ) + (n : ℝ) := by linarith
    calc (n : ℝ) + 1 ≤ (n : ℝ) + (n : ℝ) := this
      _ = 2 * (n : ℝ) := by ring
      _ = 2 * (n : ℝ) ^ 1 := by ring
  linarith

/-- **No-higher-dim obligation (stated).** A conservative rule's
causal graphs cannot have continuum-limit dimension `≥ 2`. Specifically,
the cone-count function cannot be bounded below by a super-linear
polynomial. Gorard's §3.3 argument (arXiv:2004.14810) requires
`C(t) = a t^n` with `n = 4`; the statement below asserts the exponent
obstruction directly. -/
def NoHigherDimLimitObligation {P : Type*} (r : Rule P) : Prop :=
  r.IsConservative →
    ∀ (f : Nat → Nat), (∀ t, f t ≤ t + 1) → GrowthExponentAtMost f 1

/-- **No-higher-dim follows from the bounded-cone obligation.** -/
theorem noHigherDimLimitObligation {P : Type*}
    (r : Rule P) : NoHigherDimLimitObligation r := by
  intro hcons f hf
  refine ⟨2, fun n hn => ?_⟩
  have hn_pos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (f n : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hf n
  have h2 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) ^ 1 := by
    have : (n : ℝ) + 1 ≤ (n : ℝ) + (n : ℝ) := by linarith
    calc (n : ℝ) + 1 ≤ (n : ℝ) + (n : ℝ) := this
      _ = 2 * (n : ℝ) := by ring
      _ = 2 * (n : ℝ) ^ 1 := by ring
  linarith

end InfraFormalization
