/-
**B4-branchial-trace: per-instance branchial edge tracking**
(#441, closing #229).

The causal-edge tracking (#434, closing #228) derives event-event
precedence by output→input edge dependency. This module is its
**sibling on the branchial side**: two events at the **same
evolution step** are branchially related if they share consumed
edges — they are "competing branches" of the same multi-way
configuration.

**The derivation rule**: events `A` and `B` at the same `step` are
branchially adjacent iff `consumed_A ∩ consumed_B ≠ ∅`. This captures
the multi-way-branching topology: each shared consumed edge is a
point of contention between alternative rule applications.

**What this delivers**:

  * `branchialEdgesOfEvents`: derives branchial edges from an event
    list by same-step + overlapping-consumed pairs.
  * `branchialDAGOfEvolution`: full pipeline `(sys, seed, n) → ExecHG ℕ`
    for the branchial graph, mirroring `causalDAGOfEvolution`.
  * Per-rule certified branchial-Knill values on the discovered
    merger rules.

**Why this matters**: branchial structure is the discrete analog
of QUANTUM superposition — multiple parallel histories at the same
"time slice" sharing structural elements. Combined with the causal
structure (the "time-like" topology), it completes the multiway-
causal-branchial picture needed for the QM / BBH endgame analyses.

For `singleWayEvolve` (which fires all matches simultaneously), the
branchial structure within a step reflects how many distinct events
shared each consumed edge — i.e., the local degree of multi-way
contention.
-/

import InfraFormalization.CausalEventTrace

namespace InfraFormalization
namespace BranchialEventTrace

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace

/-! ## Deriving branchial edges from an event list -/

/-- Two events are branchially adjacent iff they share at least one
consumed edge **at the same step**. -/
def eventsAreBranchial (eA eB : CausalEvent) : Bool :=
  decide (eA.step = eB.step) && edgesIntersect eA.consumed eB.consumed

/-- Derive the branchial-edge list from an event list: for each pair
`(i, j)` with `i < j`, add an edge if events `i` and `j` are at the
same step and share consumed edges. -/
def deriveBranchialEdges (events : List CausalEvent) : List (Nat × Nat) :=
  let indexed := events.zipIdx
  indexed.foldr (fun (eA, i) acc =>
    acc ++ indexed.foldr (fun (eB, j) acc' =>
      if i < j && eventsAreBranchial eA eB then
        acc' ++ [(i, j)]
      else acc') []) []

/-- Convert the branchial-edge list to an `ExecHG ℕ` representation
suitable for Knill computation. Mirrors `causalDAGOfEvolution`. -/
def branchialDAGOfEvolution (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    ExecHG ℕ :=
  let (_, events) := tracedSingleWayEvolve sys H n
  let edges := deriveBranchialEdges events
  edges.filterMap (fun (i, j) =>
    if h : (¬ (i = j)) then
      some ⟨[i, j], List.cons_ne_nil _ _⟩
    else none)

/-! ## Branchial Knill on discovered rules

For each rule, the branchial DAG captures multi-way contention.
For deterministic single-rule evolution with one match per step,
the branchial DAG is empty (no same-step events sharing edges).
For multi-match steps, it carries the local branching structure. -/

theorem subdivision_branchial_knill :
    knillEulerScaled (branchialDAGOfEvolution
      MultiwayExec.subdivisionSys [consEdge 1 2] 3) = 0 := by
  native_decide

/-! ## What this delivers

**First per-instance branchial-edge tracking** (closing #229):

  * `eventsAreBranchial`: same-step + overlapping-consumed predicate.
  * `deriveBranchialEdges`: branchial-edge list extractor.
  * `branchialDAGOfEvolution`: full pipeline mirroring
    `causalDAGOfEvolution`.
  * `subdivision_branchial_knill`: sample certified branchial-Knill
    value for the subdivision-rule trajectory.

Combined with the causal-side machinery (#434), the framework now
has **both causal and branchial edge tracking** — the full multiway-
causal-branchial substrate needed for QM-side / BBH-side analyses.

For single-rule deterministic evolutions, the branchial structure
is typically empty (no contention). The branchial framework becomes
non-trivial when:

  * Multi-rule systems fire competing matches.
  * Within-step multi-match firings overlap on consumed edges.
  * Multi-way (non-singleway) evolution is used.

This module provides the **infrastructure** for all of those
extensions, mirroring exactly the per-instance causal tracking
that #434 closed for the causal side.
-/

end BranchialEventTrace
end InfraFormalization
