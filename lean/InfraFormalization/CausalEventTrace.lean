/-
**B4-causal-trace: per-instance causal event tracking from rule
evolution** (#434, closing #228).

The earlier `CausalDAGKnill` module (#432) applied Knill to
hand-encoded causal-DAG topologies. This module closes the loop by
**deriving causal DAGs directly from rule evolution**: each rule
application becomes a `CausalEvent` carrying its consumed and
produced edges, and a causal edge `A → B` is inferred whenever
event `A` produces an edge that event `B` later consumes.

**What this delivers**:

  * `CausalEvent` structure: (step, matchIndex, ruleIndex, consumed,
    produced).
  * `tracedSingleWayStep`: like `singleWayStep` but emits the event
    list alongside the new state.
  * `tracedSingleWayEvolve`: runs `n` steps, returns the full event
    list.
  * `deriveCausalEdges`: derives causal precedence as edges
    `(eventIdx_i, eventIdx_j)` when any of event_i's produced edges
    occurs in event_j's consumed multiset.
  * `causalDAGOfEvolution`: full pipeline trajectory → causal DAG
    (as `ExecHG ℕ`, ready for Knill).
  * Knill-certified examples on subdivision-rule evolutions.

**Why this matters**: this is the **first execution-level extraction
of causal-edge tracking** from rule output in the codebase, closing
the long-standing #228 task. Combined with the Knill causal-DAG
analysis (#432), this enables **end-to-end "rule → causal DAG →
topological invariant"** pipelines — the substrate the BBH endgame
(#225, H6-H9) needs for discrete-Ψ₄ extraction.
-/

import InfraFormalization.CausalDAGKnill
import InfraFormalization.SubdivisionPath

namespace InfraFormalization
namespace CausalEventTrace

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalDAGKnill

/-! ## Causal event structure -/

/-- A `CausalEvent`: one rule application within a single-way
evolution, carrying its step index, intra-step match index, rule
index within the system, and the consumed/produced edges. -/
structure CausalEvent where
  step       : Nat
  matchIdx   : Nat
  ruleIdx    : Nat
  consumed   : ExecHG ℕ
  produced   : ExecHG ℕ

/-! ## Traced single-way step

Mirror `singleWayStep` (lines 222-240 of MultiwayExec.lean) but emit
per-match events alongside. Same algorithm: enumerate matches per
rule, apply with fresh-vertex offset, record consumed and produced. -/

/-- Traced version of `singleWayStep`. Returns `(new state, events
for this step)`. Mirrors `singleWayStep` but emits one
`CausalEvent` per match. -/
def tracedSingleWayStep (sys : ExecSystem) (H : ExecHG ℕ) (step : Nat) :
    ExecHG ℕ × List CausalEvent :=
  let baseFresh := nextFresh H
  let final := sys.rules.foldl
    (fun (acc : ExecHG ℕ × Nat × Nat × List CausalEvent) (r : ExecRule) =>
      let (state, offset, ruleIdx, events) := acc
      let matchRes := (allMatches r H).foldl
        (fun (acc' : ExecHG ℕ × Nat × Nat × List CausalEvent)
             (ρ : Fin r.numBound → ℕ) =>
          let (state', offset', rIdx, events') := acc'
          let consumed : ExecHG ℕ := mapPattern ρ r.lhs
          let ρExt : Fin (r.numBound + r.numFresh) → ℕ := fun i =>
            if h : i.val < r.numBound then ρ ⟨i.val, h⟩
            else baseFresh + offset' + (i.val - r.numBound)
          let produced : ExecHG ℕ := mapPattern ρExt r.rhs
          let event : CausalEvent :=
            { step := step
              matchIdx := events'.length
              ruleIdx := rIdx
              consumed := consumed
              produced := produced }
          (removeEdges state' consumed ++ produced,
           offset' + r.numFresh,
           rIdx,
           events' ++ [event]))
        (state, offset, ruleIdx, events)
      (matchRes.1, matchRes.2.1, ruleIdx + 1, matchRes.2.2.2))
    (H, 0, 0, [])
  (final.1, final.2.2.2)

/-- Traced version of `singleWayEvolve`. Returns `(final state, all
events collected across n steps)`. -/
def tracedSingleWayEvolve (sys : ExecSystem) (H : ExecHG ℕ) :
    Nat → ExecHG ℕ × List CausalEvent
  | 0 => (H, [])
  | n + 1 =>
    let (state_n, events_n) := tracedSingleWayEvolve sys H n
    let (state_n1, events_n1) := tracedSingleWayStep sys state_n n
    (state_n1, events_n ++ events_n1)

/-! ## Causal edge derivation

Event `A` causally precedes event `B` iff some edge in `A.produced`
is also in `B.consumed`. -/

/-- Boolean: does any edge appear in both `produced_A` and
`consumed_B`? -/
def edgesIntersect (produced_A consumed_B : ExecHG ℕ) : Bool :=
  produced_A.any (fun e => consumed_B.any (fun e' => decide (e = e')))

/-- Derive the causal-edge list from an event list. For each pair
`(i, j)` with `i < j` (event indices), add an edge if event_i's
produced edges intersect event_j's consumed edges. -/
def deriveCausalEdges (events : List CausalEvent) : List (Nat × Nat) :=
  let indexed := events.zipIdx
  indexed.foldr (fun (eA, i) acc =>
    acc ++ indexed.foldr (fun (eB, j) acc' =>
      if i < j && edgesIntersect eA.produced eB.consumed then
        acc' ++ [(i, j)]
      else acc') []) []

/-- Convert the causal-edge list to an `ExecHG ℕ` representation
suitable for Knill computation. -/
def causalDAGOfEvolution (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    ExecHG ℕ :=
  let (_, events) := tracedSingleWayEvolve sys H n
  let edges := deriveCausalEdges events
  edges.filterMap (fun (i, j) =>
    if h : (¬ (i = j)) then
      some ⟨[i, j], List.cons_ne_nil _ _⟩
    else none)

/-! ## Subdivision-rule causal DAG examples

For the subdivision rule on a single edge: at step 0 the seed has
one edge. At step 1, the single match consumes that edge and
produces 2 new edges (the subdivided pieces). At step 2, the 2
edges each subdivide into 2 more. Each step-1 event's produced
edges are consumed by 2 step-2 events.

So the causal DAG of `subdivisionSys` on edge12 over 2 steps
looks like:

  event_0 (step 0 → 1)
     │
     ├──→ event_1 (step 1 → 2, consumes first piece)
     │
     └──→ event_2 (step 1 → 2, consumes second piece)

That's a fork from event_0 to event_1 and event_2: 3 events, 2
causal edges, tree topology (χ = 1, Knill = 6). -/

/-- The subdivision-rule trajectory's causal DAG at depth 2:
1 event at step 0 + 2 events at step 1 = 3 events, fork pattern. -/
def subdivisionCausalDAG_depth2 : ExecHG ℕ :=
  causalDAGOfEvolution subdivisionSys [consEdge 1 2] 2

/-- Knill of the depth-2 subdivision causal DAG = 6 (fork = tree). -/
theorem subdivision_depth2_causalDAG_knill :
    knillEulerScaled subdivisionCausalDAG_depth2 = 6 := by native_decide

/-- The subdivision-rule trajectory at depth 1: a single event. -/
def subdivisionCausalDAG_depth1 : ExecHG ℕ :=
  causalDAGOfEvolution subdivisionSys [consEdge 1 2] 1

/-- Knill of a single-event causal DAG: empty edges, K6 not applicable
to the trivial 0-vertex case. Computes to 0. -/
theorem subdivision_depth1_causalDAG_knill :
    knillEulerScaled subdivisionCausalDAG_depth1 = 0 := by native_decide

/-! ## End-to-end pipeline theorem

The full chain `rule → traced evolution → causal events → causal DAG
→ Knill` works correctly on the subdivision example. -/

/-- **`causal_pipeline_subdivision_depth2`**: the end-to-end causal
pipeline applied to subdivisionRule on edge12 at depth 2 produces a
causal DAG with Knill = 6, matching the fork-tree topology
expectation. -/
theorem causal_pipeline_subdivision_depth2 :
    knillEulerScaled
      (causalDAGOfEvolution subdivisionSys [consEdge 1 2] 2) = 6 := by
  native_decide

/-! ## What this delivers

**First execution-level causal-edge extraction** (closing #228):

  * `CausalEvent` structure: per-match event data.
  * `tracedSingleWayStep` / `tracedSingleWayEvolve`: emit events
    alongside state evolution.
  * `deriveCausalEdges`: edge-dependency-based causal precedence.
  * `causalDAGOfEvolution`: full pipeline `trajectory → causal DAG`.
  * Knill-certified on subdivision-rule trajectories at depths 1, 2.
  * End-to-end pipeline theorem
    `causal_pipeline_subdivision_depth2`: rule + seed → causal DAG
    → Knill = 6 = `6·χ(tree)`.

**Why this matters**: combined with #432 (Knill on causal-DAG
topologies) and #431 (rule-catalog universal topology preservation),
the codebase now has a **complete loop** from rule definitions to
topological invariants of their causal evolution. This is the
infrastructure the BBH endgame (#225, H6-H9) needs: given a rule,
compute its causal DAG, apply Knill, and read off discrete topology
observables (Euler characteristic, hole-count, merger-event count).

The subdivision rule's depth-2 causal DAG is a 1-fork (3 events,
2 causal edges, tree topology). More complex rules will produce
more intricate causal DAGs — the framework handles them uniformly.
-/

end CausalEventTrace
end InfraFormalization
