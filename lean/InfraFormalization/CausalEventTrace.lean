/-
Events of a traced single-way evolution and the causal edges derived
from them.

`tracedSingleWayStep` returns the state of `singleWayStep` and one
`CausalEvent` per fired match. `deriveCausalEdges` adds an edge `i → j`
for `i < j` when an edge value produced by event `i` occurs among the
edge values consumed by event `j`. The comparison is on edge values, so
when a state holds equal hyperedges produced by different events the
derived edges include pairs that are not causal edges of the evolution.
`CausalHistory.lean` defines the causal graph on hyperedge identities.
The module also defines the traced fire-all operator and computes, by `native_decide`,
`knillEulerScaled` of two small causal graphs of the subdivision rule.
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

/-- One rule application: its step index, its match index within the step, the index of
its rule in the system, and the consumed and produced edges. -/
structure CausalEvent where
  step       : Nat
  matchIdx   : Nat
  ruleIdx    : Nat
  consumed   : ExecHG ℕ
  produced   : ExecHG ℕ

/-! ## Traced single-way step

`tracedSingleWayStep` returns the state of `singleWayStep` together with
one `CausalEvent` per fired match of `stepFold`. -/

/-- The state of `singleWayStep sys H` and the events of the step. -/
def tracedSingleWayStep (sys : ExecSystem) (H : ExecHG ℕ) (step : Nat) :
    ExecHG ℕ × List CausalEvent :=
  let acc := stepFold sys H
  (acc.avail ++ acc.produced,
   acc.fired.zipIdx.map (fun (f, k) =>
     { step := step, matchIdx := k, ruleIdx := f.1,
       consumed := f.2.1, produced := f.2.2 }))

/-- The first component of `tracedSingleWayStep` is `singleWayStep`. -/
theorem tracedSingleWayStep_fst (sys : ExecSystem) (H : ExecHG ℕ) (step : Nat) :
    (tracedSingleWayStep sys H step).1 = singleWayStep sys H := rfl

/-- `n` iterations of `tracedSingleWayStep`: the final state and the events of all `n`
steps. -/
def tracedSingleWayEvolve (sys : ExecSystem) (H : ExecHG ℕ) :
    Nat → ExecHG ℕ × List CausalEvent
  | 0 => (H, [])
  | n + 1 =>
    let (state_n, events_n) := tracedSingleWayEvolve sys H n
    let (state_n1, events_n1) := tracedSingleWayStep sys state_n n
    (state_n1, events_n ++ events_n1)

/-- The fire-all step with events: the state of `fireAllStep sys H` and one event per match.
The fire-all operator applies every match, including overlapping ones, and is not a
Wolfram model update. -/
def tracedFireAllStep (sys : ExecSystem) (H : ExecHG ℕ) (step : Nat) :
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

/-- `n` iterations of the fire-all step `tracedFireAllStep`. -/
def tracedFireAllEvolve (sys : ExecSystem) (H : ExecHG ℕ) :
    Nat → ExecHG ℕ × List CausalEvent
  | 0 => (H, [])
  | n + 1 =>
    let (state_n, events_n) := tracedFireAllEvolve sys H n
    let (state_n1, events_n1) := tracedFireAllStep sys state_n n
    (state_n1, events_n ++ events_n1)

/-! ## Causal edge derivation

An edge `i → j` is recorded when `i < j` and some edge value in the produced list of
event `i` equals an edge value in the consumed list of event `j`. -/

/-- `true` when some edge of `produced_A` equals some edge of `consumed_B`. -/
def edgesIntersect (produced_A consumed_B : ExecHG ℕ) : Bool :=
  produced_A.any (fun e => consumed_B.any (fun e' => decide (e = e')))

/-- The pairs `(i, j)` of event indices with `i < j` for which `edgesIntersect` holds on the
produced edges of event `i` and the consumed edges of event `j`. -/
def deriveCausalEdges (events : List CausalEvent) : List (Nat × Nat) :=
  let indexed := events.zipIdx
  indexed.foldr (fun (eA, i) acc =>
    acc ++ indexed.foldr (fun (eB, j) acc' =>
      if i < j && edgesIntersect eA.produced eB.consumed then
        acc' ++ [(i, j)]
      else acc') []) []

/-- A list of index pairs as two-vertex hyperedges, dropping loops. -/
def pairsToExecHG (edges : List (Nat × Nat)) : ExecHG ℕ :=
  edges.filterMap (fun (i, j) =>
    if h : (¬ (i = j)) then
      some ⟨[i, j], List.cons_ne_nil _ _⟩
    else none)

/-- The causal edges of an event list as two-vertex hyperedges. -/
def causalDAGOfEvents (events : List CausalEvent) : ExecHG ℕ :=
  pairsToExecHG (deriveCausalEdges events)

/-- Causal edges of `n` traced single-way steps. -/
def causalDAGOfEvolution (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    ExecHG ℕ :=
  let (_, events) := tracedSingleWayEvolve sys H n
  causalDAGOfEvents events

/-- Causal edges of `n` traced fire-all steps (`tracedFireAllEvolve`). -/
def causalDAGOfFireAll (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    ExecHG ℕ :=
  let (_, events) := tracedFireAllEvolve sys H n
  causalDAGOfEvents events

/-! ## Subdivision-rule examples

The examples use `subdivisionSys` on the single edge `{1, 2}` with `singleWayStep`. -/

/-- The causal edges of two steps of `subdivisionSys` on `[consEdge 1 2]`. -/
def subdivisionCausalDAG_depth2 : ExecHG ℕ :=
  causalDAGOfEvolution subdivisionSys [consEdge 1 2] 2

/-- `knillEulerScaled subdivisionCausalDAG_depth2 = 6`. Checked by `native_decide`. -/
theorem subdivision_depth2_causalDAG_knill :
    knillEulerScaled subdivisionCausalDAG_depth2 = 6 := by native_decide

/-- The causal edges of one step of `subdivisionSys` on `[consEdge 1 2]`. -/
def subdivisionCausalDAG_depth1 : ExecHG ℕ :=
  causalDAGOfEvolution subdivisionSys [consEdge 1 2] 1

/-- `knillEulerScaled subdivisionCausalDAG_depth1 = 0`. Checked by `native_decide`. -/
theorem subdivision_depth1_causalDAG_knill :
    knillEulerScaled subdivisionCausalDAG_depth1 = 0 := by native_decide

end CausalEventTrace
end InfraFormalization
