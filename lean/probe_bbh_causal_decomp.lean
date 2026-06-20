/-
Probe: edge-causal-disjoint-tree hypothesis for BBH.

Hypothesis: for single-edge-LHS rules, the causal DAG of
singleWayEvolve sys seed d decomposes into a disjoint union of
"edge-causal trees" — one tree per distinct seed edge — even when
the seed shares vertices across distinct edges. Reason: each event
consumes ONE edge of the current state and fresh-vertex allocation
gives every event's produced edges DISJOINT fresh vertices. Causal
connection is via edge-production/consumption, NOT via seed-vertex
sharing.
-/

import InfraFormalization.BBHInitialData

open InfraFormalization
open InfraFormalization.MultiwayExec
open InfraFormalization.RuleSignatureExecMetrics
open InfraFormalization.KnillDiscreteGaussBonnet
open InfraFormalization.CausalEventTrace
open InfraFormalization.DiscoveredRules
open InfraFormalization.BBHInitialData

/-! ## Helpers (top-level, not inside `do`) -/

def edgeStr (e : Hyperedge ℕ) : String := toString e.verts

def edgesStr (es : ExecHG ℕ) : String :=
  "[" ++ String.intercalate ", " (es.map edgeStr) ++ "]"

def eventStr (ev : CausalEvent) : String :=
  s!"step={ev.step} m={ev.matchIdx} consumed={edgesStr ev.consumed} produced={edgesStr ev.produced}"

def edgeMember (e : Hyperedge ℕ) (es : List (Hyperedge ℕ)) : Bool :=
  es.any (fun e' => decide (e = e'))

/-- The seed-edge index a step-0 event consumed (Some k iff event
consumed exactly the k-th seed edge of `bbhInitial`). -/
def seedEdgeAncestorOfStep0 (ev : CausalEvent) : Option Nat :=
  bbhInitial.zipIdx.foldr (fun (e, k) acc =>
    match acc with
    | some _ => acc
    | none =>
      if edgeMember e ev.consumed then some k else none) none

/-- Predecessor list given a causal-edge list `edges`. -/
def predOf (edges : List (Nat × Nat)) (i : Nat) : List Nat :=
  edges.filterMap (fun (j, k) => if k = i then some j else none)

/-- Reachable step-0 ancestor set via bounded BFS (bound = fuel). -/
partial def ancestorRoots
    (edges : List (Nat × Nat)) (i : Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | f + 1 =>
    let ps := predOf edges i
    if ps.isEmpty then [i]
    else
      let raw := ps.flatMap (fun p => ancestorRoots edges p f)
      raw.foldr (fun r acc => if r ∈ acc then acc else r :: acc) []

/-! ## Probe -/

def probe : IO Unit := do
  IO.println "=========================================================="
  IO.println "BBH causal-DAG decomposition probe — doubleCycleSys_5, d=2"
  IO.println "=========================================================="
  IO.println s!"Seed bbhInitial: {bbhInitial.length} edges"
  IO.println s!"  {edgesStr bbhInitial}"

  let s0 := bbhInitial
  IO.println s!"\nState at d=0: {s0.length} edges, nextFresh={nextFresh s0}"
  let s1 := singleWayStep doubleCycleSys_5 s0
  IO.println s!"State at d=1: {s1.length} edges, nextFresh={nextFresh s1}"
  let s2 := singleWayStep doubleCycleSys_5 s1
  IO.println s!"State at d=2: {s2.length} edges, nextFresh={nextFresh s2}"

  let (_, events) := tracedSingleWayEvolve doubleCycleSys_5 bbhInitial 2
  IO.println s!"\nTotal events over d=2: {events.length}"
  IO.println "Events:"
  for (e, i) in events.zipIdx do
    IO.println s!"  [{i}] {eventStr e}"

  let causalEdges := deriveCausalEdges events
  IO.println s!"\nCausal edges ({causalEdges.length}):"
  for (a, b) in causalEdges do
    IO.println s!"  {a} -> {b}"

  let step0Events := events.zipIdx.filter (fun p => p.1.step == 0)
  IO.println s!"\nStep-0 events: {step0Events.length}"
  for (ev, i) in step0Events do
    let anc := seedEdgeAncestorOfStep0 ev
    IO.println s!"  [{i}] consumed={edgesStr ev.consumed} seedEdgeIdx={anc}"

  let n := events.length
  let step0Idx : List Nat := step0Events.map (·.2)
  IO.println s!"\nStep-0 event indices: {step0Idx}"

  -- Per-event ancestor classification.
  IO.println "\nEvent → root step-0 ancestor(s):"
  let mut classification : List (Nat × List Nat) := []
  for i in List.range n do
    let roots := ancestorRoots causalEdges i (n + 1)
    classification := classification ++ [(i, roots)]
    let seedIdxs := roots.filterMap (fun r =>
      (events[r]?).bind seedEdgeAncestorOfStep0)
    IO.println s!"  event[{i}]: roots={roots} seedEdgeIdxs={seedIdxs}"

  -- Per-root partition.
  IO.println "\nPer-step-0-root partition (event indices):"
  for r in step0Idx do
    let inPartition : List Nat :=
      classification.filterMap (fun (i, rs) => if r ∈ rs then some i else none)
    let seedIdx := match events[r]? with
      | some ev => seedEdgeAncestorOfStep0 ev
      | none => none
    IO.println s!"  root {r} (seedEdge={seedIdx}): events {inPartition}"

  -- Cross-partition causal-edge check: any (a, b) where a and b have
  -- DIFFERENT step-0-root sets is a violation of the hypothesis.
  IO.println "\nCross-partition causal edges (should be empty for hypothesis):"
  let mut crossCount := 0
  for (a, b) in causalEdges do
    let ra := classification.lookup a |>.getD []
    let rb := classification.lookup b |>.getD []
    let raSet := ra.foldr (fun r acc => if r ∈ acc then acc else r :: acc) []
    let rbSet := rb.foldr (fun r acc => if r ∈ acc then acc else r :: acc) []
    if raSet ≠ rbSet then
      crossCount := crossCount + 1
      IO.println s!"  CROSS: {a}({raSet}) -> {b}({rbSet})"
  IO.println s!"Cross-partition causal-edge count: {crossCount}"

  -- Per-partition disjointness of CONSUMED and PRODUCED edges across partitions.
  IO.println "\nPer-partition consumed/produced edge disjointness check:"
  let partitions : List (Nat × List Nat) :=
    step0Idx.map (fun r =>
      (r, classification.filterMap (fun (i, rs) => if r ∈ rs then some i else none)))
  -- Aggregate consumed+produced edges per partition.
  let partEdges : List (Nat × List (Hyperedge ℕ)) :=
    partitions.map (fun (r, idxs) =>
      let allEs := idxs.flatMap (fun i =>
        match events[i]? with
        | none => []
        | some ev => ev.consumed ++ ev.produced)
      (r, allEs))
  for i in List.range partEdges.length do
    for j in List.range partEdges.length do
      if i < j then
        match partEdges[i]?, partEdges[j]? with
        | some (ri, eis), some (rj, ejs) =>
          let overlap := eis.filter (fun e => edgeMember e ejs)
          if overlap.length > 0 then
            IO.println s!"  OVERLAP between root {ri} and root {rj}: {edgesStr overlap}"
          else
            IO.println s!"  disjoint: root {ri} vs root {rj}"
        | _, _ => pure ()

  -- Sanity: Knill at d=2.
  let dag2 := causalDAGOfEvolution doubleCycleSys_5 bbhInitial 2
  IO.println s!"\nKnill(BBH, doubleCycle_5, 2) = {knillEulerScaled dag2}"
  let edgeDag2 := causalDAGOfEvolution doubleCycleSys_5 seedEdge12 2
  IO.println s!"Knill(edge12, doubleCycle_5, 2) = {knillEulerScaled edgeDag2}"
  IO.println s!"7 · Knill(edge12, doubleCycle_5, 2) = {7 * knillEulerScaled edgeDag2}"

  -- d=4 sanity (matches headline finding).
  let dag4 := causalDAGOfEvolution doubleCycleSys_5 bbhInitial 4
  IO.println s!"\nKnill(BBH, doubleCycle_5, 4) = {knillEulerScaled dag4}"

#eval probe
