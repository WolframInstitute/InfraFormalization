/-
Predecessors and step-0 ancestors in a causal edge list.

This module defines `predOf` and `stepZeroAncestorSet` for a list of causal
pairs, the predicate `SingleEdgeSystem` (one rule with a one-edge left-hand
side) and `distinctEdgeBaselineCount` (the number of distinct vertex lists
among the edges of a seed). It contains no theorems.
-/

import InfraFormalization.PerEdgeAdditivityFramework

namespace InfraFormalization
namespace EdgeCausallyDisjointBridge

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open PerEdgeAdditivityFramework
open TwoTriangleSeed
open DiscoveredRules

/-! ## Section A: predecessor and ancestor analysis on the causal DAG -/

/-- Direct predecessors of event index `i` in a causal-edge list. -/
def predOf (edges : List (Nat × Nat)) (i : Nat) : List Nat :=
  edges.filterMap (fun (j, k) => if k = i then some j else none)

/-- The step-0 events reached from event `i` by a backward breadth-first walk
along `edges`, for at most `fuel` rounds. -/
partial def stepZeroAncestorSet
    (events : Array CausalEvent) (edges : List (Nat × Nat))
    (i : Nat) (fuel : Nat) : List Nat :=
  let rec walk (frontier : List Nat) (visited : List Nat) (fuel : Nat) : List Nat :=
    match fuel with
    | 0 => visited
    | Nat.succ k =>
      match frontier with
      | [] => visited
      | _ =>
        let stepZero := frontier.filter (fun j =>
          if h : j < events.size then (events[j]).step = 0 else false)
        let next := frontier.flatMap (fun j => predOf edges j) |>.dedup
        let visited' := (stepZero ++ visited).dedup
        walk next visited' k
  walk [i] [] fuel

/-! ## Section B: helpers -/

/-- The system consists of exactly one rule, and that rule has a one-edge
left-hand side. -/
def SingleEdgeSystem (sys : ExecSystem) : Prop :=
  ∃ r, sys.rules = [r] ∧ SingleEdgeLHS r

/-- The number of distinct `verts` lists among the edges of `seed`, as an
integer. -/
def distinctEdgeBaselineCount (seed : ExecHG ℕ) : ℤ :=
  ((seed.map (·.verts)).foldr
    (fun v acc => if v ∈ acc then acc else v :: acc) []).length

end EdgeCausallyDisjointBridge
end InfraFormalization
