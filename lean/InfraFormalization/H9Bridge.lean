/-
A reduction of `H9Closure.engineMatchesTriad` to a one-step statement
`BridgeStepLemma`.

The evolution is `fireAllStep`, which applies every match of every rule
found in the state, including matches that share edges. It is not a
Wolfram model update when matches overlap. The systems are
`edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys`, started from
`seedEdge12 = [[1, 2]]`. `distinctEdgeCount H` is the number of distinct
vertex lists among the hyperedges of `H`.

`Psi H` is the conjunction of three predicates on `H.map (·.verts)`:

  1. `NoSelfLoops`: every vertex list `[a, b]` has `a ≠ b`.
  2. `NoSymmetricPairs`: if `[a, b]` occurs, then `[b, a]` does not occur
     (unless the two lists are equal).
  3. `MultLeTwo`: every vertex list occurs at most twice.

`BridgeStepLemma` states: for both systems and every `H` with `Psi H`,
`distinctEdgeCount (fireAllStep sys H) = 3 * distinctEdgeCount H` and
`Psi (fireAllStep sys H)`. No theorem in the library proves it.

The module proves `Psi seedEdge12` and that `BridgeStepLemma` implies
`engineMatchesTriad` and the count `3^d` for every `d`. The depth-0 cases
are checked by `native_decide`.
-/

import InfraFormalization.H9Closure

namespace InfraFormalization
namespace H9Bridge

open MultiwayExec
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DistinctEdgeIdentity
open H9Closure

/-! ## Section A: The predicate `Psi` -/

/-- The vertex list of `e`. -/
def edgeVerts (e : Hyperedge ℕ) : List ℕ := e.verts

/-- The reverse of the vertex list of `e`. -/
def edgeRevVerts (e : Hyperedge ℕ) : List ℕ := e.verts.reverse

/-- Every vertex list of length 2 in `H` has two different entries.
Vertex lists of other lengths are unconstrained. -/
def NoSelfLoops (H : ExecHG ℕ) : Prop :=
  ∀ v ∈ H.map (·.verts),
    match v with
    | [a, b] => a ≠ b
    | _ => True

/-- For every vertex list `[a, b]` in `H`, either `[b, a]` is not in `H`
or `[a, b] = [b, a]`. Vertex lists of other lengths are unconstrained. -/
def NoSymmetricPairs (H : ExecHG ℕ) : Prop :=
  ∀ v ∈ H.map (·.verts),
    match v with
    | [a, b] => [b, a] ∉ H.map (·.verts) ∨ [a, b] = [b, a]
    | _ => True

/-- Multiplicity of a vertex list `v` in `H.map (·.verts)`. -/
def vertsMult (v : List ℕ) (H : ExecHG ℕ) : Nat :=
  (H.map (·.verts)).count v

/-- Every vertex list occurs at most twice in `H.map (·.verts)`. -/
def MultLeTwo (H : ExecHG ℕ) : Prop :=
  ∀ v ∈ H.map (·.verts), vertsMult v H ≤ 2

/-- `Psi H` is the conjunction `NoSelfLoops H ∧ NoSymmetricPairs H ∧
MultLeTwo H`. -/
def Psi (H : ExecHG ℕ) : Prop :=
  NoSelfLoops H ∧ NoSymmetricPairs H ∧ MultLeTwo H

/-! ## Section B: `Psi seedEdge12` -/

/-- `Psi` holds for `seedEdge12 = [[1, 2]]`. -/
theorem psi_seedEdge12 : Psi seedEdge12 := by
  refine ⟨?_, ?_, ?_⟩
  · -- NoSelfLoops
    intro v hv
    simp [seedEdge12, Hyperedge.verts] at hv
    -- `hv : v = [1, 2]`
    rw [hv]
    decide
  · -- NoSymmetricPairs
    intro v hv
    simp [seedEdge12, Hyperedge.verts] at hv
    rw [hv]
    -- Need: [2, 1] ∉ [[1, 2]].map (·.verts) ∨ [1, 2] = [2, 1]
    left
    simp [seedEdge12, Hyperedge.verts]
  · -- MultLeTwo
    intro v hv
    simp [seedEdge12, Hyperedge.verts, vertsMult] at *
    by_cases h : v = [1, 2]
    · rw [h]; simp [seedEdge12, Hyperedge.verts]
    · simp [h] at hv

/-! ## Section C: The statement `BridgeStepLemma` -/

/-- For `sys` equal to `edgeReversal_tripleMerger_Sys` or `fork_doubleCycle_Sys` and every
hypergraph `H` with `Psi H`, the state `fireAllStep sys H` has three times the distinct-edge count
of `H` and satisfies `Psi`. No theorem in the library proves this statement. -/
def BridgeStepLemma : Prop :=
  ∀ (sys : ExecSystem),
    sys = edgeReversal_tripleMerger_Sys ∨ sys = fork_doubleCycle_Sys →
    ∀ (H : ExecHG ℕ),
      Psi H →
      distinctEdgeCount (fireAllStep sys H) = 3 * distinctEdgeCount H ∧
      Psi (fireAllStep sys H)

/-! ## Section D: `BridgeStepLemma` implies `engineMatchesTriad` -/

/-- Under `BridgeStepLemma`, `Psi` holds for
`fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d` for every d.
The proof is induction on d from `psi_seedEdge12`. -/
theorem psi_preserved_eR_tripleMerger (step : BridgeStepLemma) :
    ∀ d : Nat, Psi (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) := by
  intro d
  induction d with
  | zero => exact psi_seedEdge12
  | succ d ih =>
    have := step edgeReversal_tripleMerger_Sys (Or.inl rfl)
      (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) ih
    exact this.2

/-- Under `BridgeStepLemma`, `Psi` holds for `fireAllEvolve fork_doubleCycle_Sys seedEdge12 d`
for every d. -/
theorem psi_preserved_fork_dCyc (step : BridgeStepLemma) :
    ∀ d : Nat, Psi (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d) := by
  intro d
  induction d with
  | zero => exact psi_seedEdge12
  | succ d ih =>
    have := step fork_doubleCycle_Sys (Or.inr rfl)
      (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d) ih
    exact this.2

/-- `BridgeStepLemma` implies `engineMatchesTriad`, by induction on the
depth. The depth-0 case is checked by `native_decide`. -/
theorem bridge_from_step (step : BridgeStepLemma) : engineMatchesTriad := by
  intro d
  refine ⟨?_, ?_⟩
  · -- eR + tripleMerger branch
    induction d with
    | zero =>
      rw [triadList_length]
      native_decide
    | succ d ih =>
      have hPsi := psi_preserved_eR_tripleMerger step d
      have hstep := step edgeReversal_tripleMerger_Sys (Or.inl rfl)
        (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) hPsi
      show distinctEdgeCount (fireAllStep edgeReversal_tripleMerger_Sys
        (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d)) = (triadList (d+1)).length
      rw [hstep.1, triadList_length_succ]
      rw [triadList_length] at ih
      rw [triadList_length]
      omega
  · -- fork + doubleCycle branch
    induction d with
    | zero =>
      rw [triadList_length]
      native_decide
    | succ d ih =>
      have hPsi := psi_preserved_fork_dCyc step d
      have hstep := step fork_doubleCycle_Sys (Or.inr rfl)
        (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d) hPsi
      show distinctEdgeCount (fireAllStep fork_doubleCycle_Sys
        (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d)) = (triadList (d+1)).length
      rw [hstep.1, triadList_length_succ]
      rw [triadList_length] at ih
      rw [triadList_length]
      omega

/-! ## Section E: `BridgeStepLemma` implies the `3^d` count -/

/-- If `BridgeStepLemma` holds, then for every d and both systems the
distinct-edge count of `fireAllEvolve sys seedEdge12 d` is `3^d`. The
proof composes `bridge_from_step` with
`H9Closure.H9_conditional_on_bridge`. -/
theorem H9_closure_from_step (step : BridgeStepLemma) :
    ∀ d : Nat,
      distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) = 3^d ∧
      distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d) = 3^d := by
  exact H9_conditional_on_bridge (bridge_from_step step)


end H9Bridge
end InfraFormalization
