/-
A ternary-tree model `triadList` with `3^d` elements at depth d, and the
statement `engineMatchesTriad` that relates it to the distinct-edge count
of the fire-all evolution.

The evolution is `fireAllEvolve`. `fireAllStep` applies every match of
every rule found in the state, including matches that share edges. It is
not a Wolfram model update when matches overlap. `distinctEdgeCount H`
is the number of distinct vertex lists among the hyperedges of `H`.

The systems are `edgeReversal + tripleMerger`
(`edgeReversal_tripleMerger_Sys`) and `forkRule_2 + doubleCycle_5`
(`fork_doubleCycle_Sys`), both started from `seedEdge12 = [[1, 2]]`.

PROVED without `native_decide`:

  * `TriadEdge d` (inductive type) and `triadList d` (an explicit list).
  * `triadList_length d : (triadList d).length = 3^d`, by induction on
    `d`.
  * `H9_conditional_on_bridge`: if `engineMatchesTriad` holds, then
    `distinctEdgeCount (fireAllEvolve sys seedEdge12 d) = 3^d` for every
    d and both systems.

PROVED-WITH-NATIVE-DECIDE: `bridge_at_0` to `bridge_at_7`, the two
equalities of `engineMatchesTriad` at depths 0 to 7.

OPEN: `engineMatchesTriad` itself, for all d.
-/

import InfraFormalization.H9StructuralProgress

namespace InfraFormalization
namespace H9Closure

open MultiwayExec
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DistinctEdgeIdentity
open H9StructuralProgress

/-! ## Section A: The triadic combinatorial model -/

/-- `TriadEdge d` is an inductive type with one element `base` at depth 0
and three constructors `reverseOf`, `freshA`, `freshB` from depth d to
depth d+1. The type has no definitional link to the engine. The
correspondence between distinct edges of the engine and `TriadEdge d` is
the OPEN statement `engineMatchesTriad`, which compares counts only. -/
inductive TriadEdge : Nat → Type
  | base : TriadEdge 0
  | reverseOf {d : Nat} (parent : TriadEdge d) : TriadEdge (d+1)
  | freshA {d : Nat} (parent : TriadEdge d) : TriadEdge (d+1)
  | freshB {d : Nat} (parent : TriadEdge d) : TriadEdge (d+1)
deriving DecidableEq

/-! ## Section B: Explicit enumeration as a list -/

/-- `triadList d` is a list of elements of `TriadEdge d`: `triadList 0` is
`[base]`, and `triadList (d+1)` replaces each element `p` of
`triadList d` by `reverseOf p`, `freshA p`, `freshB p`. -/
def triadList : (d : Nat) → List (TriadEdge d)
  | 0 => [TriadEdge.base]
  | d+1 => (triadList d).flatMap (fun p =>
      [TriadEdge.reverseOf p, TriadEdge.freshA p, TriadEdge.freshB p])

/-! ## The cardinality theorem (proved via List.length induction) -/

/-- `triadList 0` has length 1. -/
theorem triadList_length_zero : (triadList 0).length = 1 := by
  simp [triadList]

/-- `(triadList (d+1)).length = 3 * (triadList d).length`, from
`List.length_flatMap` with inner length 3. -/
theorem triadList_length_succ (d : Nat) :
    (triadList (d+1)).length = 3 * (triadList d).length := by
  simp [triadList, List.length_flatMap]
  ring

/-- `(triadList d).length = 3^d`, by induction on `d` using
`triadList_length_succ`. -/
theorem triadList_length (d : Nat) : (triadList d).length = 3^d := by
  induction d with
  | zero => simp [triadList]
  | succ d ih => rw [triadList_length_succ, ih, pow_succ]; ring

/-! ## Section D: Length of `triadList` -/

/-- `∀ d, (triadList d).length = 3^d`. This is `triadList_length`. The
statement concerns the list `triadList` only and does not mention the
engine. -/
theorem H9_combinatorial_closed : ∀ d : Nat, (triadList d).length = 3^d :=
  triadList_length

/-! ## Section E: The statement `engineMatchesTriad` (OPEN) -/

/-- `engineMatchesTriad` (OPEN): for every d, the distinct-edge counts
of `fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d` and of
`fireAllEvolve fork_doubleCycle_Sys seedEdge12 d` both equal
`(triadList d).length`. This module does not prove it. -/
def engineMatchesTriad : Prop :=
  ∀ d : Nat,
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) =
      (triadList d).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d) =
      (triadList d).length

/-! ## Section F: Consequence of `engineMatchesTriad` -/

/-- `engineMatchesTriad` implies, for every d and for both systems, that
the distinct-edge count of the fire-all evolution of `seedEdge12` after
`d` steps is `3^d`. The proof rewrites with `triadList_length`. -/
theorem H9_conditional_on_bridge (h : engineMatchesTriad) :
    ∀ d : Nat,
      distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) = 3^d ∧
      distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d) = 3^d := by
  intro d
  obtain ⟨h1, h2⟩ := h d
  rw [h1, h2, triadList_length]
  exact ⟨rfl, rfl⟩

/-! ## Section G: `engineMatchesTriad` at depths 0 to 7

Each theorem below states the two equalities of `engineMatchesTriad` at
one depth. The proofs rewrite with `triadList_length` and evaluate the
engine by `native_decide`. -/

/-- The two equalities of `engineMatchesTriad` at depth 0. -/
theorem bridge_at_0 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 0) =
      (triadList 0).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 0) =
      (triadList 0).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-- The two equalities of `engineMatchesTriad` at depth 1. -/
theorem bridge_at_1 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 1) =
      (triadList 1).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 1) =
      (triadList 1).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-- The two equalities of `engineMatchesTriad` at depth 2. -/
theorem bridge_at_2 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 2) =
      (triadList 2).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 2) =
      (triadList 2).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-- The two equalities of `engineMatchesTriad` at depth 3. -/
theorem bridge_at_3 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 3) =
      (triadList 3).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 3) =
      (triadList 3).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-- The two equalities of `engineMatchesTriad` at depth 4. -/
theorem bridge_at_4 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 4) =
      (triadList 4).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 4) =
      (triadList 4).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-- The two equalities of `engineMatchesTriad` at depth 5. -/
theorem bridge_at_5 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 5) =
      (triadList 5).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 5) =
      (triadList 5).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-- The two equalities of `engineMatchesTriad` at depth 6. -/
theorem bridge_at_6 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 6) =
      (triadList 6).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 6) =
      (triadList 6).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-- The two equalities of `engineMatchesTriad` at depth 7. -/
theorem bridge_at_7 :
    distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 7) =
      (triadList 7).length ∧
    distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 7) =
      (triadList 7).length := by
  refine ⟨?_, ?_⟩ <;> (rw [triadList_length]; native_decide)

/-! ## Contents

PROVED without `native_decide`:

  * `triadList_length : ∀ d, (triadList d).length = 3^d`, and its copy
    `H9_combinatorial_closed`.
  * `H9_conditional_on_bridge`: `engineMatchesTriad` implies
    `distinctEdgeCount (fireAllEvolve sys seedEdge12 d) = 3^d` for all d,
    for both systems.

PROVED-WITH-NATIVE-DECIDE:

  * `bridge_at_0` to `bridge_at_7`: the two equalities of
    `engineMatchesTriad` at depths 0 to 7.

OPEN: `engineMatchesTriad`, the statement that for every d,
`distinctEdgeCount (fireAllEvolve edgeReversal_tripleMerger_Sys seedEdge12 d)`
and `distinctEdgeCount (fireAllEvolve fork_doubleCycle_Sys seedEdge12 d)`
both equal `(triadList d).length`.

`H9Bridge` reduces `engineMatchesTriad` to the OPEN statement
`H9Bridge.BridgeStepLemma`.
-/

end H9Closure
end InfraFormalization
