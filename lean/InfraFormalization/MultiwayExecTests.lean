/-
**Cross-check tests for `MultiwayExec`** vs the reference outputs in
`../efficient_rewriting_final/tmp/TestCases.wl`.

Each test instantiates a rule + seed used in
`HypergraphRewritingEngine`'s `getMWGStats` reference data, runs the
Lean executable engine for the same number of steps, and checks the
event-count and (un-canonicalised) state-count match.

The Lean engine does **not** canonicalise states modulo
hypergraph isomorphism. So the **event count** matches the reference
exactly; the **state count** matches up to (initial + few steps),
diverging at the depth where Wolfram's engine first collapses two
distinct-but-isomorphic states.

Reference (`getMWGStats` from `TestCases.wl`):

  TestCase1: rule `{{1,2}} → {{1,2}, {2,3}}`, init `{{1,2}}`.
    step 1: NumStates=2, NumEvents=1
    step 2: NumStates=4, NumEvents=3
    step 3: NumStates=8 (canonical), NumEvents=9
-/

import InfraFormalization.MultiwayExec

namespace InfraFormalization
namespace MultiwayExec
namespace Test

open InfraFormalization.Hypergraph

/-! ## TestCase1 from `TestCases.wl`

Rule: `{{1, 2}} → {{1, 2}, {2, 3}}` (vertex 3 fresh).
Seed: `{{1, 2}}`.
-/

private def lhsEdge1 : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def rhsKeep1 : Hyperedge (Fin 3) := ⟨[0, 1], by decide⟩
private def rhsNew1  : Hyperedge (Fin 3) := ⟨[1, 2], by decide⟩

/-- TestCase1's rule: one bound LHS edge, one fresh-vertex RHS edge. -/
def tc1Rule : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [lhsEdge1]
  rhs := [rhsKeep1, rhsNew1]

def tc1Sys : ExecSystem := ⟨[tc1Rule]⟩

def tc1Seed : ExecHG ℕ := [⟨[1, 2], by decide⟩]

/-- Step 1 reaches exactly 1 state. Reference event count for step 1 is
1; with our (un-canonicalised) state semantics, 1 next-state from the
single seed = 1 event = exact match. -/
example :
    (multiwayEvolve tc1Sys tc1Seed 1).length = 1 := by decide

/-- Step 2 reaches exactly 2 states. Reference cumulative state count
at step 2 is 4 (initial 1 + step-1 1 + step-2 2 = 4). Cumulative
event count at step 2 is 3 (1 + 2). Both match. -/
example :
    (multiwayEvolve tc1Sys tc1Seed 2).length = 2 := by decide

/-- Step 3 reaches exactly 6 states (un-canonicalised). Reference
cumulative event count = 9 (1 + 2 + 6). Reference canonicalised state
count = 8; un-canonical count is 10 (1+1+2+6) — diverges by 2 (the
exact number of isomorphic pairs Wolfram's engine collapses). -/
example :
    (multiwayEvolve tc1Sys tc1Seed 3).length = 6 := by decide

/-- Cumulative event count to step 3 = 1 + 2 + 6 = 9 — matches the
reference exactly. -/
example :
    (multiwayStep tc1Sys tc1Seed).length
      + ((multiwayEvolve tc1Sys tc1Seed 1).flatMap (multiwayStep tc1Sys)).length
      + ((multiwayEvolve tc1Sys tc1Seed 2).flatMap (multiwayStep tc1Sys)).length
      = 9 := by decide

/-! ## TestCase2 from `TestCases.wl`

Rule: `{{1, 2}, {2, 3}} → {{1, 2}, {2, 3}, {2, 4}}` (vertex 4 fresh).
Seed: `{{1, 2}, {2, 3}}`.
Reference step 1: NumStates=2 (cumulative: init + 1), NumEvents=1.
-/

private def tc2_lhs0 : Hyperedge (Fin 3) := ⟨[0, 1], by decide⟩
private def tc2_lhs1 : Hyperedge (Fin 3) := ⟨[1, 2], by decide⟩
private def tc2_rhs0 : Hyperedge (Fin 4) := ⟨[0, 1], by decide⟩
private def tc2_rhs1 : Hyperedge (Fin 4) := ⟨[1, 2], by decide⟩
private def tc2_rhs2 : Hyperedge (Fin 4) := ⟨[1, 3], by decide⟩

def tc2Rule : ExecRule where
  numBound := 3
  numFresh := 1
  lhs := [tc2_lhs0, tc2_lhs1]
  rhs := [tc2_rhs0, tc2_rhs1, tc2_rhs2]

def tc2Sys : ExecSystem := ⟨[tc2Rule]⟩

def tc2Seed : ExecHG ℕ := [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩]

/-- TC2 step 1: exactly 1 event (1 next state). Matches reference
NumEvents=1. -/
example :
    (multiwayEvolve tc2Sys tc2Seed 1).length = 1 := by decide

/-! ## TestCase3 from `TestCases.wl`

Rule: `{{1, 2}, {2, 3}} → {{1, 2}, {2, 3}, {3, 1}, {2, 4}}`.
Seed: `{{1, 2}, {2, 3}}`.
Reference step 1: NumStates=2, NumEvents=1.
-/

private def tc3_rhs2 : Hyperedge (Fin 4) := ⟨[2, 0], by decide⟩
private def tc3_rhs3 : Hyperedge (Fin 4) := ⟨[1, 3], by decide⟩

def tc3Rule : ExecRule where
  numBound := 3
  numFresh := 1
  lhs := [tc2_lhs0, tc2_lhs1]
  rhs := [tc2_rhs0, tc2_rhs1, tc3_rhs2, tc3_rhs3]

def tc3Sys : ExecSystem := ⟨[tc3Rule]⟩

example :
    (multiwayEvolve tc3Sys tc2Seed 1).length = 1 := by decide

/-! ## TestCase6 from `TestCases.wl`

Rule: `{{1, 2}} → {{1, 2}, {2, 3}}` (vertex 3 fresh).
Seed: `{{1, 2}, {2, 1}}` (2-cycle: distinct edges, swapped indices).
Reference step 1: NumStates=2, NumEvents=2 (two distinct bindings:
(a=1, b=2) and (a=2, b=1)).
-/

def tc6Sys : ExecSystem := ⟨[tc1Rule]⟩  -- same rule as TC1

def tc6Seed : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 1], by decide⟩]

example :
    (multiwayEvolve tc6Sys tc6Seed 1).length = 2 := by decide

end Test
end MultiwayExec
end InfraFormalization
