/-
Comparison of `MultiwayExec` with reference outputs of `HypergraphRewritingEngine`.

The reference values are `getMWGStats` outputs in `../efficient_rewriting_final/tmp/TestCases.wl`.
Each example runs `multiwayEvolve` for a rule and seed from that file and checks the number of
states or events by `decide`. `multiwayEvolve` does not identify isomorphic states, so state counts
agree with the reference only up to the first step at which the reference identifies two isomorphic
states. For TestCase1 (`{{1,2}} → {{1,2}, {2,3}}`, initial state `{{1,2}}`), the reference gives
2, 4 and 8 cumulative states and 1, 3 and 9 cumulative events at steps 1, 2 and 3. The module also
checks edge and vertex counts of four single-way steps of the edge-subdivision rule.
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

/-- Step 1 has 1 state, from 1 event, as in the reference. -/
example :
    (multiwayEvolve tc1Sys tc1Seed 1).length = 1 := by decide

/-- Step 2 has 2 states. The cumulative state count `1 + 1 + 2 = 4` and event count `1 + 2 = 3`
agree with the reference. -/
example :
    (multiwayEvolve tc1Sys tc1Seed 2).length = 2 := by decide

/-- Step 3 has 6 states. The cumulative state count is `1 + 1 + 2 + 6 = 10`, against 8 in the
reference,
which identifies isomorphic states. -/
example :
    (multiwayEvolve tc1Sys tc1Seed 3).length = 6 := by decide

/-- The cumulative event count up to step 3 is `1 + 2 + 6 = 9`, as in the reference. -/
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

/-- TestCase2, step 1: 1 state, from 1 event, as in the reference. -/
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

/-! ## Single-way evolution of the edge-subdivision rule

The rule `{{a, b}} → {{a, c}, {c, b}}` with `c` fresh inserts a midpoint into an edge. From the
single edge `{1, 2}`, the examples check that the state after `n ≤ 4` single-way steps has `2^n`
edges and `2^n + 1` vertices. -/

private def subdLhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def subdRhsL : Hyperedge (Fin 3) := ⟨[0, 2], by decide⟩
private def subdRhsR : Hyperedge (Fin 3) := ⟨[2, 1], by decide⟩

/-- The edge-subdivision rule: `{a,b} → {a,c}, {c,b}` with `c` fresh. -/
def subdivisionRule : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [subdLhs]
  rhs := [subdRhsL, subdRhsR]

def subdivisionSys : ExecSystem := ⟨[subdivisionRule]⟩

/-- Seed: a single edge `{1, 2}`. -/
def subdSeed : ExecHG ℕ := [⟨[1, 2], by decide⟩]

/-- After 0 single-way steps, 1 edge and 2 vertices. -/
example : hgEdgeCount   (singleWayEvolve subdivisionSys subdSeed 0) = 1 := by decide
example : hgVertexCount (singleWayEvolve subdivisionSys subdSeed 0) = 2 := by decide

/-- After 1 single-way step, 2 edges and 3 vertices (path `1—3—2`). -/
example : hgEdgeCount   (singleWayEvolve subdivisionSys subdSeed 1) = 2 := by decide
example : hgVertexCount (singleWayEvolve subdivisionSys subdSeed 1) = 3 := by decide

/-- After 2 single-way steps, 4 edges and 5 vertices. -/
example : hgEdgeCount   (singleWayEvolve subdivisionSys subdSeed 2) = 4 := by decide
example : hgVertexCount (singleWayEvolve subdivisionSys subdSeed 2) = 5 := by decide

/-- After 3 single-way steps, 8 edges and 9 vertices. -/
example : hgEdgeCount   (singleWayEvolve subdivisionSys subdSeed 3) = 8 := by decide
example : hgVertexCount (singleWayEvolve subdivisionSys subdSeed 3) = 9 := by decide

/-- After 4 single-way steps, 16 edges and 17 vertices. -/
example : hgEdgeCount   (singleWayEvolve subdivisionSys subdSeed 4) = 16 := by decide
example : hgVertexCount (singleWayEvolve subdivisionSys subdSeed 4) = 17 := by decide

end Test
end MultiwayExec
end InfraFormalization
