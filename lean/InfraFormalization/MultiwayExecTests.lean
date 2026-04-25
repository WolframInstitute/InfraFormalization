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

end Test
end MultiwayExec
end InfraFormalization
