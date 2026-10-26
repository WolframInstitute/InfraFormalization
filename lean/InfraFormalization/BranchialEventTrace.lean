/-
Same-step consumed-edge contention between the events of a traced
single-way evolution.

`eventsAreBranchial A B` holds when events `A` and `B` belong to the same
step and their consumed edge lists share an edge value. The fired matches
of one `singleWayStep` are edge-disjoint as edge instances, so the
relation holds only when two fired matches consume distinct instances of
equal edge values. This relation is not the branchial graph of the
Wolfram model, which relates states of the multiway system.
-/

import InfraFormalization.CausalEventTrace

namespace InfraFormalization
namespace BranchialEventTrace

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace

/-! ## Same-step contention pairs from an event list -/

/-- Two events have the same step and share at least one consumed edge
value. -/
def eventsAreBranchial (eA eB : CausalEvent) : Bool :=
  decide (eA.step = eB.step) && edgesIntersect eA.consumed eB.consumed

/-- The list of index pairs `(i, j)` with `i < j` such that events `i` and
`j` satisfy `eventsAreBranchial`. -/
def deriveBranchialEdges (events : List CausalEvent) : List (Nat × Nat) :=
  let indexed := events.zipIdx
  indexed.foldr (fun (eA, i) acc =>
    acc ++ indexed.foldr (fun (eB, j) acc' =>
      if i < j && eventsAreBranchial eA eB then
        acc' ++ [(i, j)]
      else acc') []) []

/-- Same-step contention edges of `n` traced single-way steps. -/
def branchialDAGOfEvolution (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    ExecHG ℕ :=
  let (_, events) := tracedSingleWayEvolve sys H n
  pairsToExecHG (deriveBranchialEdges events)

/-- Same-step contention edges of `n` traced fire-all steps. The fire-all
operator applies every match, including overlapping ones, and is not a
Wolfram model update. -/
def branchialDAGOfFireAll (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    ExecHG ℕ :=
  let (_, events) := tracedFireAllEvolve sys H n
  pairsToExecHG (deriveBranchialEdges events)

/-! ## Example -/

/-- For the subdivision rule from one edge, the scaled Knill value of the
same-step contention graph of three single-way steps is 0. Checked by
`native_decide`. -/
theorem subdivision_branchial_knill :
    knillEulerScaled (branchialDAGOfEvolution
      MultiwayExec.subdivisionSys [consEdge 1 2] 3) = 0 := by
  native_decide

end BranchialEventTrace
end InfraFormalization
