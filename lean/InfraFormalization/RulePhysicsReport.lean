/-
A record of computed values for a rule run.

This module defines `PhysicsReport`, a record of lists and integers, and
`evaluateRule sys seed n`, which fills it from the states
`singleWayEvolve sys seed k` for `k ≤ n` and from
`causalDAGOfEvolution sys seed n`: edge and vertex counts, scaled Knill
values, Forman and Higuchi values, the size and scaled Knill value of the
causal graph, the scaled Knill values divided by 6, `1 − causalKnill / 6`,
and whether the scaled Knill values of the states are all equal. Field
values for the subdivision rule on one edge at depth 3, and for three rules
on one edge at depth 1, are checked by `native_decide`.
-/

import InfraFormalization.CausalEventTrace
import InfraFormalization.RulePreservationClassification

namespace InfraFormalization
namespace RulePhysicsReport

open MultiwayExec
open RuleSignatureExecMetrics
open HiguchiScreener
open KnillDiscreteGaussBonnet
open CausalEventTrace

/-! ## The record -/

/-- Computed values of a rule run. -/
structure PhysicsReport where
  -- Per-state lists
  spatialEdges       : List Nat
  spatialVertices    : List Nat
  spatialKnill       : List Int
  spatialForman      : List Int
  spatialHiguchi     : List Int
  -- Causal graph of the run
  causalDAGEdges     : Nat
  causalDAGVertices  : Nat
  causalKnill        : Int
  -- Values derived from the above
  spatialChi         : List Int   -- spatialKnill / 6, integer division
  causalChi          : Int        -- causalKnill / 6, integer division
  mergerEventCount   : Int        -- 1 − causalKnill / 6
  topologyPreserved  : Bool       -- all entries of spatialKnill are equal

/-! ## Evaluation -/

/-- All entries of the list equal its first entry. -/
def allEqual (xs : List Int) : Bool :=
  match xs with
  | [] => true
  | x :: rest => rest.all (· == x)

/-- The report of the run of `sys` from `seed` for `n` steps of
`singleWayStep`. -/
def evaluateRule (sys : ExecSystem) (seed : ExecHG ℕ) (n : Nat) :
    PhysicsReport :=
  let states := (List.range (n + 1)).map (singleWayEvolve sys seed)
  let spatialKnill := states.map knillEulerScaled
  let causalDAG := causalDAGOfEvolution sys seed n
  let causalK := knillEulerScaled causalDAG
  { spatialEdges      := states.map (·.length)
    spatialVertices   := states.map (fun s => (vertexList s).length)
    spatialKnill      := spatialKnill
    spatialForman     := states.map execFormanScalar
    spatialHiguchi    := states.map higuchiTotalDoubled
    causalDAGEdges    := causalDAG.length
    causalDAGVertices := (vertexList causalDAG).length
    causalKnill       := causalK
    spatialChi        := spatialKnill.map (· / 6)
    causalChi         := causalK / 6
    mergerEventCount  := 1 - causalK / 6
    topologyPreserved := allEqual spatialKnill }

/-! ## Subdivision rule on one edge at depth 3 -/

/-- The report of `subdivisionSys` on `[consEdge 1 2]` at depth 3. -/
def subdivisionReport_depth3 : PhysicsReport :=
  evaluateRule subdivisionSys [consEdge 1 2] 3

/-! ### Field values, checked by `native_decide` -/

theorem subdivision_report_spatialEdges :
    subdivisionReport_depth3.spatialEdges = [1, 2, 4, 8] := by native_decide

theorem subdivision_report_spatialVertices :
    subdivisionReport_depth3.spatialVertices = [2, 3, 5, 9] := by native_decide

theorem subdivision_report_spatialKnill :
    subdivisionReport_depth3.spatialKnill = [6, 6, 6, 6] := by native_decide

theorem subdivision_report_spatialForman :
    subdivisionReport_depth3.spatialForman = [4, 4, 4, 4] := by native_decide

theorem subdivision_report_spatialHiguchi :
    subdivisionReport_depth3.spatialHiguchi = [2, 2, 2, 2] := by native_decide

theorem subdivision_report_causalKnill :
    subdivisionReport_depth3.causalKnill = 6 := by native_decide

theorem subdivision_report_spatialChi :
    subdivisionReport_depth3.spatialChi = [1, 1, 1, 1] := by native_decide

theorem subdivision_report_causalChi :
    subdivisionReport_depth3.causalChi = 1 := by native_decide

theorem subdivision_report_mergerEventCount :
    subdivisionReport_depth3.mergerEventCount = 0 := by native_decide

theorem subdivision_report_topologyPreserved :
    subdivisionReport_depth3.topologyPreserved = true := by native_decide

/-! ### Conjunction -/

/-- The conjunction of the ten field values above. -/
theorem subdivision_report_complete :
    subdivisionReport_depth3.spatialEdges = [1, 2, 4, 8] ∧
    subdivisionReport_depth3.spatialVertices = [2, 3, 5, 9] ∧
    subdivisionReport_depth3.spatialKnill = [6, 6, 6, 6] ∧
    subdivisionReport_depth3.spatialForman = [4, 4, 4, 4] ∧
    subdivisionReport_depth3.spatialHiguchi = [2, 2, 2, 2] ∧
    subdivisionReport_depth3.causalKnill = 6 ∧
    subdivisionReport_depth3.spatialChi = [1, 1, 1, 1] ∧
    subdivisionReport_depth3.causalChi = 1 ∧
    subdivisionReport_depth3.mergerEventCount = 0 ∧
    subdivisionReport_depth3.topologyPreserved = true :=
  ⟨subdivision_report_spatialEdges,
   subdivision_report_spatialVertices,
   subdivision_report_spatialKnill,
   subdivision_report_spatialForman,
   subdivision_report_spatialHiguchi,
   subdivision_report_causalKnill,
   subdivision_report_spatialChi,
   subdivision_report_causalChi,
   subdivision_report_mergerEventCount,
   subdivision_report_topologyPreserved⟩

/-! ## Three rules on one edge at depth 1 -/

open RulePreservationClassification

def trivialIdentityReport : PhysicsReport :=
  evaluateRule trivialIdentitySys RulePreservationClassification.edge12 1
def subdivisionReport1 : PhysicsReport :=
  evaluateRule subdivisionSysLocal RulePreservationClassification.edge12 1
def triangulationReport : PhysicsReport :=
  evaluateRule triangulationSys RulePreservationClassification.edge12 1

theorem trivialIdentity_report_topology_preserved :
    trivialIdentityReport.topologyPreserved = true := by native_decide
theorem subdivision_report1_topology_preserved :
    subdivisionReport1.topologyPreserved = true := by native_decide
theorem triangulation_report_topology_preserved :
    triangulationReport.topologyPreserved = true := by native_decide

/-- For the identity, subdivision and triangulation rules on `edge12` at
depth 1, the scaled Knill values of the two states are equal. -/
theorem three_rules_knill_constant_one_step :
    trivialIdentityReport.topologyPreserved = true ∧
    subdivisionReport1.topologyPreserved = true ∧
    triangulationReport.topologyPreserved = true :=
  ⟨trivialIdentity_report_topology_preserved,
   subdivision_report1_topology_preserved,
   triangulation_report_topology_preserved⟩

end RulePhysicsReport
end InfraFormalization
