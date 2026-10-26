/-
Reports of twelve rules on one edge at depth 2.

This module computes `evaluateRule sys edge12 2` for twelve rules and
checks by `native_decide` the edge counts of the three states and that the
scaled Knill values of the states are equal for each rule. The edge counts
are `[1, 1, 1]` for six rules (`trivialIdentity`, `triangleClosure`,
`wheeler`, the rule of G3 `jgorardSys`, `quintIdentity`, `quintReversal`),
`[1, 2, 4]` for four rules and `[1, 3, 9]` for two rules.
-/

import InfraFormalization.RulePhysicsReport

namespace InfraFormalization
namespace RuleReportComparison

open MultiwayExec
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open LiteratureRules
open RuleExtraction
open KnillDiscreteGaussBonnet
open RulePreservationClassification
open RulePhysicsReport

/-! ## Reports at depth 2 -/

def report_trivialIdentity : PhysicsReport :=
  evaluateRule trivialIdentitySys RulePreservationClassification.edge12 2
def report_subdivision : PhysicsReport :=
  evaluateRule subdivisionSysLocal RulePreservationClassification.edge12 2
def report_triangulation : PhysicsReport :=
  evaluateRule triangulationSys RulePreservationClassification.edge12 2
def report_triangleClosure : PhysicsReport :=
  evaluateRule triangleClosureSys RulePreservationClassification.edge12 2
def report_wheeler : PhysicsReport :=
  evaluateRule wheelerSys RulePreservationClassification.edge12 2
def report_jgorard : PhysicsReport :=
  evaluateRule jgorardSys RulePreservationClassification.edge12 2
def report_tripleExtend : PhysicsReport :=
  evaluateRule tripleExtendSys RulePreservationClassification.edge12 2
def report_quintIdentity : PhysicsReport :=
  evaluateRule quintIdentitySys RulePreservationClassification.edge12 2
def report_quintFreshSink : PhysicsReport :=
  evaluateRule quintFreshSinkSys RulePreservationClassification.edge12 2
def report_quintReversal : PhysicsReport :=
  evaluateRule quintReversalSys RulePreservationClassification.edge12 2
def report_quintBidirect : PhysicsReport :=
  evaluateRule quintBidirectSys RulePreservationClassification.edge12 2
def report_quintFreshSource : PhysicsReport :=
  evaluateRule quintFreshSourceSys RulePreservationClassification.edge12 2

/-! ## Table -/

/-- A record with one `PhysicsReport` per rule. -/
structure CatalogReportTable where
  trivialIdentity : PhysicsReport
  subdivision     : PhysicsReport
  triangulation   : PhysicsReport
  triangleClosure : PhysicsReport
  wheeler         : PhysicsReport
  jgorard         : PhysicsReport
  tripleExtend    : PhysicsReport
  quintIdentity   : PhysicsReport
  quintFreshSink  : PhysicsReport
  quintReversal   : PhysicsReport
  quintBidirect   : PhysicsReport
  quintFreshSource: PhysicsReport

/-- The table for the `edge12` seed at depth 2. -/
def catalogReportTable : CatalogReportTable :=
  { trivialIdentity := report_trivialIdentity
    subdivision     := report_subdivision
    triangulation   := report_triangulation
    triangleClosure := report_triangleClosure
    wheeler         := report_wheeler
    jgorard         := report_jgorard
    tripleExtend    := report_tripleExtend
    quintIdentity   := report_quintIdentity
    quintFreshSink  := report_quintFreshSink
    quintReversal   := report_quintReversal
    quintBidirect   := report_quintBidirect
    quintFreshSource:= report_quintFreshSource }

/-! ## Edge counts, checked by `native_decide` -/

theorem trivialIdentity_edges :
    report_trivialIdentity.spatialEdges = [1, 1, 1] := by native_decide
theorem subdivision_edges :
    report_subdivision.spatialEdges = [1, 2, 4] := by native_decide
theorem triangulation_edges :
    report_triangulation.spatialEdges = [1, 3, 9] := by native_decide
theorem triangleClosure_edges :
    report_triangleClosure.spatialEdges = [1, 1, 1] := by native_decide
theorem wheeler_edges :
    report_wheeler.spatialEdges = [1, 1, 1] := by native_decide
theorem jgorard_edges :
    report_jgorard.spatialEdges = [1, 1, 1] := by native_decide
theorem tripleExtend_edges :
    report_tripleExtend.spatialEdges = [1, 3, 9] := by native_decide
theorem quintIdentity_edges :
    report_quintIdentity.spatialEdges = [1, 1, 1] := by native_decide
theorem quintFreshSink_edges :
    report_quintFreshSink.spatialEdges = [1, 2, 4] := by native_decide
theorem quintReversal_edges :
    report_quintReversal.spatialEdges = [1, 1, 1] := by native_decide
theorem quintBidirect_edges :
    report_quintBidirect.spatialEdges = [1, 2, 4] := by native_decide
theorem quintFreshSource_edges :
    report_quintFreshSource.spatialEdges = [1, 2, 4] := by native_decide

/-! ## Equal scaled Knill values along each run, checked by `native_decide` -/

theorem trivialIdentity_preserves : report_trivialIdentity.topologyPreserved = true := by native_decide
theorem subdivision_preserves : report_subdivision.topologyPreserved = true := by native_decide
theorem triangulation_preserves : report_triangulation.topologyPreserved = true := by native_decide
theorem triangleClosure_preserves : report_triangleClosure.topologyPreserved = true := by native_decide
theorem wheeler_preserves : report_wheeler.topologyPreserved = true := by native_decide
theorem jgorard_preserves : report_jgorard.topologyPreserved = true := by native_decide
theorem tripleExtend_preserves : report_tripleExtend.topologyPreserved = true := by native_decide
theorem quintIdentity_preserves : report_quintIdentity.topologyPreserved = true := by native_decide
theorem quintFreshSink_preserves : report_quintFreshSink.topologyPreserved = true := by native_decide
theorem quintReversal_preserves : report_quintReversal.topologyPreserved = true := by native_decide
theorem quintBidirect_preserves : report_quintBidirect.topologyPreserved = true := by native_decide
theorem quintFreshSource_preserves : report_quintFreshSource.topologyPreserved = true := by native_decide

/-! ## Conjunctions -/

/-- For each of the twelve rules on `edge12` at depth 2, the scaled Knill
values of the three states are equal. -/
theorem catalog_knill_constant_two_steps :
    report_trivialIdentity.topologyPreserved = true ∧
    report_subdivision.topologyPreserved = true ∧
    report_triangulation.topologyPreserved = true ∧
    report_triangleClosure.topologyPreserved = true ∧
    report_wheeler.topologyPreserved = true ∧
    report_jgorard.topologyPreserved = true ∧
    report_tripleExtend.topologyPreserved = true ∧
    report_quintIdentity.topologyPreserved = true ∧
    report_quintFreshSink.topologyPreserved = true ∧
    report_quintReversal.topologyPreserved = true ∧
    report_quintBidirect.topologyPreserved = true ∧
    report_quintFreshSource.topologyPreserved = true :=
  ⟨trivialIdentity_preserves, subdivision_preserves,
   triangulation_preserves, triangleClosure_preserves,
   wheeler_preserves, jgorard_preserves,
   tripleExtend_preserves, quintIdentity_preserves,
   quintFreshSink_preserves, quintReversal_preserves,
   quintBidirect_preserves, quintFreshSource_preserves⟩

/-- The edge counts of the twelve rules on `edge12` at depth 2: `[1,1,1]`
for six rules, `[1,2,4]` for four and `[1,3,9]` for two. -/
theorem catalog_rule_diversity_3_classes :
    -- [1, 1, 1] (6 rules)
    report_trivialIdentity.spatialEdges = [1, 1, 1] ∧
    report_triangleClosure.spatialEdges = [1, 1, 1] ∧
    report_wheeler.spatialEdges = [1, 1, 1] ∧
    report_jgorard.spatialEdges = [1, 1, 1] ∧
    report_quintIdentity.spatialEdges = [1, 1, 1] ∧
    report_quintReversal.spatialEdges = [1, 1, 1] ∧
    -- [1, 2, 4] (4 rules)
    report_subdivision.spatialEdges = [1, 2, 4] ∧
    report_quintFreshSink.spatialEdges = [1, 2, 4] ∧
    report_quintBidirect.spatialEdges = [1, 2, 4] ∧
    report_quintFreshSource.spatialEdges = [1, 2, 4] ∧
    -- [1, 3, 9] (2 rules)
    report_triangulation.spatialEdges = [1, 3, 9] ∧
    report_tripleExtend.spatialEdges = [1, 3, 9] :=
  ⟨trivialIdentity_edges, triangleClosure_edges, wheeler_edges,
   jgorard_edges, quintIdentity_edges, quintReversal_edges,
   subdivision_edges, quintFreshSink_edges,
   quintBidirect_edges, quintFreshSource_edges,
   triangulation_edges, tripleExtend_edges⟩

/-! ## Distinct edge counts -/

/-- The edge-count lists of the identity, subdivision and triangulation
rules are pairwise distinct. -/
theorem catalog_classes_are_distinct :
    report_trivialIdentity.spatialEdges ≠ report_subdivision.spatialEdges ∧
    report_subdivision.spatialEdges ≠ report_triangulation.spatialEdges ∧
    report_trivialIdentity.spatialEdges ≠ report_triangulation.spatialEdges := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trivialIdentity_edges, subdivision_edges]; decide
  · rw [subdivision_edges, triangulation_edges]; decide
  · rw [trivialIdentity_edges, triangulation_edges]; decide

end RuleReportComparison
end InfraFormalization
