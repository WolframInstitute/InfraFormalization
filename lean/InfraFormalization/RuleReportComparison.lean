/-
**B4-table: comprehensive multi-rule report comparison table** (#436).

Builds a concrete comparison artifact across the codebase's full
12-rule catalog: each named rule (`trivialIdentity`, `subdivision`,
`triangulation`, `triangleClosure`, `wheeler`, `jgorardNamed`,
`tripleExtend`, and the 5 quint-stable rules) gets its own
`PhysicsReport` computed at depth 2 on the canonical `edge12` seed.

The result is a **comparison table** showing each rule's per-step
edge-count trajectory + topology preservation indicator + causal-DAG
Knill. The table immediately classifies rules by their dynamical
behavior:

| Rule                | edges (depth 2)  | Class               |
|---------------------|------------------|---------------------|
| trivialIdentity     | `[1, 1, 1]`      | identity (no-op)    |
| subdivision         | `[1, 2, 4]`      | doubling            |
| triangulation       | `[1, 3, 9]`      | tripling            |
| triangleClosure     | `[1, 1, 1]`      | identity (no match) |
| wheeler             | `[1, 1, 1]`      | identity (no match) |
| jgorardNamed        | `[1, 1, 1]`      | identity (no match) |
| tripleExtend        | `[1, 3, 9]`      | tripling            |
| quintRuleIdentity   | `[1, 1, 1]`      | identity            |
| quintRuleFreshSink  | `[1, 2, 4]`      | doubling            |
| quintRuleReversal   | `[1, 1, 1]`      | identity            |
| quintRuleBidirect   | `[1, 2, 4]`      | doubling            |
| quintRuleFreshSource| `[1, 2, 4]`      | doubling            |

**3 classes**: 6 identity-like (no edge growth), 4 doubling, 2 tripling.
All preserve topology (Knill = 6 throughout).

**Bundled artifacts**:

  * `catalogReportTable`: a 12-field record, one report per rule.
  * `catalog_topology_universally_preserved`: every rule's report
    has `topologyPreserved = true`.
  * `catalog_rule_diversity_3_classes`: 3 distinct edge-trajectory
    shapes occur across the catalog (rule diversity is non-trivial).
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

/-! ## The 12-rule catalog reports at depth 2 -/

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

/-! ## Catalog report table -/

/-- A 12-field record bundling the per-rule `PhysicsReport`s for the
entire named-rule catalog. -/
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

/-- The catalog report table for the `edge12` seed at depth 2. -/
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

/-! ## Per-rule edge-trajectory certifications -/

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

/-! ## Per-rule topology preservation -/

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

/-! ## Universal topology preservation bundle -/

/-- **`catalog_topology_universally_preserved`**: every rule in the
12-rule catalog produces a `PhysicsReport` with `topologyPreserved =
true` on `edge12` at depth 2. -/
theorem catalog_topology_universally_preserved :
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

/-! ## Rule diversity: 3 distinct edge-trajectory classes -/

/-- **`catalog_rule_diversity_3_classes`**: the 12-rule catalog
produces exactly 3 distinct edge-trajectory shapes at depth 2 on
`edge12`: `[1,1,1]` (identity), `[1,2,4]` (doubling), `[1,3,9]`
(tripling). Rule diversity is non-trivial — the rule library spans
multiple dynamical behaviors, not just one. -/
theorem catalog_rule_diversity_3_classes :
    -- Identity class (6 rules)
    report_trivialIdentity.spatialEdges = [1, 1, 1] ∧
    report_triangleClosure.spatialEdges = [1, 1, 1] ∧
    report_wheeler.spatialEdges = [1, 1, 1] ∧
    report_jgorard.spatialEdges = [1, 1, 1] ∧
    report_quintIdentity.spatialEdges = [1, 1, 1] ∧
    report_quintReversal.spatialEdges = [1, 1, 1] ∧
    -- Doubling class (4 rules)
    report_subdivision.spatialEdges = [1, 2, 4] ∧
    report_quintFreshSink.spatialEdges = [1, 2, 4] ∧
    report_quintBidirect.spatialEdges = [1, 2, 4] ∧
    report_quintFreshSource.spatialEdges = [1, 2, 4] ∧
    -- Tripling class (2 rules)
    report_triangulation.spatialEdges = [1, 3, 9] ∧
    report_tripleExtend.spatialEdges = [1, 3, 9] :=
  ⟨trivialIdentity_edges, triangleClosure_edges, wheeler_edges,
   jgorard_edges, quintIdentity_edges, quintReversal_edges,
   subdivision_edges, quintFreshSink_edges,
   quintBidirect_edges, quintFreshSource_edges,
   triangulation_edges, tripleExtend_edges⟩

/-! ## Cross-class distinctness -/

/-- **`catalog_classes_are_distinct`**: the three dynamical classes
give visibly distinct edge-trajectory tails — identity stays at 1,
doubling reaches 4 at depth 2, tripling reaches 9. -/
theorem catalog_classes_are_distinct :
    report_trivialIdentity.spatialEdges ≠ report_subdivision.spatialEdges ∧
    report_subdivision.spatialEdges ≠ report_triangulation.spatialEdges ∧
    report_trivialIdentity.spatialEdges ≠ report_triangulation.spatialEdges := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trivialIdentity_edges, subdivision_edges]; decide
  · rw [subdivision_edges, triangulation_edges]; decide
  · rw [trivialIdentity_edges, triangulation_edges]; decide

/-! ## What this delivers

**First multi-rule comparison-table artifact**:

  * `CatalogReportTable` (12 fields): one `PhysicsReport` per named
    rule in the catalog.
  * Per-rule edge-trajectory certifications (12 theorems).
  * Per-rule topology-preservation certifications (12 theorems).
  * Bundled `catalog_topology_universally_preserved` (12-way conj).
  * Bundled `catalog_rule_diversity_3_classes` (12-way conj):
    explicit classification into identity / doubling / tripling.
  * `catalog_classes_are_distinct`: pairwise `≠` proofs.

**Sample classification table**:

| Class       | Rule count | Edge trajectory   |
|-------------|------------|-------------------|
| Identity    | 6          | `[1, 1, 1]`       |
| Doubling    | 4          | `[1, 2, 4]`       |
| Tripling    | 2          | `[1, 3, 9]`       |

Total: 12 rules across 3 dynamical classes, all topology-preserving.

**Why this matters**: this is the first cross-catalog comparison
**artifact** (not just a bunch of separate theorems): a single
`CatalogReportTable` value with 12 rule reports, certified field by
field, demonstrating the codebase produces *structured comparative
data* about rules. Combined with the per-rule report (#435), this is
the foundation for higher-level rule analysis — sorting rules by
asymptotic growth rate, classifying by causal-DAG topology shape,
identifying rules that might produce BBH-type causal structures.
-/

end RuleReportComparison
end InfraFormalization
