/-
**B4-bbh-initial: BBH initial-data hypergraph + additivity-confirmed
certification** (#443; partial closure of H6).

This module defines a **binary-black-hole initial-data hypergraph**:
two triangular "clusters" connected by a single bridge edge, capturing
the qualitative structure of a binary BH initial configuration before
coalescence.

**The structure**: 6 vertices, 7 edges.

  * Cluster A: triangle on `{0, 1, 2}` — three edges
  * Cluster B: triangle on `{3, 4, 5}` — three edges
  * Bridge:  one edge `{2, 3}` connecting the clusters

This is the discrete analog of two compact gravitating bodies with
weak inter-body coupling — exactly the kind of initial data a
Numerical Relativity code would set up for a binary BH coalescence
simulation.

**Headline finding**: applying the discovered merger rules to this
BBH seed at depth 4 produces causal-DAG Knill values exactly
matching the per-seed-edge additivity prediction:

  * `Knill(BBH, edgeReversal, 4)   = 7 × 0  = 0`  ✓
  * `Knill(BBH, doubleCycle_5, 4)  = 7 × -6 = -42` ✓

The structural-rule invariants extend cleanly from simple single-edge
seeds to physics-motivated initial data. Confirmed at d=4 for the 2
sampled rules on seven-edge BBH seeds; not a general theorem.

**Why this matters**: a discrete BBH model needs to predict event
counts and topology of the causal evolution from physically-motivated
initial data. This module shows that the framework's structural
invariants extrapolate consistently from toy single-edge seeds to
7-edge BBH-style configurations.

**Partial closure of H6** (BBH initial data as hypergraph): the seed
is defined, the rule-class invariants are certified to apply.
Outstanding for H7-H9: rule evolution at higher depths showing
the bridge "merging" the clusters topologically; discrete-Ψ₄
extraction from the causal trajectory; numerical-relativity waveform
matching.
-/

import InfraFormalization.DiscoveredRules

namespace InfraFormalization
namespace BBHInitialData

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules

/-! ## The BBH initial-data hypergraph

Two triangles bridged by one edge. -/

/-- **`bbhInitial`**: binary-BH initial-data hypergraph. Two
triangular "clusters" (`{0,1,2}` and `{3,4,5}`) connected by a
single bridge edge (`{2,3}`). 6 vertices, 7 edges. -/
def bbhInitial : ExecHG ℕ :=
  [-- Cluster A: triangle on {0, 1, 2}
   ⟨[0,1], List.cons_ne_nil _ _⟩,
   ⟨[1,2], List.cons_ne_nil _ _⟩,
   ⟨[0,2], List.cons_ne_nil _ _⟩,
   -- Cluster B: triangle on {3, 4, 5}
   ⟨[3,4], List.cons_ne_nil _ _⟩,
   ⟨[4,5], List.cons_ne_nil _ _⟩,
   ⟨[3,5], List.cons_ne_nil _ _⟩,
   -- Bridge: edge {2, 3}
   ⟨[2,3], List.cons_ne_nil _ _⟩]

/-- BBH initial data has 7 edges. -/
theorem bbhInitial_edge_count : bbhInitial.length = 7 := by decide

/-! ## Discovered-rule application at depth 4

Each merger-class rule applied to the BBH seed produces causal-DAG
Knill values exactly matching the per-seed-edge additivity prediction
proved in #438:

  Knill(rule, seed-with-N-edges, 4) = N · Knill(rule, edge12, 4)
-/

/-- Edge-reversal on BBH at depth 4: Knill = `7 × 0 = 0` ✓ -/
theorem edgeReversal_bbh_knill_zero :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys bbhInitial 4) = 0 := by
  native_decide

/-- Double-cycle on BBH at depth 4: Knill = `7 × (-6) = -42` ✓ -/
theorem doubleCycle_5_bbh_knill_neg42 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 bbhInitial 4) = -42 := by
  native_decide

/-! ## Additivity-law confirmation on BBH

The per-seed-edge invariants from `StableDiscoveredRules` (#438)
extend to the 7-edge BBH seed. -/

/-- **`bbh_additivity_law_holds`**: the structural per-seed-edge
additivity holds on the BBH initial-data:

  `Knill(BBH, rule, 4) = 7 · Knill(edge12, rule, 4)`

for both edge-reversal and double-cycle rules. -/
theorem bbh_additivity_law_holds :
    knillEulerScaled (causalDAGOfEvolution edgeReversalSys bbhInitial 4) =
      7 * knillEulerScaled (causalDAGOfEvolution edgeReversalSys seedEdge12 4) ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 bbhInitial 4) =
      7 * knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) := by
  refine ⟨?_, ?_⟩
  · rw [edgeReversal_bbh_knill_zero, edgeReversal_knill_zero]; rfl
  · rw [doubleCycle_5_bbh_knill_neg42, doubleCycle_5_knill_neg6]; rfl

/-! ## What this delivers

**First BBH-initial-data instance** in the codebase:

  * `bbhInitial` — 6-vertex, 7-edge two-triangles-plus-bridge
    hypergraph capturing binary BH initial-config structure.
  * `bbhInitial_edge_count`: certified edge count.
  * Per-rule Knill certifications on BBH at depth 4.
  * `bbh_additivity_law_holds` — proves the per-seed-edge
    invariants from #438 extend to the 7-edge BBH seed.

**Why this matters**: the framework's structural-rule invariants
extrapolate consistently from toy single-edge seeds to physics-
motivated BBH-style initial configurations. This is the first step
toward H6 / H7 / H8 / H9 — the BBH-from-hypergraph endgame.

**Outstanding**:

  * H7: rule evolution at deeper depths showing the bridge edge
    causing the clusters to topologically merge.
  * H8: discrete-Ψ₄ extraction from the causal trajectory.
  * H9: numerical-relativity waveform matching against LIGO data.

The framework is now poised to attack each of these — the
infrastructure is in place, the invariants are stable, the search
machinery discovers rules, and the BBH seed is defined as a
first-class Lean object.
-/

end BBHInitialData
end InfraFormalization
