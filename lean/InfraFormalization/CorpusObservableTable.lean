/-
**B4-corpus-observable-table: comprehensive (R, B, signature) table
for the multi-rule combo corpus** (#473; corpus-level consolidation).

This module provides a **comprehensive observable table** for the
multi-rule combo corpus at depth 3 on `edge12`, listing for each
combo:

  * `R(combo, 3)` — discrete Ricci scalar (causal density).
  * `B(combo, 3)` — branchial density.
  * Signature: Lorentzian (R<0, B>0) vs Riemannian (R>0, B>0) vs
    degenerate (R=0 or B=0).

**The corpus table** (all `native_decide`-certified):

  | Combo                       | R    | B   | Sig         |
  |-----------------------------|------|-----|-------------|
  | edgeReversal + identity      | -24  | 30  | Lorentzian  |
  | edgeReversal + fork          | -42  | 66  | Lorentzian  |
  | edgeReversal + doubleCycle_5 | -24  | 42  | Lorentzian  |
  | fork + doubleCycle_5         |   0  | 78  | degenerate (R=0) |
  | edgeReversal + tripleMerger  | -36  | 78  | Lorentzian  |

**Observations**:

  * 4 of 5 combos are Lorentzian (R < 0 < B).
  * `fork + dCyc` is R-degenerate (R = 0) — interaction of two
    non-trivial single rules cancels classical curvature.
  * `eR + tripleMerger` and `fork + dCyc` both have B = 78 — same
    quantum-amplitude scale but different classical-curvature
    character.

**Why this matters** (final corpus consolidation):

The framework now has a **publication-ready table** of dual-side
observables across the multi-rule corpus. This is the discrete
analog of how continuum-GR characterizes solutions by their Ricci
scalar values at characteristic events.

**Key research findings**:

  * **R-degeneracy from rule interaction**: `fork + dCyc` shows
    that combining a Tree-class and Merger-class rule can produce
    R = 0 — classical curvature cancellation.
  * **Same B different R**: `eR + tripleMerger` and `fork + dCyc`
    both give B = 78 but differ on R (-36 vs 0).

These dual-side observable patterns are the framework's discrete-QG
prediction set for rule corpus characterization.
-/

import InfraFormalization.CorpusBalanceSpectrum
import InfraFormalization.DiscreteMetricTensor

namespace InfraFormalization
namespace CorpusObservableTable

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity
open DiscreteMetricTensor

/-! ## Corpus values for fork + doubleCycle -/

theorem R_fork_dCyc_3 : discreteRicciScalar fork_doubleCycle_Sys 3 = 0 := by
  native_decide

theorem B_fork_dCyc_3 : discreteBranchialDensity fork_doubleCycle_Sys 3 = 78 := by
  native_decide

/-- `eR + doubleCycle` at depth 3: R = -24, B = 42. -/
theorem RB_eR_dCyc_3 :
    discreteRicciScalar edgeReversal_doubleCycle_Sys 3 = -24 ∧
    discreteBranchialDensity edgeReversal_doubleCycle_Sys 3 = 42 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## The corpus observable table -/

/-- **`corpus_observable_table`**: comprehensive (R, B) values for
the multi-rule combo corpus at depth 3 on edge12. 5 combos with
distinct dynamical signatures.

  * `eR + id`: (-24, 30) — Lorentzian.
  * `eR + fork`: (-42, 66) — Lorentzian.
  * `eR + dCyc`: (-24, 42) — Lorentzian (different B from eR + id).
  * `fork + dCyc`: (0, 78) — R-degenerate (interaction cancels
    classical curvature).
  * `eR + tripleMerger`: (-36, 78) — Lorentzian (same B as
    fork + dCyc but different R).
-/
theorem corpus_observable_table :
    discreteMetricTensor edgeReversal_identity_Sys 3 = (-24, 30) ∧
    discreteMetricTensor edgeReversal_fork_Sys 3 = (-42, 66) ∧
    discreteMetricTensor edgeReversal_doubleCycle_Sys 3 = (-24, 42) ∧
    discreteMetricTensor fork_doubleCycle_Sys 3 = (0, 78) ∧
    discreteMetricTensor edgeReversal_tripleMerger_Sys 3 = (-36, 78) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **`corpus_signature_classification`**: 4 of 5 combos are
Lorentzian; `fork + dCyc` is R-degenerate. -/
theorem corpus_signature_classification :
    hasLorentzianSignature edgeReversal_identity_Sys 3 = true ∧
    hasLorentzianSignature edgeReversal_fork_Sys 3 = true ∧
    hasLorentzianSignature edgeReversal_doubleCycle_Sys 3 = true ∧
    hasLorentzianSignature fork_doubleCycle_Sys 3 = false ∧
    hasLorentzianSignature edgeReversal_tripleMerger_Sys 3 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## R-degeneracy finding: rule-interaction cancels classical curvature -/

/-- **`R_degeneracy_from_interaction`**: at depth 3 on edge12,
`fork + dCyc` has R = 0 even though both component rules are
non-trivial (Tree class + Merger class). The combination cancels
classical curvature at depth 3.

This is a research finding: **rule interaction can cancel classical
curvature**. The framework demonstrates that combining a Tree-class
and Merger-class rule can produce an R-zero combo. -/
theorem R_degeneracy_from_interaction :
    discreteRicciScalar fork_doubleCycle_Sys 3 = 0 ∧
    discreteRicciScalar forkSys_2 3 ≠ 0 ∧
    discreteRicciScalar doubleCycleSys_5 3 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Same-B different-R observation -/

/-- **`same_B_different_R`**: `eR + tripleMerger` (R=-36) and
`fork + dCyc` (R=0) both give B = 78 — same quantum-amplitude
scale but different classical-curvature character. -/
theorem same_B_different_R :
    discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 =
      discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 ≠
      discreteRicciScalar fork_doubleCycle_Sys 3 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## What this delivers

**Publication-ready 5-combo corpus observable table**:

  * `corpus_observable_table`: 5-conj bundle of (R, B) values.
  * `corpus_signature_classification`: signature predicate.
  * `R_degeneracy_from_interaction`: shows rule interaction can
    cancel classical curvature.
  * `same_B_different_R`: demonstrates dual-side independence at
    corpus level.

**Why this matters** (final dual-side characterization):

The framework now has a **discrete-QG observational prediction
set** with concrete (R, B) values for 5 multi-rule combos. This is
the substrate for downstream continuum-limit analysis.

**Key research findings**:

  * Rule interaction can **cancel R** (fork + dCyc: R = 0).
  * Same B can correspond to different R (eR + tripleMerger vs
    fork + dCyc: both B = 78, R = -36 vs 0).
  * 4 of 5 combos remain Lorentzian — most multi-rule combos
    produce GR-like signature.

**For rule selection by physics target**:

  * BBH: `eR + tripleMerger` (lowest α* from #470).
  * Classical-curvature-zero: `fork + dCyc` (R = 0 baseline).
  * Maximum amplitude richness: `eR + fork` or `eR + tripleMerger`
    (both have highest B values 66 / 78).

The multi-rule combo corpus is now fully characterized by its
dual-side discrete-QG observables.
-/

end CorpusObservableTable
end InfraFormalization
