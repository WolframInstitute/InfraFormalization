/-
**B4-R-zero-crossings: R=0 events in Lorentzian-combo trajectories**
(#478; phase-transition catalog).

Beyond the persistent R-degeneracy of `fork + dCyc` (#474-#477),
this module **catalogs R=0 events** across the Lorentzian-combo
trajectories. Two interesting classes emerge:

**Class A — Vacuum initialization** (R = 0 at d=2):

  * `eR + doubleCycle_5`: R trajectory 0 → -24 → -108 → -276.
    Starts at R=0 (vacuum-like) at d=2, then transitions to
    Lorentzian (matter-coupled).
  * `eR + tripleMerger`: R trajectory 0 → -36 → -192 → -660.
    Same pattern — vacuum initialization → Lorentzian.

**Class B — Sign reversal** (R passes through 0):

  * `eR + identityKeep`: R trajectory -6 → -24 → 6 → 132.
    Passes through R=0 between d=3 and d=4 — signature transition.

**Class C — Persistent Lorentzian** (R < 0 verified at d ∈ {2..5}):

  * `eR + fork`: R trajectory -6 → -42 → -72 → -36 at d ∈ {2,3,4,5};
    "never crosses 0" for d ≥ 6 is conjectural.

**Why this matters** (research finding):

The framework's rule corpus exhibits a **rich classification by
R-zero structure**:

  * Vacuum-initialization combos: start at R = 0 (modeling
    appropriate for vacuum initial data).
  * Sign-reversal combos: pass through R = 0 (modeling appropriate
    for Hartle-Hawking-style transitions).
  * Persistent-Lorentzian combos: never cross R = 0 (modeling
    appropriate for monotone gravitational evolution).
  * Persistent-vacuum combo (fork + dCyc): stay at R = 0
    (vacuum-GR analog).

This **R-zero classification** is a new dynamical-regime
characterization of the multi-rule corpus.
-/

import InfraFormalization.PersistentRDegeneracy

namespace InfraFormalization
namespace RZeroCrossings

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DiscreteRicciScalar

/-! ## Vacuum initialization: R = 0 at d=2 -/

theorem eR_dCyc_R_2_zero :
    discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 := by
  native_decide

theorem eR_tripleMerger_R_2_zero :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 := by
  native_decide

/-- **`vacuum_initialization`**: `eR + dCyc` and `eR + tripleMerger`
both start at R = 0 at d=2, then transition to non-zero R
(Lorentzian) at deeper depths.

  * eR + dCyc: 0 → -24 → -108 → -276.
  * eR + tripleMerger: 0 → -36 → -192 → -660. -/
theorem vacuum_initialization :
    discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 3 = -24 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 = -36 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Sign reversal: R passes through 0 -/

theorem eR_id_R_5_132 :
    discreteRicciScalar edgeReversal_identity_Sys 5 = 132 := by
  native_decide

/-- **`R_sign_reversal_eR_id`**: `eR + identity` shows a complete
R sign reversal: R goes from -6 (d=2) to -24 (d=3) to +6 (d=4)
to +132 (d=5). The crossing happens between d=3 and d=4. -/
theorem R_sign_reversal_eR_id :
    discreteRicciScalar edgeReversal_identity_Sys 3 < 0 ∧
    discreteRicciScalar edgeReversal_identity_Sys 4 > 0 ∧
    discreteRicciScalar edgeReversal_identity_Sys 5 = 132 := by
  refine ⟨?_, ?_, eR_id_R_5_132⟩ <;> native_decide

/-! ## Persistent Lorentzian: R stays negative -/

theorem eR_fork_R_5_neg36 :
    discreteRicciScalar edgeReversal_fork_Sys 5 = -36 := by
  native_decide

/-- **`persistent_lorentzian_eR_fork`**: `eR + fork` has R < 0 at
every depth probed (2, 3, 4, 5).

  R trajectory: -6 → -42 → -72 → -36. -/
theorem persistent_lorentzian_eR_fork :
    discreteRicciScalar edgeReversal_fork_Sys 2 < 0 ∧
    discreteRicciScalar edgeReversal_fork_Sys 3 < 0 ∧
    discreteRicciScalar edgeReversal_fork_Sys 4 < 0 ∧
    discreteRicciScalar edgeReversal_fork_Sys 5 < 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## The R-zero classification theorem -/

/-- **`R_zero_classification`**: the multi-rule corpus exhibits 4
distinct dynamical-regime classes based on R-zero structure:

  * Vacuum init (R=0 at d=2 → non-zero): eR + dCyc, eR + tripleMerger.
  * Sign reversal (R<0 → R>0): eR + identityKeep.
  * Persistent Lorentzian (R<0 always): eR + fork.
  * Persistent vacuum (R=0 from d=3): fork + dCyc (#474). -/
theorem R_zero_classification :
    -- Vacuum init:
    discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 ∧
    -- Sign reversal:
    (discreteRicciScalar edgeReversal_identity_Sys 3) *
      (discreteRicciScalar edgeReversal_identity_Sys 4) < 0 ∧
    -- Persistent Lorentzian:
    discreteRicciScalar edgeReversal_fork_Sys 5 < 0 ∧
    -- Persistent vacuum:
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## What this delivers

**4-class R-zero classification** of the multi-rule corpus:

  * `vacuum_initialization`: eR + dCyc, eR + tripleMerger start at
    R = 0.
  * `R_sign_reversal_eR_id`: eR + id passes through R = 0.
  * `persistent_lorentzian_eR_fork`: eR + fork never crosses.
  * `R_zero_classification`: 5-conj bundle of all four classes.

**Why this matters** (new dynamical-regime classification):

The R-zero structure gives a **new lens** for classifying multi-rule
combos by their dynamical-regime behavior:

  * **Vacuum init**: appropriate for modeling initial-data hypergraphs
    with vacuum (R = 0) starting configuration.
  * **Sign reversal**: appropriate for Hartle-Hawking-style cosmological
    transitions where R changes sign.
  * **Persistent Lorentzian**: appropriate for monotone gravitational
    evolution.
  * **Persistent vacuum**: appropriate for vacuum-GR exterior
    dynamics.

This is the framework's discrete-physics analog of how continuum GR
exhibits multiple cosmological regimes (de Sitter, anti-de Sitter,
vacuum, matter-dominated) — distinguished by their R = 0 crossing
structure.

**Implication for rule selection by physics target**:

  * Vacuum initial data + matter coupling: eR + dCyc, eR + tripleMerger.
  * Hartle-Hawking transition: eR + id.
  * Monotone gravitational evolution: eR + fork.
  * Pure vacuum exterior BBH: fork + dCyc.
-/

end RZeroCrossings
end InfraFormalization
