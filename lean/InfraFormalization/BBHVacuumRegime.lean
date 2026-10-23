/-
**B4-bbh-vacuum-regime: BBH satisfies the vacuum-like discrete
regime** (#476; BBH-applied vacuum substrate).

The vacuum-like regime (#474, #475) is characterized by R = 0 with
non-trivial B. This module **applies the regime to the BBH seed**,
showing that fork + doubleCycle_5 on BBH gives:

  * `R_BBH(fork + dCyc, d) = 0` at all probed depths (3, 4).
  * `B_BBH(fork + dCyc, d) = 7 · B_edge(d)` (universal additivity).

**Headline result** (all `native_decide`-certified):

For `fork + doubleCycle_5` on BBH:

  | d | R_BBH | B_BBH | predicted B = 7·B_edge |
  |---|-------|-------|--------------------------|
  | 3 |   0   |  546  |       7·78 = 546 ✓        |
  | 4 |   0   | 1680  |     7·240 = 1680 ✓        |

**Why this matters** (BBH-applied vacuum substrate):

This module gives the framework's **first explicit BBH-applied
vacuum-like regime characterization**. With this:

  * The BBH seed admits a vacuum-like discrete dynamics (R = 0).
  * The quantum-amplitude content (B) scales as 7 × single-edge.
  * Both structural laws (R-persistence, universal additivity)
    hold simultaneously on BBH.

**Physical interpretation**:

For modeling **exterior BBH dynamics** (vacuum-GR + QFT outside the
horizons), the framework now has a certified discrete-substrate:

  * Classical-curvature: R = 0 (vacuum).
  * Quantum-amplitude: B = 7 · B_edge (per-edge linear scaling).

This is the discrete-physics analog of how vacuum-GR has trivial
stress-energy but non-trivial gravitational radiation amplitudes
in the exterior region.

**Implication for BBH endgame**:

  * H6 (BBH initial data): bbhInitial gives the spatial structure.
  * H7 (BBH evolution): fork + dCyc gives a vacuum-like evolution.
  * H8 (discrete Ψ₄): enhanced Ψ₄ with R = 0 baseline + B-amplitude
    gives the discrete waveform substrate.
  * H9 (continuum convergence): if R = 0 persists under refinement
    and B scales appropriately, the framework predicts continuum
    vacuum-GR exterior dynamics.
-/

import InfraFormalization.VacuumLikeUniversal
import InfraFormalization.BBHInitialData

namespace InfraFormalization
namespace BBHVacuumRegime

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open BBHInitialData
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## BBH vacuum-regime values -/

theorem bbh_vacuum_R_3 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) = 0 := by
  native_decide

theorem bbh_vacuum_R_4 :
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) = 0 := by
  native_decide

theorem bbh_vacuum_B_3 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) = 546 := by
  native_decide

theorem bbh_vacuum_B_4 :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) = 1680 := by
  native_decide

/-! ## BBH vacuum-like regime certification -/

/-- **`bbh_vacuum_regime_certified`**: the BBH seed admits the
vacuum-like discrete regime under `fork + doubleCycle_5`:

  * R_BBH = 0 at depths 3 and 4.
  * B_BBH = 7 × B_edge at every probed depth. -/
theorem bbh_vacuum_regime_certified :
    -- R = 0 on BBH:
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) = 0 ∧
    -- B follows 7× per-edge additivity:
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) =
      7 * discreteBranchialDensity fork_doubleCycle_Sys 3 ∧
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) =
      7 * discreteBranchialDensity fork_doubleCycle_Sys 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **`bbh_vacuum_B_growth`**: under the vacuum-like regime on BBH,
the branchial Knill (quantum amplitude analog) grows substantially
between depths: 546 → 1680 (≈3× per depth step), while R stays
at 0. -/
theorem bbh_vacuum_B_growth :
    knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) >
      knillEulerScaled (branchialDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) ∧
    knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 3) =
      knillEulerScaled (causalDAGOfFireAll fork_doubleCycle_Sys bbhInitial 4) := by
  refine ⟨?_, ?_⟩
  · rw [bbh_vacuum_B_4, bbh_vacuum_B_3]; decide
  · rw [bbh_vacuum_R_3, bbh_vacuum_R_4]

/-! ## What this delivers

**First BBH-applied vacuum-like regime certification**:

  * `bbh_vacuum_regime_certified`: 4-conj bundle.
  * `bbh_vacuum_B_growth`: B grows while R stays at 0.

**Why this matters**:

The framework now has a certified discrete-substrate for exterior
BBH dynamics:

  * Classical gravity is vacuum-like (R = 0).
  * Quantum amplitude (B) grows with depth.
  * Per-edge additivity holds at the BBH scale.

This is the discrete-physics analog of vacuum-GR + QFT description
of exterior BBH dynamics — appropriate for modeling the
gravitational-wave-emission region outside the BH horizons.

**Comparison with Lorentzian BBH (#468)**:

  * Lorentzian regime (eR + id on BBH): R = -168, B = 210.
  * Vacuum-like regime (fork + dCyc on BBH): R = 0, B = 546.

The vacuum-like regime has stronger quantum-amplitude content (B
larger by 2.6×) and zero classical curvature — a qualitatively
distinct BBH-modeling regime.

**For H9 / continuum endgame**: if the vacuum-like regime persists
under refinement, the framework predicts the continuum-limit BBH
exterior has R = 0 vacuum with finite quantum-amplitude density.
This is consistent with the standard QFT-on-curved-spacetime
description of BBH gravitational-wave emission.
-/

end BBHVacuumRegime
end InfraFormalization
