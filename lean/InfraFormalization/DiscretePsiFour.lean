/-
**B4-psi4: discrete Ψ₄ analog from Knill delta + Bondi flux** (#448;
H8 toward closure).

In numerical relativity, Ψ₄ is a complex-valued Newman-Penrose
scalar measuring outgoing gravitational radiation. Its modulus
integrated over a sphere = instantaneous luminosity.

For the discrete framework, we assemble its causal-DAG analog:

  * **Real part** = per-step Knill delta (topology rate of change)
  * **Imag part** = per-step event count (Bondi flux, #447)

Together these form a **discrete complex luminosity signal**
`discretePsiFour : List (Int × Nat)` carrying both observables
at every step of the evolution.

**Why this works** (the formal analog):

  In NR: Ψ₄ ∈ ℂ. Re(Ψ₄) is the "plus" polarization rate;
  Im(Ψ₄) is the "cross" polarization rate. Together their
  square-modulus integrates to gravitational-wave energy.

  In discrete: Re(Ψ₄_n) = ΔKnill_n (topology change rate),
  Im(Ψ₄_n) = flux_n (event count). Together they carry the
  full per-step causal-DAG signature.

**Certified-data results** for the highest-merger combo
`edgeReversal + tripleMerger` on `edge12` (causal-DAG empty at
depths 0-2; non-trivial from depth 3 onward):

  | step k | flux_k | knill_{k+1} | ΔKnill_k |
  |--------|--------|-------------|----------|
  |   0    |    2   |     0       |     0    |
  |   1    |    6   |     0       |     0    |
  |   2    |   18   |   -36       |   -36    |
  |   3    |   54   |  -192       |  -156    |

The pair `(ΔKnill = -156, flux = 54)` at the final step is the
discrete Ψ₄ amplitude at peak. Both components grow geometrically
— the discrete analog of the "chirp" of a binary inspiral.

**On the BBH 7-edge seed** (via per-edge additivity #438): discrete
Ψ₄ amplitudes are exactly 7× their single-edge values, so the
integrated modulus-squared is 49× the single-edge baseline.

This module provides the framework's **first complex-valued
luminosity observable** — combining the two real-valued observables
developed in #446 (Knill delta) and #447 (event count) into the
discrete Ψ₄ analog needed for H8.
-/

import InfraFormalization.MergerGrowthDepthTrajectory
import InfraFormalization.DiscreteBondiFlux

namespace InfraFormalization
namespace DiscretePsiFour

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open BBHInitialData
open MultiRuleDiscovered
open DiscreteBondiFlux
open MergerGrowthDepthTrajectory

/-! ## Discrete Ψ₄ as a pair-valued list -/

/-- **`discretePsiFour`**: per-step composite of (ΔKnill, flux). Each
entry is (real_part = topology delta, imag_part = event count). Real
part is the change in causal-DAG Knill between consecutive depths;
imag part is the event count at that step. -/
def discretePsiFour (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    List (Int × Nat) :=
  let flux := perStepEventCount sys H n
  let knills := (List.range (n+1)).map (fun k =>
    knillEulerScaled (causalDAGOfEvolution sys H k))
  let deltas := (List.range n).map (fun k =>
    (knills.getD (k+1) 0) - (knills.getD k 0))
  deltas.zip flux

/-! ## Modulus and integrated luminosity -/

/-- Squared-modulus of a discrete Ψ₄ entry: `re² + im²`. Discrete
analog of |Ψ₄|² — the instantaneous gravitational-wave luminosity. -/
def psiFourModSq (entry : Int × Nat) : Int :=
  entry.1 * entry.1 + (entry.2 : Int) * (entry.2 : Int)

/-- Total integrated modulus-squared over a trajectory. Discrete
analog of ∫|Ψ₄|² dt — total radiated energy. -/
def integratedModSq (psi : List (Int × Nat)) : Int :=
  (psi.map psiFourModSq).foldr (· + ·) 0

/-! ## Verified Ψ₄ trajectory on edge12: edgeReversal (tree class) -/

/-- **`edgeReversal_psi4_trajectory`**: full discrete-Ψ₄ trajectory
for `edgeReversal` on `edge12` over 6 depths.

Knill sequence at depths 0-6: 0, 0, 6, 6, 0, -6, -18.
Deltas: 0, 6, 0, -6, -6, -12.
Flux: 1 event per step (linear).

Trajectory: (0,1), (6,1), (0,1), (-6,1), (-6,1), (-12,1). -/
theorem edgeReversal_psi4_trajectory :
    discretePsiFour edgeReversalSys seedEdge12 6 =
      [(0, 1), (6, 1), (0, 1), (-6, 1), (-6, 1), (-12, 1)] := by
  native_decide

/-! ## Verified Ψ₄ trajectory for the geometric champion -/

/-- **`exponential_psi4_signature`**: the `edgeReversal + tripleMerger`
combo on `edge12` over 4 depths exhibits **exponentially growing
Ψ₄ flux** — flux × 3 per step. Knill drops kick in at step 2 and
accelerate sharply at step 3 (delta = -156). -/
theorem exponential_psi4_signature :
    discretePsiFour edgeReversal_tripleMerger_Sys seedEdge12 4 =
      [(0, 2), (0, 6), (-36, 18), (-156, 54)] := by
  native_decide

/-! ## Integrated Ψ₄ modulus-squared -/

/-- **`integrated_psi4_modsq_champion`**: total integrated |Ψ₄|² for
the exponential-growth combo over 4 depths. Discrete analog of
total radiated energy.

Σ (re² + im²) = (0 + 4) + (0 + 36) + (1296 + 324) + (24336 + 2916)
              =  4 + 36 + 1620 + 27252 = 28912 -/
theorem integrated_psi4_modsq_champion :
    integratedModSq (discretePsiFour edgeReversal_tripleMerger_Sys seedEdge12 4) = 28912 := by
  native_decide

/-! ## Integrated Ψ₄ for edgeReversal tree-class baseline -/

/-- **`integrated_psi4_modsq_baseline`**: total |Ψ₄|² for
`edgeReversal` tree-class trajectory on `edge12` over 6 depths.

Σ = (0+1) + (36+1) + (0+1) + (36+1) + (36+1) + (144+1)
  = 1 + 37 + 1 + 37 + 37 + 145 = 258 -/
theorem integrated_psi4_modsq_baseline :
    integratedModSq (discretePsiFour edgeReversalSys seedEdge12 6) = 258 := by
  native_decide

/-! ## Per-edge additivity at the Ψ₄ level (BBH connection)

Per-edge additivity (#438, #447) tells us BBH-seed Ψ₄ values are
exactly 7× the single-edge baseline for both components, so
integrated |Ψ₄|² scales by 49 (since modulus is squared). -/

/-- **`bbhPsiFourPredicted_tripleMerger`**: the predicted BBH-seed
discrete Ψ₄ trajectory for the exponential-growth champion. By
per-edge additivity, this is 7× the `edge12` trajectory.
Each component multiplied by 7: (0,2)→(0,14), (0,6)→(0,42),
(-36,18)→(-252,126), (-156,54)→(-1092,378). -/
def bbhPsiFourPredicted_tripleMerger : List (Int × Nat) :=
  [(0, 14), (0, 42), (-252, 126), (-1092, 378)]

/-- The predicted BBH trajectory has integrated modulus-squared
49× the single-edge baseline. -/
theorem bbh_psi4_predicted_modsq :
    integratedModSq bbhPsiFourPredicted_tripleMerger = 49 * 28912 := by
  native_decide

/-! ## What this delivers

**First complex-valued discrete Ψ₄ analog** in the framework:

  * `discretePsiFour` — pair-valued (ΔKnill, flux) trajectory.
  * `psiFourModSq` and `integratedModSq` — discrete analogs of
    instantaneous and integrated gravitational-wave luminosity.
  * `edgeReversal_psi4_trajectory` — full 6-depth Ψ₄ signal for
    the tree-class rule.
  * `exponential_psi4_signature` — Ψ₄ trajectory for the
    exponential-growth combo showing |Ψ₄| growing each step.
  * `integrated_psi4_modsq_baseline` (258) and `_champion` (28912)
    — total radiated "energy" comparison: champion combo
    produces ~110× more total luminosity than tree baseline.
  * `bbh_psi4_predicted_modsq` — predicted BBH-seed integrated
    luminosity (49 × 28912 = 1416688) via per-edge additivity.

**Why this matters** (toward H8): the framework now exposes a
**complex-valued discrete Ψ₄ trajectory** with:

  * Per-step pair (ΔKnill, flux) at every step.
  * Modulus and integrated modulus — proxy for instantaneous and
    total gravitational-wave luminosity.
  * Per-edge additivity certified on the BBH seed.

This is the strongest available discrete substrate for matching
against an actual NR Ψ₄ waveform.

**Outstanding (H8 full closure / H9)**:

  * Scaling theorem: discrete Ψ₄ → continuum Ψ₄ as depth → ∞.
  * NR-waveform matching: fit the discrete chirp to GW150914 data.
  * Phase identification: ringdown frequency extraction.
-/

end DiscretePsiFour
end InfraFormalization
