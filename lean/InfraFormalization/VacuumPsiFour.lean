/-
**B4-vacuum-psi-four: enhanced Ψ₄ in the vacuum-like regime**
(#477; H8 vacuum-regime application).

The enhanced discrete Ψ₄ (#472) = (causal ΔKnill, branchial K).
In the vacuum-like regime (#474-#476), R = 0 ⇒ ΔKnill_causal = 0
between consecutive depths once both are in the regime.

This module **certifies the enhanced Ψ₄ trajectory in the vacuum
regime**, giving a clean **purely imaginary** Ψ₄ signal — the
discrete analog of how vacuum-GR has zero classical "plus"
polarization but non-zero quantum "cross" polarization in this
regime.

**Headline result** (all `native_decide`-certified):

For `fork + doubleCycle_5` enhanced Ψ₄ at depth 4 (after the
R-degeneracy kicks in):

  * `Re(Ψ₄_enh) = ΔKnill_causal = 0 - 0 = 0`.
  * `Im(Ψ₄_enh) = B(d=4) = 240`.

So `Ψ₄_enh(d=4) = (0, 240)` — **purely imaginary** Ψ₄ signal.

This is qualitatively distinct from the Lorentzian regime
(#472 enhanced Ψ₄): in vacuum regime, the gravitational-wave
"real polarization" component vanishes.

**Why this matters** (physical interpretation):

In continuum GR:

  * Classical vacuum has zero Ricci scalar (R = 0).
  * Gravitational waves have polarization (+, ×) decomposition.
  * In pure gravitational radiation (no source), the (+) component
    can vanish while (×) persists.

The framework's discrete analog:

  * Vacuum-like regime: Re(Ψ₄_enh) = 0.
  * Quantum amplitude (Im part) persists and grows.

This is the **discrete-physics analog of pure (×) polarization
gravitational radiation**.

**BBH application**:

For BBH: vacuum-regime Ψ₄ on BBH at depth 4 = `(0, 7·240) = (0, 1680)`
— pure quantum-amplitude signal with zero classical curvature
change.

This is the framework's **discrete substrate for pure-quantum-
amplitude vacuum gravitational radiation** — relevant for modeling
the asymptotic GW emission from BBH after the inspiral phase.
-/

import InfraFormalization.BBHVacuumRegime
import InfraFormalization.EnhancedPsi4

namespace InfraFormalization
namespace VacuumPsiFour

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open BBHInitialData
open EnhancedPsi4
open BBHVacuumRegime

/-! ## Vacuum-regime enhanced Ψ₄ at depth 4 -/

theorem vacuum_psi4_eR_d4 :
    enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4 = (0, 240) := by
  native_decide

theorem vacuum_psi4_BBH_d4 :
    enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4 = (0, 1680) := by
  native_decide

/-! ## Purely imaginary Ψ₄ characterization -/

/-- **`vacuum_psi4_purely_imaginary`**: in the vacuum-like regime
at depth 4, the enhanced Ψ₄ has **zero real part** and non-zero
imaginary part — the discrete analog of pure (×) polarization
gravitational radiation.

  * Re(Ψ₄_enh) = 0 (no classical-curvature change).
  * Im(Ψ₄_enh) = B = 240 ≠ 0 (quantum amplitude active). -/
theorem vacuum_psi4_purely_imaginary :
    (enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4).1 = 0 ∧
    (enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4).2 ≠ 0 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## BBH vacuum-regime Ψ₄ -/

/-- **`bbh_vacuum_psi4_certified`**: enhanced Ψ₄ on BBH in vacuum
regime at depth 4: `(0, 1680)` — 7× the single-edge baseline. -/
theorem bbh_vacuum_psi4_certified :
    enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4 = (0, 1680) ∧
    -- BBH = 7 × single-edge:
    (enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4).2 =
      7 * (enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4).2 := by
  refine ⟨?_, ?_⟩
  · exact vacuum_psi4_BBH_d4
  · rw [vacuum_psi4_BBH_d4, vacuum_psi4_eR_d4]; decide

/-! ## |Ψ₄|² in vacuum regime -/

/-- |Ψ₄|² for vacuum-regime fork + dCyc at depth 4 on edge12:
`0² + 240² = 57600`. Pure quantum-amplitude luminosity. -/
theorem vacuum_modsq_edge12 :
    let p := enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4
    p.1 * p.1 + p.2 * p.2 = 57600 := by
  native_decide

/-- |Ψ₄|² for vacuum-regime fork + dCyc at depth 4 on BBH:
`0² + 1680² = 2822400 = 49 × 57600`. -/
theorem vacuum_modsq_BBH :
    let p := enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4
    p.1 * p.1 + p.2 * p.2 = 49 * 57600 := by
  native_decide

/-! ## What this delivers

**Vacuum-regime enhanced Ψ₄ certifications**:

  * `vacuum_psi4_eR_d4`: `(0, 240)` on edge12.
  * `vacuum_psi4_BBH_d4`: `(0, 1680)` on BBH.
  * `vacuum_psi4_purely_imaginary`: Re=0 with Im≠0.
  * `bbh_vacuum_psi4_certified`: BBH = 7 × single-edge.
  * `vacuum_modsq_edge12` (57600), `vacuum_modsq_BBH` (49 × 57600).

**Why this matters** (H8 vacuum-regime characterization):

The framework's discrete Ψ₄ now has TWO well-characterized regimes:

  * **Lorentzian Ψ₄** (#472): complex value with both Re and Im
    non-zero — full gravitational+quantum signal.
  * **Vacuum Ψ₄** (this module): purely imaginary value — pure
    quantum-amplitude signal with vanishing classical curvature
    change.

This is qualitatively distinct from continuum NR Ψ₄, which is
always complex-valued in BBH simulations. The framework's vacuum
regime gives a **different physical regime** — pure quantum-
gravitational-radiation without classical curvature flux.

**For physics interpretation**:

The vacuum-regime Ψ₄ is a candidate for modeling:

  * **Pure cross-polarization GW** emission.
  * **Ringdown** phase asymptotic dynamics.
  * **Asymptotic Bondi radiation** at null infinity.

The Lorentzian Ψ₄ models full classical-quantum coupled dynamics
(inspiral + merger).

**For H9 (continuum endgame)**: the vacuum-regime Ψ₄ is the
framework's discrete prediction for the asymptotic vacuum-GR
gravitational-wave amplitude — a well-defined H9 sub-target for
continuum-limit analysis.
-/

end VacuumPsiFour
end InfraFormalization
