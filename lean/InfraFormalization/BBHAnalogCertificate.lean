/-
BBH analog bundle.

This module proves one conjunction, `bbh_analog_full_certificate`,
about the hypergraph `bbhInitial` (6 vertices, 7 two-vertex edges:
two triangles joined by the edge `{2,3}`) and the rule `edgeReversalSys`.

The name "BBH" is a label for this seed. The module defines no black
hole, metric or radiation field.

The evolution is `tracedFireAllEvolve` / `causalDAGOfFireAll`.
`fireAllStep` applies every match of every rule found in the state,
including matches that share edges. It is not a Wolfram model update
when matches overlap.

The conjuncts are values computed by `native_decide` (directly or
through the cited lemmas) for these specific seeds and depths:

  1. `bbhInitial` has 7 edges.
  2. The scaled Knill Euler characteristic of the fire-all causal
     graph of `edgeReversalSys` on `bbhInitial` is 0, -42 and -126 at
     depths 4, 5 and 6.
  3. At depth 6 this value equals 7 times the value on the one-edge
     seed `seedEdge12`.
  4. `perStepEventCount edgeReversalSys bbhInitial 6` is
     `[7, 7, 7, 7, 7, 7]`.
  5. `integratedModSq bbhPsiFourPredicted_tripleMerger = 49 * 28912`.
     The list `bbhPsiFourPredicted_tripleMerger` is written out by
     hand as 7 times the components of a one-edge trajectory. It is
     not computed from an evolution of `bbhInitial`.

Status: PROVED-WITH-NATIVE-DECIDE.
-/

import InfraFormalization.DiscretePsiFour
import InfraFormalization.BBHDeepEvolution

namespace InfraFormalization
namespace BBHAnalogCertificate

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open BBHInitialData
open BBHDeepEvolution
open DiscreteBondiFlux
open DiscretePsiFour

/-! ## The BBH bundle theorem -/

/-- `bbh_analog_full_certificate`: the conjunction of the edge count
of `bbhInitial`, the fire-all causal-graph Knill values of
`edgeReversalSys` on `bbhInitial` at depths 4, 5 and 6, the depth-6
equality with 7 times the `seedEdge12` value, the per-step event
counts at depth 6, and the integrated squared modulus of the
hand-written list `bbhPsiFourPredicted_tripleMerger`. -/
theorem bbh_analog_full_certificate :
    -- 1. bbhInitial has 7 edges:
    bbhInitial.length = 7 ∧
    -- 2. Fire-all causal-graph Knill on bbhInitial, depths 4-6:
    knillEulerScaled (causalDAGOfFireAll edgeReversalSys bbhInitial 4) = 0 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversalSys bbhInitial 5) = -42 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversalSys bbhInitial 6) = -126 ∧
    -- 3. Depth 6: bbhInitial value = 7 × seedEdge12 value:
    (knillEulerScaled (causalDAGOfFireAll edgeReversalSys bbhInitial 6) =
      7 * knillEulerScaled (causalDAGOfFireAll edgeReversalSys seedEdge12 6)) ∧
    -- 4. Per-step event counts on bbhInitial, depth 6:
    perStepEventCount edgeReversalSys bbhInitial 6 = [7, 7, 7, 7, 7, 7] ∧
    -- 5. Integrated squared modulus of the hand-written list:
    integratedModSq bbhPsiFourPredicted_tripleMerger = 49 * 28912 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bbhInitial_edge_count
  · exact edgeReversal_bbh_knill_zero
  · exact edgeReversal_bbh_depth5
  · exact edgeReversal_bbh_depth6
  · exact bbh_additivity_extends_depth6
  · exact edgeReversal_bbh_flux
  · exact bbh_psi4_predicted_modsq

/-! ## Lemmas used

  * `bbhInitial_edge_count`.
  * `edgeReversal_bbh_knill_zero`, `edgeReversal_bbh_depth5`,
    `edgeReversal_bbh_depth6`.
  * `bbh_additivity_extends_depth6`.
  * `edgeReversal_bbh_flux`.
  * `bbh_psi4_predicted_modsq`.

No statement in this module relates these values to a continuum
limit or to gravitational waveforms.
-/

end BBHAnalogCertificate
end InfraFormalization
