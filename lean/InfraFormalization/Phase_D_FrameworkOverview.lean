/-
A conjunction of eighteen finite statements about the fire-all evolution.

The statements are values of scaled Knill invariants for specific small
rules, seeds and depths, computed by `native_decide`
(PROVED-WITH-NATIVE-DECIDE). The graphs come from `tracedFireAllEvolve`.
`fireAllStep` applies every match of every rule found in the state,
including matches that share edges. It is not a Wolfram model update
when matches overlap, and the values do not describe Wolfram model
evolutions. The "branchial" graphs (`branchialDAGOfFireAll`) link two
events of the same step that consume a common edge value. They are not
the branchial graph of the Wolfram model.

Definitions used:

  * `discreteRicciScalar sys d` (R): scaled Knill value of
    `causalDAGOfFireAll sys seedEdge12 d`.
  * `discreteBranchialDensity sys d` (B): scaled Knill value of
    `branchialDAGOfFireAll sys seedEdge12 d`.
  * `discreteMetricTensor sys d`: the integer pair `(R, B)`.
  * `hasLorentzianSignature sys d`: `true` when R and B are nonzero and
    of opposite sign.
  * `bbhInitial`: a 7-edge graph, two triangles on `{0,1,2}` and
    `{3,4,5}` joined by the edge `{2,3}`.

The statement that the seed-edge proportionality holds for every system,
seed and depth is OPEN. This module checks it for `seedPath123` and
`bbhInitial` with two systems at depth 3.
-/

import InfraFormalization.BBHMetricTensor
import InfraFormalization.MetricSignatureEvolution
import InfraFormalization.UnifiedEHBalance
import InfraFormalization.BranchialFromInteraction
import InfraFormalization.DualSideIndependence
import InfraFormalization.BranchialUniversalAdditivity
import InfraFormalization.RicciScalarDepthTrajectory
import InfraFormalization.DiscreteQuantumGravity

namespace InfraFormalization
namespace Phase_D_FrameworkOverview

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
open DiscreteMetricTensor

/-! ## The conjunction -/

/-- A conjunction of eighteen finite statements. R is
`discreteRicciScalar` and B is `discreteBranchialDensity` (values on
`seedEdge12`).

  1. `bbhInitial` has 7 edges.
  2. R(`edgeReversal + identityKeep`, 3) = -24.
  3. B(`edgeReversal + identityKeep`, 3) = 30.
  4. The fire-all contention graph of `edgeReversalSys` on `seedEdge12`
     at depth 3 has scaled Knill value 0.
  5. The fire-all causal graph of `edgeReversal + identityKeep` on
     `seedPath123` at depth 3 has scaled Knill value 2 · (-24).
  6. The fire-all contention graph of the same system on `seedPath123`
     at depth 3 has scaled Knill value 2 · 30.
  7. R(`edgeReversal + identityKeep`, 4) > R(`edgeReversal + identityKeep`, 3).
  8. R(`edgeReversal + identityKeep`, 2) = R(`edgeReversal + forkRule_2`, 2).
  9. B(`edgeReversal + identityKeep`, 2) ≠ B(`edgeReversal + forkRule_2`, 2).
  10. `discreteMetricTensor edgeReversal_identity_Sys 3 = (-24, 30)`.
  11. `hasLorentzianSignature edgeReversal_identity_Sys 3 = true`.
  12. `hasLorentzianSignature edgeReversal_identity_Sys 4 = false`.
  13. 5 · R + 4 · B = 0 for `edgeReversal + identityKeep` at depth 3.
  14. 11 · R + 7 · B = 0 for `edgeReversal + forkRule_2` at depth 3.
  15-18. For both systems at depth 3, the causal and contention values on
     `bbhInitial` equal 7 times R and 7 times B. -/
theorem phase_D_framework_complete :
    -- (1) Edge count of bbhInitial
    bbhInitial.length = 7 ∧
    -- (2) R value
    discreteRicciScalar edgeReversal_identity_Sys 3 = -24 ∧
    -- (3) B value
    discreteBranchialDensity edgeReversal_identity_Sys 3 = 30 ∧
    -- (4) Single-rule contention value 0
    knillEulerScaled (branchialDAGOfFireAll edgeReversalSys seedEdge12 3) = 0 ∧
    -- (5) Causal value on seedPath123, d=3
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys
      UniversalAdditivity.seedPath123 3) = 2 * (-24) ∧
    -- (6) Contention value on seedPath123, d=3
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys
      UniversalAdditivity.seedPath123 3) = 2 * 30 ∧
    -- (7) R at depth 4 exceeds R at depth 3
    discreteRicciScalar edgeReversal_identity_Sys 4 >
      discreteRicciScalar edgeReversal_identity_Sys 3 ∧
    -- (8-9) Same R, different B
    discreteRicciScalar edgeReversal_identity_Sys 2 =
      discreteRicciScalar edgeReversal_fork_Sys 2 ∧
    discreteBranchialDensity edgeReversal_identity_Sys 2 ≠
      discreteBranchialDensity edgeReversal_fork_Sys 2 ∧
    -- (10) The pair (R, B)
    discreteMetricTensor edgeReversal_identity_Sys 3 = (-24, 30) ∧
    -- (11) Sign test at depth 3
    hasLorentzianSignature edgeReversal_identity_Sys 3 = true ∧
    -- (12) Sign test at depth 4
    hasLorentzianSignature edgeReversal_identity_Sys 4 = false ∧
    -- (13) Linear relation for eR + id
    5 * discreteRicciScalar edgeReversal_identity_Sys 3 +
      4 * discreteBranchialDensity edgeReversal_identity_Sys 3 = 0 ∧
    -- (14) Linear relation for eR + fork
    11 * discreteRicciScalar edgeReversal_fork_Sys 3 +
      7 * discreteBranchialDensity edgeReversal_fork_Sys 3 = 0 ∧
    -- (15-18) Values on bbhInitial equal 7 times the seedEdge12 values
    knillEulerScaled (causalDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) =
      7 * discreteRicciScalar edgeReversal_identity_Sys 3 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_identity_Sys bbhInitial 3) =
      7 * discreteBranchialDensity edgeReversal_identity_Sys 3 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) =
      7 * discreteRicciScalar edgeReversal_fork_Sys 3 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_fork_Sys bbhInitial 3) =
      7 * discreteBranchialDensity edgeReversal_fork_Sys 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> native_decide

/-! ## Contents

`phase_D_framework_complete` is a conjunction of eighteen finite
statements, all proved by `native_decide`. It concerns the systems
`edgeReversal`, `edgeReversal + identityKeep` and
`edgeReversal + forkRule_2`, depths 2 to 4, and the seeds `seedEdge12`,
`seedPath123` and `bbhInitial`. It states no relation to general
relativity, quantum mechanics or black holes, and no continuum limit.
-/

end Phase_D_FrameworkOverview
end InfraFormalization
