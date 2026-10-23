/-
Signs and zeros of `discreteRicciScalar` (R) for four two-rule systems
at depths 2 to 5.

R is the scaled Knill value of `causalDAGOfFireAll sys seedEdge12 d`.
The graph comes from `tracedFireAllEvolve`, which applies every match of
every rule found in the state, including matches that share edges. It
is not a Wolfram model update when matches overlap. R is an integer
computed from a finite graph. It is not the Ricci scalar of a metric,
and R = 0 is not a vacuum condition.

Values of R, PROVED-WITH-NATIVE-DECIDE in this module or in `RGrowthRates`,
`PersistentRDegeneracy`, `DualSideIndependence`, `DiscreteMetricTensor`
and `RClosedForm`:

  | System                         | d=2 | d=3 | d=4                  | d=5                  |
  |--------------------------------|-----|-----|----------------------|----------------------|
  | edgeReversal + doubleCycle_5   |  0  | -24 | -108 (`RGrowthRates`)| -276 (`RGrowthRates`)|
  | edgeReversal + tripleMerger    |  0  | -36 | -192                 | -660                 |
  | edgeReversal + identityKeep    | -6  | -24 |  6                   | 132                  |
  | edgeReversal + forkRule_2      | -6  | -42 | -72                  | -36                  |
  | forkRule_2 + doubleCycle_5     |  6  |  0  |  0                   | not computed         |

The values -192 and -660 for `edgeReversal + tripleMerger` follow from
`RClosedForm`. For `edgeReversal + identityKeep`, R changes sign between
depths 3 and 4.
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

/-! ## R = 0 at depth 2 -/

theorem eR_dCyc_R_2_zero :
    discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 := by
  native_decide

theorem eR_tripleMerger_R_2_zero :
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 := by
  native_decide

/-- R at depths 2 and 3:

  * `edgeReversal + doubleCycle_5`: 0, -24.
  * `edgeReversal + tripleMerger`: 0, -36. -/
theorem vacuum_initialization :
    discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 ∧
    discreteRicciScalar edgeReversal_doubleCycle_Sys 3 = -24 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 3 = -36 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Sign change for `edgeReversal + identityKeep` -/

theorem eR_id_R_5_132 :
    discreteRicciScalar edgeReversal_identity_Sys 5 = 132 := by
  native_decide

/-- For `edgeReversal + identityKeep`, R(3) < 0, R(4) > 0 and
R(5) = 132. The values at depths 2 to 5 are -6, -24, 6, 132. -/
theorem R_sign_reversal_eR_id :
    discreteRicciScalar edgeReversal_identity_Sys 3 < 0 ∧
    discreteRicciScalar edgeReversal_identity_Sys 4 > 0 ∧
    discreteRicciScalar edgeReversal_identity_Sys 5 = 132 := by
  refine ⟨?_, ?_, eR_id_R_5_132⟩ <;> native_decide

/-! ## R < 0 at depths 2 to 5 for `edgeReversal + forkRule_2` -/

theorem eR_fork_R_5_neg36 :
    discreteRicciScalar edgeReversal_fork_Sys 5 = -36 := by
  native_decide

/-- For `edgeReversal + forkRule_2`, R < 0 at depths 2, 3, 4 and 5. The
values are -6, -42, -72, -36. -/
theorem persistent_lorentzian_eR_fork :
    discreteRicciScalar edgeReversal_fork_Sys 2 < 0 ∧
    discreteRicciScalar edgeReversal_fork_Sys 3 < 0 ∧
    discreteRicciScalar edgeReversal_fork_Sys 4 < 0 ∧
    discreteRicciScalar edgeReversal_fork_Sys 5 < 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Conjunction -/

/-- A conjunction of five finite statements about R:

  * R = 0 at depth 2 for `edgeReversal + doubleCycle_5` and for
    `edgeReversal + tripleMerger`.
  * R(3) · R(4) < 0 for `edgeReversal + identityKeep`.
  * R(5) < 0 for `edgeReversal + forkRule_2`.
  * R(4) = 0 for `forkRule_2 + doubleCycle_5`. -/
theorem R_zero_classification :
    -- R = 0 at depth 2:
    discreteRicciScalar edgeReversal_doubleCycle_Sys 2 = 0 ∧
    discreteRicciScalar edgeReversal_tripleMerger_Sys 2 = 0 ∧
    -- Sign change between depths 3 and 4:
    (discreteRicciScalar edgeReversal_identity_Sys 3) *
      (discreteRicciScalar edgeReversal_identity_Sys 4) < 0 ∧
    -- R < 0 at depth 5:
    discreteRicciScalar edgeReversal_fork_Sys 5 < 0 ∧
    -- R = 0 at depth 4:
    discreteRicciScalar fork_doubleCycle_Sys 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Contents

  * `vacuum_initialization`: R at depths 2 and 3 for
    `edgeReversal + doubleCycle_5` and `edgeReversal + tripleMerger`.
  * `R_sign_reversal_eR_id`: R < 0 at depth 3, R > 0 at depth 4, and
    R = 132 at depth 5 for `edgeReversal + identityKeep`.
  * `persistent_lorentzian_eR_fork`: R < 0 at depths 2 to 5 for
    `edgeReversal + forkRule_2`.
  * `R_zero_classification`: five of the finite statements above.

The module computes R at depths 2 to 5 only. Whether R of
`edgeReversal + forkRule_2` stays negative at depths 6 and above is OPEN.
-/

end RZeroCrossings
end InfraFormalization
