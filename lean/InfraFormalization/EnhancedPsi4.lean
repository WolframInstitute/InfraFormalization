/-
A pair of integers built from causal and contention Knill values.

`enhancedPsiFour sys H d` is the pair (causal Knill at depth d minus
causal Knill at depth d-1, contention Knill at depth d). The causal
graph is `causalDAGOfFireAll`. The contention graph is
`branchialDAGOfFireAll`, which joins two events of the same step that
consume a common edge; it is not the Wolfram-model branchial graph.
The evolution is `fireAllStep`, which applies every match of every
rule found in the state, including matches that share edges. It is
not a Wolfram model update when matches overlap.

The name refers to the Newman-Penrose scalar Ψ₄. The module defines no
Weyl tensor, null tetrad or waveform, and proves no relation to Ψ₄.

Values for `eR + id` on `seedEdge12` (PROVED-WITH-NATIVE-DECIDE):

  | d | causal K | contention K | enhancedPsiFour |
  |---|----------|--------------|-----------------|
  | 3 |   -24    |      30      |    (-18, 30)    |
  | 4 |     6    |      42      |     (30, 42)    |

`bbhEnhancedPsiFour_eR_id` multiplies the `seedEdge12` pair by 7. It
does not evaluate `bbhInitial`.
-/

import InfraFormalization.BBHBranchialMultiDepth
import InfraFormalization.DiscretePsiFour
import InfraFormalization.DiscreteRicciScalar

namespace InfraFormalization
namespace EnhancedPsi4

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

/-! ## Definition -/

/-- `enhancedPsiFour sys H d`: the pair whose first component is the
scaled Knill value of `causalDAGOfFireAll sys H d` minus the value at
depth `d - 1` (minus 0 when `d = 0`), and whose second component is
the scaled Knill value of `branchialDAGOfFireAll sys H d`. -/
def enhancedPsiFour (sys : ExecSystem) (H : ExecHG ℕ) (d : Nat) :
    Int × Int :=
  let causal_d := knillEulerScaled (causalDAGOfFireAll sys H d)
  let causal_prev :=
    if d = 0 then 0
    else knillEulerScaled (causalDAGOfFireAll sys H (d - 1))
  let branchial_d := knillEulerScaled (branchialDAGOfFireAll sys H d)
  (causal_d - causal_prev, branchial_d)

/-! ## Values for eR + id on seedEdge12 -/

theorem enhanced_psi4_eR_id_3 :
    enhancedPsiFour edgeReversal_identity_Sys seedEdge12 3 = (-18, 30) := by
  native_decide

theorem enhanced_psi4_eR_id_4 :
    enhancedPsiFour edgeReversal_identity_Sys seedEdge12 4 = (30, 42) := by
  native_decide

/-! ## Depths 3 and 4 together -/

/-- `enhanced_psi4_eR_id_trajectory`: for `eR + id` on `seedEdge12`,
`enhancedPsiFour` is `(-18, 30)` at depth 3 and `(30, 42)` at
depth 4. -/
theorem enhanced_psi4_eR_id_trajectory :
    enhancedPsiFour edgeReversal_identity_Sys seedEdge12 3 = (-18, 30) ∧
    enhancedPsiFour edgeReversal_identity_Sys seedEdge12 4 = (30, 42) :=
  ⟨enhanced_psi4_eR_id_3, enhanced_psi4_eR_id_4⟩

/-! ## Sums of squares -/

/-- Sum of squares at depth 3 for `eR + id`: `(-18)² + 30² = 1224`. -/
theorem mod_sq_eR_id_3 :
    let p := enhancedPsiFour edgeReversal_identity_Sys seedEdge12 3
    p.1 * p.1 + p.2 * p.2 = 1224 := by
  native_decide

/-- Sum of squares at depth 4 for `eR + id`: `30² + 42² = 2664`. -/
theorem mod_sq_eR_id_4 :
    let p := enhancedPsiFour edgeReversal_identity_Sys seedEdge12 4
    p.1 * p.1 + p.2 * p.2 = 2664 := by
  native_decide

/-! ## Seven times the seedEdge12 pair -/

/-- `bbhEnhancedPsiFour_eR_id d`: the `seedEdge12` pair for `eR + id`
at depth `d`, with both components multiplied by 7. It is not computed
from an evolution of `bbhInitial`. -/
def bbhEnhancedPsiFour_eR_id (d : Nat) : Int × Int :=
  let p := enhancedPsiFour edgeReversal_identity_Sys seedEdge12 d
  (7 * p.1, 7 * p.2)

/-- `bbhEnhancedPsiFour_eR_id 3 = (-126, 210)`. -/
theorem bbh_enhanced_psi4_3 :
    bbhEnhancedPsiFour_eR_id 3 = (-126, 210) := by
  native_decide

/-- The sum of squares of `bbhEnhancedPsiFour_eR_id 3` is
`126² + 210² = 59976 = 49 * 1224`. -/
theorem bbh_mod_sq_eR_id_3 :
    let p := bbhEnhancedPsiFour_eR_id 3
    p.1 * p.1 + p.2 * p.2 = 49 * 1224 := by
  native_decide

/-! ## Summary

  * `enhancedPsiFour sys H d`: the pair (causal Knill difference from
    depth d-1 to d, contention Knill at depth d).
  * Values for `eR + id` on `seedEdge12`: `(-18, 30)` at depth 3 and
    `(30, 42)` at depth 4.
  * Sums of squares: 1224 at depth 3 and 2664 at depth 4.
  * `bbhEnhancedPsiFour_eR_id d`: 7 times the `seedEdge12` pair; at
    depth 3 it is `(-126, 210)` and its sum of squares is `49 * 1224`.

All values are PROVED-WITH-NATIVE-DECIDE.
-/

end EnhancedPsi4
end InfraFormalization
