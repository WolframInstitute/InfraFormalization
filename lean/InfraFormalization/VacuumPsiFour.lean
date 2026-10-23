/-
Values of `EnhancedPsi4.enhancedPsiFour` for `forkRule_2 + doubleCycle_5`
at depth 4.

`enhancedPsiFour sys H d` is an integer pair. The first entry is the
scaled Knill value of `causalDAGOfFireAll sys H d` minus the value at
depth d-1. The second entry is the scaled Knill value of
`branchialDAGOfFireAll sys H d`, the graph that links two events of the
same step that consume a common edge value. This relation is not the
branchial graph of the Wolfram model. Both graphs come from
`tracedFireAllEvolve`, which applies every match of every rule found in
the state, including matches that share edges. It is not a Wolfram model
update when matches overlap.

The module names refer to the Newman-Penrose scalar Ψ₄ and to vacuum
solutions. The module does not define a Weyl tensor, a polarization, a
complex number or a vacuum condition. It computes integer pairs.

The module computes by `native_decide` (PROVED-WITH-NATIVE-DECIDE):

  * On `seedEdge12` at depth 4 the pair is `(0, 240)`.
  * On `bbhInitial` at depth 4 the pair is `(0, 1680)`, with
    1680 = 7 × 240.
  * The sums of squares of the two pairs are 57600 and 49 × 57600.

`bbhInitial` is a 7-edge graph: two triangles on `{0,1,2}` and
`{3,4,5}` joined by the edge `{2,3}`.
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

/-! ## Values at depth 4 -/

theorem vacuum_psi4_eR_d4 :
    enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4 = (0, 240) := by
  native_decide

theorem vacuum_psi4_BBH_d4 :
    enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4 = (0, 1680) := by
  native_decide

/-! ## First entry zero, second entry nonzero -/

/-- On `seedEdge12` at depth 4, the first entry of the pair is 0 and the
second entry is nonzero (240). -/
theorem vacuum_psi4_purely_imaginary :
    (enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4).1 = 0 ∧
    (enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4).2 ≠ 0 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## The pair on `bbhInitial` -/

/-- On `bbhInitial` at depth 4 the pair is `(0, 1680)`, and its second
entry is 7 times the second entry on `seedEdge12`. -/
theorem bbh_vacuum_psi4_certified :
    enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4 = (0, 1680) ∧
    -- Second entry on bbhInitial = 7 × second entry on seedEdge12:
    (enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4).2 =
      7 * (enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4).2 := by
  refine ⟨?_, ?_⟩
  · exact vacuum_psi4_BBH_d4
  · rw [vacuum_psi4_BBH_d4, vacuum_psi4_eR_d4]; decide

/-! ## Sums of squares -/

/-- For the pair on `seedEdge12` at depth 4: `0² + 240² = 57600`. -/
theorem vacuum_modsq_edge12 :
    let p := enhancedPsiFour fork_doubleCycle_Sys seedEdge12 4
    p.1 * p.1 + p.2 * p.2 = 57600 := by
  native_decide

/-- For the pair on `bbhInitial` at depth 4: `0² + 1680² = 2822400 =
49 × 57600`. -/
theorem vacuum_modsq_BBH :
    let p := enhancedPsiFour fork_doubleCycle_Sys bbhInitial 4
    p.1 * p.1 + p.2 * p.2 = 49 * 57600 := by
  native_decide

/-! ## Contents

  * `vacuum_psi4_eR_d4`: `(0, 240)` on `seedEdge12`.
  * `vacuum_psi4_BBH_d4`: `(0, 1680)` on `bbhInitial`.
  * `vacuum_psi4_purely_imaginary`: first entry 0, second entry nonzero,
    on `seedEdge12`.
  * `bbh_vacuum_psi4_certified`: the pair on `bbhInitial` and the factor
    7 between second entries.
  * `vacuum_modsq_edge12` (57600), `vacuum_modsq_BBH` (49 × 57600).

All statements concern `forkRule_2 + doubleCycle_5` at depth 4. The
module states nothing about gravitational radiation, polarization or a
continuum limit.
-/

end VacuumPsiFour
end InfraFormalization
