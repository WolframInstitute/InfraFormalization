/-
A conjunction of twelve finite statements proved in other modules.

The statements are values of scaled Knill invariants, edge counts and
event counts for specific small rules, seeds and depths. Most of them
are computed from `tracedFireAllEvolve`. `fireAllStep` applies every
match of every rule found in the state, including matches that share
edges. It is not a Wolfram model update when matches overlap. The
"branchial" graphs (`branchialDAGOfFireAll`) link two events of the same
step that consume a common edge value. They are not the branchial graph
of the Wolfram model.

`bbhInitial` is a 7-edge graph: two triangles on `{0,1,2}` and
`{3,4,5}` joined by the edge `{2,3}`. The module name refers to quantum
gravity. The module does not define a quantum state, a gravitational
field or a black hole. The theorem
`discrete_quantum_gravity_certificate` lists the twelve statements.
All of them are PROVED-WITH-NATIVE-DECIDE or follow from such lemmas.
-/

import InfraFormalization.MultiRuleRDivergence
import InfraFormalization.BranchialRSpectrum
import InfraFormalization.BBHAnalogCertificate
import InfraFormalization.CurvatureDensityLimit
import InfraFormalization.RicciScalarDepthTrajectory

namespace InfraFormalization
namespace DiscreteQuantumGravity

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open BBHInitialData
open MultiRuleDiscovered
open MultiRuleRDivergence
open BranchialRSpectrum
open BBHAnalogCertificate
open DiscretePsiFour
open DiscreteBondiFlux
open BBHDeepEvolution
open UniversalAdditivity
open DiscreteRicciScalar
open RicciScalarDepthTrajectory
open CurvatureDensityLimit

/-! ## The conjunction -/

/-- A conjunction of twelve finite statements from imported modules:

  1. `bbhInitial` has 7 edges.
  2. At depth 6, the scaled Knill value of the fire-all causal graph of
     `edgeReversalSys` on `bbhInitial` is 7 times its value on
     `seedEdge12`.
  3. The fire-all per-step event counts of `edgeReversalSys` on
     `bbhInitial` over 6 steps are `[7, 7, 7, 7, 7, 7]`.
  4. `integratedModSq bbhPsiFourPredicted_tripleMerger = 49 * 28912`, an
     arithmetic fact about a literal list.
  5. `discreteRicciScalar doubleCycleSys_5 4 = -6`.
  6. `discreteRicciScalar bidirectedEdgeSys 4 = 126`.
  7. The scaled Knill value of `causalDAGOfEvolution doubleCycleSys_5
     bbhInitial 4` is `7 * (-6)`.
  8. The scaled Knill value of `causalDAGOfEvolution doubleCycleSys_5
     seedPath123 4` is `2 * (-6)`.
  9. `discreteRicciScalar edgeReversalSys 3 =
     discreteRicciScalar identityKeepSys 3`.
  10. The fire-all contention graph of `edgeReversalSys` on `seedEdge12`
      at depth 3 has scaled Knill value 0.
  11. The same quantity for `edgeReversal + tripleMerger` is 78.
  12. `discreteRicciScalar edgeReversal_fork_Sys 4` differs from
      `discreteRicciScalar edgeReversalSys 4 +
      discreteRicciScalar forkSys_2 4`.

Items 7 and 8 use `causalDAGOfEvolution`, which is built from
`tracedSingleWayEvolve` (edge-disjoint matches). The other evolution
items use the fire-all operator. -/
theorem discrete_quantum_gravity_certificate :
    -- Values on bbhInitial:
    bbhInitial.length = 7 ∧
    knillEulerScaled (causalDAGOfFireAll edgeReversalSys bbhInitial 6) =
      7 * knillEulerScaled (causalDAGOfFireAll edgeReversalSys seedEdge12 6) ∧
    perStepEventCount edgeReversalSys bbhInitial 6 = [7, 7, 7, 7, 7, 7] ∧
    integratedModSq bbhPsiFourPredicted_tripleMerger = 49 * 28912 ∧
    -- discreteRicciScalar values:
    discreteRicciScalar doubleCycleSys_5 4 = -6 ∧
    discreteRicciScalar bidirectedEdgeSys 4 = 126 ∧
    -- Factor 7 and factor 2 relative to the single edge (single-way trace):
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 bbhInitial 4) = 7 * (-6) ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) = 2 * (-6) ∧
    -- Equal R at depth 3 for two rules:
    discreteRicciScalar edgeReversalSys 3 = discreteRicciScalar identityKeepSys 3 ∧
    -- Contention-graph values:
    knillEulerScaled (branchialDAGOfFireAll edgeReversalSys seedEdge12 3) = 0 ∧
    knillEulerScaled (branchialDAGOfFireAll edgeReversal_tripleMerger_Sys seedEdge12 3) = 78 ∧
    -- Multi-rule R differs from the sum of the single-rule values:
    discreteRicciScalar edgeReversal_fork_Sys 4 ≠
      discreteRicciScalar edgeReversalSys 4 + discreteRicciScalar forkSys_2 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bbhInitial_edge_count
  · exact bbh_additivity_extends_depth6
  · exact edgeReversal_bbh_flux
  · exact bbh_psi4_predicted_modsq
  · exact R_doubleCycle_5_4
  · exact R_bidirected_4
  · rw [doubleCycle_5_bbh_knill_neg42]; rfl
  · rw [doubleCycle_5_path_knill_neg12]; rfl
  · rw [R_universal_at_depth3_edgeReversal, R_universal_at_depth3_identityKeep]
  · exact edgeReversal_branchial_0
  · exact eR_tripleMerger_branchial_78
  · exact R_sum_combination_fails.2.1

/-! ## Contents

`discrete_quantum_gravity_certificate` is a conjunction of twelve
statements, each proved by citing a lemma from an imported module. Those
lemmas are proved by `native_decide` or `decide`. The theorem states no
relation to general relativity, quantum mechanics or black holes, and no
continuum limit.
-/

end DiscreteQuantumGravity
end InfraFormalization
