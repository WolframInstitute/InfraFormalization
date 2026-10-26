/-
Knill sum after one step for twelve named rules.

The module evaluates `knillEulerScaled (singleWayEvolve sys edge12 1)` for twelve single-rule
systems: the trivial identity, subdivision, the five rules of `LiteratureRules` and the five rules
of `RuleExtraction`. Each value is 6, the value at the seed `edge12`, checked by `native_decide`.
The left-hand sides of `triangleClosureRule`, `wheelerRule` and `jgorardNamedRule` have more than
one edge, so these rules have no match on `edge12` and the state after one step is the seed.
-/

import InfraFormalization.KnillRuleBridge
import InfraFormalization.LiteratureRules
import InfraFormalization.RuleExtraction
import InfraFormalization.RuleSignatureExecCorpus

namespace InfraFormalization
namespace RulePreservationClassification

open MultiwayExec
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open LiteratureRules
open RuleExtraction
open KnillDiscreteGaussBonnet
open KnillRuleBridge

/-- The seed with the single edge `{1, 2}`. -/
def edge12 : ExecHG ℕ := [⟨[1, 2], List.cons_ne_nil _ _⟩]

/-- `knillEulerScaled edge12 = 6`. -/
theorem edge12_knill_init : knillEulerScaled edge12 = 6 := by native_decide

/-! ## Single-rule systems -/

def trivialIdentitySys : ExecSystem := ⟨[trivialIdentityExecRule]⟩
def subdivisionSysLocal : ExecSystem := ⟨[subdivisionRule]⟩
def triangulationSys : ExecSystem := ⟨[triangulationRule]⟩
def triangleClosureSys : ExecSystem := ⟨[triangleClosureRule]⟩
def wheelerSys : ExecSystem := ⟨[wheelerRule]⟩
def jgorardSys : ExecSystem := ⟨[jgorardNamedRule]⟩
def tripleExtendSys : ExecSystem := ⟨[tripleExtendRule]⟩
def quintIdentitySys : ExecSystem := ⟨[quintRuleIdentity]⟩
def quintFreshSinkSys : ExecSystem := ⟨[quintRuleFreshSink]⟩
def quintReversalSys : ExecSystem := ⟨[quintRuleReversal]⟩
def quintBidirectSys : ExecSystem := ⟨[quintRuleBidirect]⟩
def quintFreshSourceSys : ExecSystem := ⟨[quintRuleFreshSource]⟩

/-! ## Knill sum after one step

Each theorem states `knillEulerScaled (singleWayEvolve sys edge12 1) = 6`. -/

theorem trivialIdentity_knill_after_one_step :
    knillEulerScaled (singleWayEvolve trivialIdentitySys edge12 1) = 6 := by
  native_decide

theorem subdivisionRule_knill_after_one_step :
    knillEulerScaled (singleWayEvolve subdivisionSysLocal edge12 1) = 6 := by
  native_decide

theorem triangulationRule_knill_after_one_step :
    knillEulerScaled (singleWayEvolve triangulationSys edge12 1) = 6 := by
  native_decide

theorem triangleClosureRule_knill_after_one_step :
    knillEulerScaled (singleWayEvolve triangleClosureSys edge12 1) = 6 := by
  native_decide

theorem wheelerRule_knill_after_one_step :
    knillEulerScaled (singleWayEvolve wheelerSys edge12 1) = 6 := by
  native_decide

theorem jgorardRule_knill_after_one_step :
    knillEulerScaled (singleWayEvolve jgorardSys edge12 1) = 6 := by
  native_decide

theorem tripleExtendRule_knill_after_one_step :
    knillEulerScaled (singleWayEvolve tripleExtendSys edge12 1) = 6 := by
  native_decide

theorem quintIdentity_knill_after_one_step :
    knillEulerScaled (singleWayEvolve quintIdentitySys edge12 1) = 6 := by
  native_decide

theorem quintFreshSink_knill_after_one_step :
    knillEulerScaled (singleWayEvolve quintFreshSinkSys edge12 1) = 6 := by
  native_decide

theorem quintReversal_knill_after_one_step :
    knillEulerScaled (singleWayEvolve quintReversalSys edge12 1) = 6 := by
  native_decide

theorem quintBidirect_knill_after_one_step :
    knillEulerScaled (singleWayEvolve quintBidirectSys edge12 1) = 6 := by
  native_decide

theorem quintFreshSource_knill_after_one_step :
    knillEulerScaled (singleWayEvolve quintFreshSourceSys edge12 1) = 6 := by
  native_decide

/-! ## Conjunctions -/

/-- The conjunction of the twelve values above. -/
theorem named_rules_knill_after_one_step :
    knillEulerScaled (singleWayEvolve trivialIdentitySys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve subdivisionSysLocal edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve triangulationSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve triangleClosureSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve wheelerSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve jgorardSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve tripleExtendSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve quintIdentitySys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve quintFreshSinkSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve quintReversalSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve quintBidirectSys edge12 1) = 6 ∧
    knillEulerScaled (singleWayEvolve quintFreshSourceSys edge12 1) = 6 :=
  ⟨trivialIdentity_knill_after_one_step, subdivisionRule_knill_after_one_step,
   triangulationRule_knill_after_one_step, triangleClosureRule_knill_after_one_step,
   wheelerRule_knill_after_one_step, jgorardRule_knill_after_one_step,
   tripleExtendRule_knill_after_one_step, quintIdentity_knill_after_one_step,
   quintFreshSink_knill_after_one_step, quintReversal_knill_after_one_step,
   quintBidirect_knill_after_one_step, quintFreshSource_knill_after_one_step⟩

/-- Three equalities between the values for pairs of rules: trivial identity and
`jgorardNamedRule`, subdivision and triangulation, `wheelerRule` and `quintRuleIdentity`. -/
theorem named_rules_knill_edge12_equalities :
    knillEulerScaled (singleWayEvolve trivialIdentitySys edge12 1) =
      knillEulerScaled (singleWayEvolve jgorardSys edge12 1) ∧
    knillEulerScaled (singleWayEvolve subdivisionSysLocal edge12 1) =
      knillEulerScaled (singleWayEvolve triangulationSys edge12 1) ∧
    knillEulerScaled (singleWayEvolve wheelerSys edge12 1) =
      knillEulerScaled (singleWayEvolve quintIdentitySys edge12 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trivialIdentity_knill_after_one_step, jgorardRule_knill_after_one_step]
  · rw [subdivisionRule_knill_after_one_step, triangulationRule_knill_after_one_step]
  · rw [wheelerRule_knill_after_one_step, quintIdentity_knill_after_one_step]

end RulePreservationClassification
end InfraFormalization
