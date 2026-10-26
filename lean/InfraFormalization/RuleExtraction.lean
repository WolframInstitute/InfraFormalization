/-
Five named rules that satisfy `quintStablyClassifiable`.

The module defines five rules with left-hand side `{0,1}`: identity, `{0,1} → {0,1},{0,2}`,
reversal, `{0,1} → {0,1},{1,0}` and `{0,1} → {0,1},{2,1}`. It proves that each satisfies
`quintStablyClassifiable` on `seedSet` at depth 2, and evaluates traces of the identity, reversal
and bidirection rules under `canonicalDossier`, which applies `singleWayStep`. On the evaluated
seeds these traces are constant. All values are checked by `native_decide`.
-/

import InfraFormalization.DualCurvatureScreener

namespace InfraFormalization
namespace RuleExtraction

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch
open DualCurvatureScreener

/-! ## Rules -/

/-- The left-hand-side edge `{0, 1}` over the two bound vertices `Fin 2`. -/
private def lhsEdge : Hyperedge (Fin 2) := ⟨[0, 1], List.cons_ne_nil _ _⟩

/-- The edge `{0, 1}` over `Fin 3` (two bound vertices and one fresh vertex). -/
private def lhsEdgeFin3 : Hyperedge (Fin 3) := ⟨[0, 1], List.cons_ne_nil _ _⟩

private def reverseFin3 : Hyperedge (Fin 3) := ⟨[1, 0], List.cons_ne_nil _ _⟩

private def freshSinkFin3 : Hyperedge (Fin 3) := ⟨[0, 2], List.cons_ne_nil _ _⟩

private def freshSourceFin3 : Hyperedge (Fin 3) := ⟨[2, 1], List.cons_ne_nil _ _⟩

/-- `{0, 1} → {0, 1}`. -/
def quintRuleIdentity : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [lhsEdge]
  rhs := [lhsEdgeFin3]

/-- `{0, 1} → {0, 1}, {0, 2}` with fresh vertex `2`. -/
def quintRuleFreshSink : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [lhsEdge]
  rhs := [lhsEdgeFin3, freshSinkFin3]

/-- `{0, 1} → {1, 0}`. -/
def quintRuleReversal : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [lhsEdge]
  rhs := [reverseFin3]

/-- `{0, 1} → {0, 1}, {1, 0}`. -/
def quintRuleBidirect : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [lhsEdge]
  rhs := [lhsEdgeFin3, reverseFin3]

/-- `{0, 1} → {0, 1}, {2, 1}` with fresh vertex `2`. -/
def quintRuleFreshSource : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [lhsEdge]
  rhs := [lhsEdgeFin3, freshSourceFin3]

/-! ## `quintStablyClassifiable` on `seedSet` at depth 2 -/

/-- `quintRuleIdentity` satisfies `quintStablyClassifiable` on `seedSet` at depth 2. -/
theorem quintRuleIdentity_quintStable :
    quintStablyClassifiable quintRuleIdentity seedSet 2 = true := by
  native_decide

theorem quintRuleFreshSink_quintStable :
    quintStablyClassifiable quintRuleFreshSink seedSet 2 = true := by
  native_decide

theorem quintRuleReversal_quintStable :
    quintStablyClassifiable quintRuleReversal seedSet 2 = true := by
  native_decide

theorem quintRuleBidirect_quintStable :
    quintStablyClassifiable quintRuleBidirect seedSet 2 = true := by
  native_decide

theorem quintRuleFreshSource_quintStable :
    quintStablyClassifiable quintRuleFreshSource seedSet 2 = true := by
  native_decide

/-! ## Traces at depth 2 -/

/-! ### `quintRuleIdentity` on `edge12`, `path123` and `cycle4` -/

example : (canonicalDossier quintRuleIdentity edge12 2).formanScalarTrace
    = [4, 4, 4] := by native_decide
example : (canonicalDossier quintRuleIdentity edge12 2).transportScalarTrace
    = [-2, -2, -2] := by native_decide
example : (canonicalDossier quintRuleIdentity edge12 2).higuchiScalarTrace
    = [2, 2, 2] := by native_decide
example : (canonicalDossier quintRuleIdentity edge12 2).degVarianceTrace
    = [0, 0, 0] := by native_decide
example : (canonicalDossier quintRuleIdentity edge12 2).squareCountTrace
    = [0, 0, 0] := by native_decide

example : (canonicalDossier quintRuleIdentity path123 2).formanScalarTrace
    = [4, 4, 4] := by native_decide
example : (canonicalDossier quintRuleIdentity path123 2).transportScalarTrace
    = [-16, -16, -16] := by native_decide
example : (canonicalDossier quintRuleIdentity path123 2).higuchiScalarTrace
    = [2, 2, 2] := by native_decide
example : (canonicalDossier quintRuleIdentity path123 2).degVarianceTrace
    = [2, 2, 2] := by native_decide
example : (canonicalDossier quintRuleIdentity path123 2).squareCountTrace
    = [0, 0, 0] := by native_decide

example : (canonicalDossier quintRuleIdentity cycle4 2).formanScalarTrace
    = [0, 0, 0] := by native_decide
example : (canonicalDossier quintRuleIdentity cycle4 2).transportScalarTrace
    = [-64, -64, -64] := by native_decide
example : (canonicalDossier quintRuleIdentity cycle4 2).higuchiScalarTrace
    = [0, 0, 0] := by native_decide
example : (canonicalDossier quintRuleIdentity cycle4 2).degVarianceTrace
    = [0, 0, 0] := by native_decide
example : (canonicalDossier quintRuleIdentity cycle4 2).squareCountTrace
    = [8, 8, 8] := by native_decide

/-! ### `quintRuleReversal` -/

example : (canonicalDossier quintRuleReversal edge12 2).formanScalarTrace
    = [4, 4, 4] := by native_decide
example : (canonicalDossier quintRuleReversal cycle4 2).squareCountTrace
    = [8, 8, 8] := by native_decide

/-! ### `quintRuleBidirect` -/

example : (canonicalDossier quintRuleBidirect edge12 2).formanScalarTrace
    = [4, 4, 4] := by native_decide
example : (canonicalDossier quintRuleBidirect cycle4 2).squareCountTrace
    = [8, 8, 8] := by native_decide

/-! ## Rate bounds with `c = 0`

`rateBounded trace tgt 0` holds iff every entry of `trace` equals `tgt`. -/

theorem quintRuleIdentity_edge12_forman_rateBounded :
    rateBounded (canonicalDossier quintRuleIdentity edge12 2).formanScalarTrace
      4 0 = true := by native_decide

theorem quintRuleIdentity_edge12_transport_rateBounded :
    rateBounded (canonicalDossier quintRuleIdentity edge12 2).transportScalarTrace
      (-2) 0 = true := by native_decide

theorem quintRuleIdentity_edge12_higuchi_rateBounded :
    rateBounded (canonicalDossier quintRuleIdentity edge12 2).higuchiScalarTrace
      2 0 = true := by native_decide

theorem quintRuleIdentity_edge12_degvariance_rateBounded :
    rateBounded (canonicalDossier quintRuleIdentity edge12 2).degVarianceTrace
      0 0 = true := by native_decide

theorem quintRuleIdentity_edge12_squarecount_rateBounded :
    rateBounded (canonicalDossier quintRuleIdentity edge12 2).squareCountTrace
      0 0 = true := by native_decide

theorem quintRuleReversal_edge12_forman_rateBounded :
    rateBounded (canonicalDossier quintRuleReversal edge12 2).formanScalarTrace
      4 0 = true := by native_decide

theorem quintRuleBidirect_edge12_forman_rateBounded :
    rateBounded (canonicalDossier quintRuleBidirect edge12 2).formanScalarTrace
      4 0 = true := by native_decide

end RuleExtraction
end InfraFormalization
