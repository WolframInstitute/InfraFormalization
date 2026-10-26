/-
Scaled degree variance on `ExecHG ℕ`.

This module defines the integer `|V| · Σ_v deg(v)² − (Σ_v deg(v))²`, which
equals `|V|² · Var(deg)`, and its trace along the states of a dossier. The
examples compute it on four small graphs and on two short runs. Values are
checked by `native_decide`.
-/

import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecMetrics
import InfraFormalization.OllivierRicciExec

namespace InfraFormalization
namespace DegreeVarianceScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics

/-- The sum of `deg(v)²` over the vertex list of `H`. -/
def degSquaredSum (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => (execAdjDegree H v : ℤ)^2 + acc) 0

/-- The sum of `deg(v)` over the vertex list of `H`. -/
def degSum (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => (execAdjDegree H v : ℤ) + acc) 0

/-- The integer `|V| · Σ deg² − (Σ deg)²`. -/
def degVarianceScaled (H : ExecHG ℕ) : ℤ :=
  let n : ℤ := (vertexList H).length
  n * degSquaredSum H - (degSum H)^2

/-- The per-state degree-variance trace of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.degVarianceTrace
    (d : Dossier) : List ℤ :=
  d.states.map degVarianceScaled

/-- All entries of the degree-variance trace equal its first entry. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.degVarianceConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.degVarianceTrace

/-! ## Values on four graphs -/

/-- Triangle: all degrees are 2, so `3·12 − 36 = 0`. -/
example : degVarianceScaled OllivierRicciExec.k3 = 0 := by native_decide

/-- 4-cycle: all degrees are 2, so `4·16 − 64 = 0`. -/
example : degVarianceScaled OllivierRicciExec.cycle4 = 0 := by native_decide

/-- Single edge `{1, 2}`: both degrees are 1, so `2·2 − 4 = 0`. -/
example : degVarianceScaled RuleSignatureExecMetrics.edge12 = 0 := by native_decide

/-- Path `[{1,2}, {2,3}]`: degrees `[1, 2, 1]`, so
`3·(1+4+1) − (1+2+1)² = 18 − 16 = 2`. -/
example : degVarianceScaled RuleSignatureExecMetrics.path123 = 2 := by
  native_decide

/-! ## Traces of two runs -/

/-- For the identity rule on `edge12` with 2 steps, the trace is
`[0, 0, 0]`. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        RuleSignatureExecMetrics.edge12 2).degVarianceTrace = [0, 0, 0] := by
  native_decide

/-- For the edge-append rule on `edge12` with 2 steps, the trace is not
constant. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).degVarianceConstant = false := by
  native_decide

end DegreeVarianceScreener
end InfraFormalization
