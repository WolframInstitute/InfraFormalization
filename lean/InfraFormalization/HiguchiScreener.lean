/-
Degree-defect vertex scalar on `ExecHG ℕ`.

Higuchi's combinatorial curvature of a planar graph is `1 − deg(v)/2 + Σ_{F ∋ v} 1/|F|`, summed over incident faces. This module drops the face term and defines the integer `2 − deg(v)` per vertex, where `deg` is `execAdjDegree`, and its sum over the vertices of a state. It also defines the trace of this sum along a `canonicalDossier`, which evolves by `singleWayStep`. Values on small examples are checked by `native_decide`.
-/

import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecMetrics
import InfraFormalization.OllivierRicciExec

namespace InfraFormalization
namespace HiguchiScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics

/-- The integer `2 − execAdjDegree H v`. -/
def higuchiVertexDoubled (H : ExecHG ℕ) (v : ℕ) : ℤ :=
  2 - (execAdjDegree H v : ℤ)

/-- The sum of `higuchiVertexDoubled H v` over `v ∈ vertexList H`. For a simple graph this is `2·|V| − 2·|E|`, which is `0` on a cycle. -/
def higuchiTotalDoubled (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => higuchiVertexDoubled H v + acc) 0

/-- The list of `higuchiTotalDoubled` values of the states of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.higuchiScalarTrace
    (d : Dossier) : List ℤ :=
  d.states.map higuchiTotalDoubled

/-- `true` when every entry of `higuchiScalarTrace` equals the first. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.higuchiScalarConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.higuchiScalarTrace

/-! ## Values on small graphs -/

/-- On K₃ each vertex has degree 2, so the total is `0`. -/
example : higuchiTotalDoubled OllivierRicciExec.k3 = 0 := by native_decide

/-- On the 4-cycle each vertex has degree 2, so the total is `0`. -/
example : higuchiTotalDoubled OllivierRicciExec.cycle4 = 0 := by native_decide

/-- On the single edge `{1, 2}` each endpoint has degree 1, so the total is `2`. -/
example : higuchiTotalDoubled RuleSignatureExecMetrics.edge12 = 2 := by
  native_decide

/-- On the path `[{1,2}, {2,3}]` the endpoints contribute 1 each and the middle vertex 0, so the total is `2`. -/
example : higuchiTotalDoubled RuleSignatureExecMetrics.path123 = 2 := by
  native_decide

/-! ## Traces along `singleWayStep` evolutions -/

/-- Under the identity rule from `edge12` the state does not change, and the trace over two steps is `[2, 2, 2]`. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        RuleSignatureExecMetrics.edge12 2).higuchiScalarTrace
      = [2, 2, 2] := by
  native_decide

/-- Under the rule `{a,b} → {a,b},{b,c}` from `edge12`, the trace over two steps is `[2, 2, 2]`. Each step adds one edge and one new vertex, so `2·|V| − 2·|E|` is unchanged. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).higuchiScalarTrace = [2, 2, 2] := by
  native_decide

/-- `higuchiScalarConstant` is `true` for the same dossier. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).higuchiScalarConstant = true := by
  native_decide

end HiguchiScreener
end InfraFormalization
