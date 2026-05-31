/-
**Degree-variance screener on `ExecHG ℕ`** (#407).

A FOURTH independent curvature family alongside Forman (#384),
transport-Ollivier (#402), and Higuchi (#405). Built on the integer-
valued un-normalised graph-Laplacian scalar

  Σ_v deg(v)² · |V| − (Σ_v deg(v))²

which is `|V|² · Var_{V}(deg)`: integer, decide-checkable, and
independent of Forman/Transport/Higuchi (all three are first-order in
`deg(v)`, this one is second-order in the *distribution* of `deg`).

On regular graphs (every vertex same degree) this scalar vanishes; on
graphs with degree heterogeneity it is strictly positive. In spectral
terms, `|V| · Σ deg² − (Σ deg)² = |V| · 2 · Σ_e (deg(u)+deg(v))/2 − …`
relates to the L²-norm of the Laplacian's degree-diagonal, i.e. to
`tr(L²) − (tr L)²/|V|`, the Laplacian-spectral variance.
-/

import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecMetrics
import InfraFormalization.OllivierRicciExec

namespace InfraFormalization
namespace DegreeVarianceScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics

/-- **Sum of squared degrees** of `H` (over its vertex list). -/
def degSquaredSum (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => (execAdjDegree H v : ℤ)^2 + acc) 0

/-- **Sum of degrees** of `H` (= 2·|E| for a simple graph). -/
def degSum (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => (execAdjDegree H v : ℤ) + acc) 0

/-- **Scaled degree variance** of `H`:
`|V| · Σ deg² − (Σ deg)²`. Integer-valued, decide-checkable, vanishes
on regular graphs, strictly positive on graphs with degree
heterogeneity. -/
def degVarianceScaled (H : ExecHG ℕ) : ℤ :=
  let n : ℤ := (vertexList H).length
  n * degSquaredSum H - (degSum H)^2

/-- The per-state degree-variance trace of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.degVarianceTrace
    (d : Dossier) : List ℤ :=
  d.states.map degVarianceScaled

/-- A candidate's degree-variance trace is constant along its run. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.degVarianceConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.degVarianceTrace

/-! ## Concrete cross-checks pin the numerics

The four chosen seeds span the regular-vs-heterogeneous degree axis: -/

/-- **K₃** (triangle): all three vertices have degree 2, so
`|V|·Σ deg² − (Σ deg)² = 3·12 − 36 = 0`. K₃ is degree-regular. -/
example : degVarianceScaled OllivierRicciExec.k3 = 0 := by native_decide

/-- **4-cycle**: all four vertices have degree 2, so
`4·16 − 64 = 0`. Cycle is degree-regular. -/
example : degVarianceScaled OllivierRicciExec.cycle4 = 0 := by native_decide

/-- **Single edge `{1, 2}`**: both endpoints have degree 1, so
`2·2 − 4 = 0`. An isolated edge is degree-regular. -/
example : degVarianceScaled RuleSignatureExecMetrics.edge12 = 0 := by native_decide

/-- **3-path `[{1,2}, {2,3}]`**: degrees `[1, 2, 1]`,
`3·(1+4+1) − (1+2+1)² = 18 − 16 = 2`. The path's degree heterogeneity
shows up as a strictly positive scalar. -/
example : degVarianceScaled RuleSignatureExecMetrics.path123 = 2 := by
  native_decide

/-! ## End-to-end: degree-variance distinguishes regular from irregular runs -/

/-- **Trivial identity on edge12**: state never changes, so the trace
is `[0, 0, 0]` (edge12 is degree-regular). -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        RuleSignatureExecMetrics.edge12 2).degVarianceTrace = [0, 0, 0] := by
  native_decide

/-- The constancy verdict for edge-append on edge12: `false`. The
rule perturbs the path's degree distribution, so the scalar trace is
non-constant. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).degVarianceConstant = false := by
  native_decide

end DegreeVarianceScreener
end InfraFormalization
