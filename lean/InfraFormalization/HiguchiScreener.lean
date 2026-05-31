/-
**Higuchi planar-style combinatorial curvature on `ExecHG ℕ`** (#367,
#405).

The classical Higuchi combinatorial curvature at a vertex `v` of a
planar graph is
  κ_H(v) := 1 − deg(v)/2 + Σ_{F ∋ v} 1/|F|
where the sum is over faces `F` incident to `v`. For our `ExecHG ℕ`
setting we use the simpler **Euler-defect form**
  κ_H(v) := 1 − deg(v)/2
which agrees with the full Higuchi formula on triangulated 2-manifolds
(after the standard face-sum reduction) and extends meaningfully to
arbitrary graphs. We keep the integer-valued doubled scalar
`2·κ_H(v) := 2 − deg(v)` for `decide`-checkability.

Aggregated per state: `sum_v (2 − deg(v))`. This is a THIRD independent
curvature family alongside triangle-Forman (#384) and transport-
Ollivier (#402). Together they give three independent angles on a
rule's curvature signature.
-/

import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecMetrics
import InfraFormalization.OllivierRicciExec

namespace InfraFormalization
namespace HiguchiScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics

/-- **Doubled Higuchi vertex curvature**: `2 − adjDegree(v)`. Integer-
valued, decide-checkable. -/
def higuchiVertexDoubled (H : ExecHG ℕ) (v : ℕ) : ℤ :=
  2 - (execAdjDegree H v : ℤ)

/-- **Doubled total Higuchi curvature** of `H`: sum over `vertexList H`
of `higuchiVertexDoubled`. For a triangulated 2-sphere this equals
`2·χ = 4` (Euler characteristic). For flat planar graphs (e.g., simple
cycles), it vanishes. -/
def higuchiTotalDoubled (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => higuchiVertexDoubled H v + acc) 0

/-- The per-state Higuchi-trace of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.higuchiScalarTrace
    (d : Dossier) : List ℤ :=
  d.states.map higuchiTotalDoubled

/-- A candidate's Higuchi trace is constant along its run. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.higuchiScalarConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.higuchiScalarTrace

/-! ## Concrete cross-checks pin the numerics -/

/-- **K₃** (triangle): each vertex has degree 2, so `κ_H(v) = 2 − 2 = 0`
for every `v`; total = `0`. K₃ is "flat" in Higuchi curvature even
though it has positive Ollivier-Ricci-style curvature. -/
example : higuchiTotalDoubled OllivierRicciExec.k3 = 0 := by native_decide

/-- **4-cycle**: each vertex has degree 2, same as K₃. Total = `0`
(flat in Higuchi). -/
example : higuchiTotalDoubled OllivierRicciExec.cycle4 = 0 := by native_decide

/-- **Single edge `{1, 2}`**: each endpoint has degree 1, so
`κ_H(v) = 2 − 1 = 1` for each; total = `2` (positive, sphere-like —
the "half-sphere defect" of an isolated edge). -/
example : higuchiTotalDoubled RuleSignatureExecMetrics.edge12 = 2 := by
  native_decide

/-- **3-path** `[{1,2}, {2,3}]`: endpoints degree 1 (κ = 1 each),
middle degree 2 (κ = 0); total = `2`. -/
example : higuchiTotalDoubled RuleSignatureExecMetrics.path123 = 2 := by
  native_decide

/-! ## End-to-end: Higuchi distinguishes runs that Forman/Transport may
not -/

/-- **Trivial identity on edge12**: state never changes, so the
Higuchi trace is constant at `[2, 2, 2]`. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        RuleSignatureExecMetrics.edge12 2).higuchiScalarTrace
      = [2, 2, 2] := by
  native_decide

/-- **Edge-append on edge12 — Higuchi is CONSERVED**. The
`{a,b} → {a,b},{b,c}` rule preserves the path shape (each application
extends the path by one edge with one new vertex), and a path of any
length has total Higuchi = `2` (two endpoint defects). So the trace
is `[2, 2, 2]` — constant! Forman + Transport both said this rule is
non-constant; Higuchi says it IS constant. The three screeners
disagree on which rules are stable, **detecting different aspects of
curvature**. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).higuchiScalarTrace = [2, 2, 2] := by
  native_decide

/-- And so the Higuchi-constancy verdict on edge-append is `true`. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).higuchiScalarConstant = true := by
  native_decide

end HiguchiScreener
end InfraFormalization
