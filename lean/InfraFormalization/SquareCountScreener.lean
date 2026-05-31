/-
**Square-count screener on `ExecHG ℕ`** (#410).

A FIFTH independent curvature scalar alongside Forman (#384),
transport (#402), Higuchi (#405), and degree-variance (#407). The new
scalar counts **4-cycles** (squares) — ordered closed walks
`v₀ → v₁ → v₂ → v₃ → v₀` with all four vertices distinct.

Squares capture *global cycle topology* that the four earlier
scalars miss: Forman / Higuchi / DegVariance are degree-based (local
first-order), Transport is W₁-based (local-neighbourhood), but
4-cycle counting requires reaching across two hops and folding back
— a strictly larger-scope signal.

Counts an *ordered* representative `(v₀, v₁, v₂, v₃)` per square,
so each undirected 4-cycle contributes `8` (= 4 rotations × 2
reflections); the integer scalar is `squareCountOrdered H`,
divisible by `8` for any consistent enumeration.
-/

import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecMetrics
import InfraFormalization.OllivierRicciExec

namespace InfraFormalization
namespace SquareCountScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open OllivierRicciExec

/-- Decidable predicate: `(u, v)` is an undirected edge of `H`. -/
def execHasEdge (H : ExecHG ℕ) (u v : ℕ) : Bool :=
  H.any (fun e => (e.verts == [u, v]) || (e.verts == [v, u]))

/-- **Ordered 4-cycle count** of `H`: number of tuples
`(v₀, v₁, v₂, v₃)` with all four vertices distinct and all four
edges `(v₀,v₁), (v₁,v₂), (v₂,v₃), (v₃,v₀)` present in `H`.
Each undirected 4-cycle contributes `8` to this count
(4 rotations × 2 reflections). -/
def squareCountOrdered (H : ExecHG ℕ) : ℤ :=
  let verts := vertexList H
  let cnt := verts.foldr (fun a accA =>
    accA + verts.foldr (fun b accB =>
      accB + verts.foldr (fun c accC =>
        accC + verts.foldr (fun d accD =>
          if a != b && a != c && a != d
            && b != c && b != d
            && c != d
            && execHasEdge H a b
            && execHasEdge H b c
            && execHasEdge H c d
            && execHasEdge H d a
          then accD + 1
          else accD) 0) 0) 0) 0
  (cnt : ℤ)

/-- The per-state square-count trace of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.squareCountTrace
    (d : Dossier) : List ℤ :=
  d.states.map squareCountOrdered

/-- A candidate's square-count trace is constant along its run. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.squareCountConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.squareCountTrace

/-! ## Concrete cross-checks pin the numerics

The four chosen seeds span the cycle-topology axis: -/

/-- **K₃** (triangle): no 4-cycle (only 3-cycles); count = 0. -/
example : squareCountOrdered OllivierRicciExec.k3 = 0 := by native_decide

/-- **4-cycle**: exactly ONE undirected 4-cycle, ordered count = 8. -/
example : squareCountOrdered OllivierRicciExec.cycle4 = 8 := by native_decide

/-- **Single edge**: too small for any 4-cycle. -/
example : squareCountOrdered RuleSignatureExecMetrics.edge12 = 0 := by native_decide

/-- **3-path** `[{1,2}, {2,3}]`: too few edges. -/
example : squareCountOrdered RuleSignatureExecMetrics.path123 = 0 := by native_decide

/-! ## End-to-end: square count distinguishes runs the four earlier
scalars cannot -/

/-- **Trivial identity on cycle4**: state never changes; trace constant. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        OllivierRicciExec.cycle4 2).squareCountTrace = [8, 8, 8] := by
  native_decide

/-- The constancy verdict for the identity on cycle4: `true`. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        OllivierRicciExec.cycle4 2).squareCountConstant = true := by
  native_decide

end SquareCountScreener
end InfraFormalization
