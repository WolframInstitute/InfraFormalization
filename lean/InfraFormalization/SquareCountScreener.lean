/-
Ordered 4-cycle counts of `ExecHG ℕ` states.

This module defines `squareCountOrdered H`, the number of tuples
`(v₀, v₁, v₂, v₃)` of distinct vertices with all four edges
`(v₀,v₁), (v₁,v₂), (v₂,v₃), (v₃,v₀)` present as binary hyperedges, and the
per-state trace and constancy test of a dossier. Values on K₃, the
4-cycle, a single edge, a 2-edge path and the identity rule on the 4-cycle
are checked by `native_decide`.
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

/-- `H` contains the hyperedge `[u, v]` or `[v, u]`. -/
def execHasEdge (H : ExecHG ℕ) (u v : ℕ) : Bool :=
  H.any (fun e => (e.verts == [u, v]) || (e.verts == [v, u]))

/-- The number of tuples `(v₀, v₁, v₂, v₃)` of distinct vertices of `H` with
`execHasEdge` true on `(v₀,v₁), (v₁,v₂), (v₂,v₃), (v₃,v₀)`. Each undirected
4-cycle gives 8 such tuples. -/
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

/-- The list of `squareCountOrdered` values of the states of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.squareCountTrace
    (d : Dossier) : List ℤ :=
  d.states.map squareCountOrdered

/-- All entries of the square-count trace equal its first entry. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.squareCountConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.squareCountTrace

/-! ## Values on fixed states, checked by `native_decide` -/

/-- K₃: count 0. -/
example : squareCountOrdered OllivierRicciExec.k3 = 0 := by native_decide

/-- The 4-cycle: count 8. -/
example : squareCountOrdered OllivierRicciExec.cycle4 = 8 := by native_decide

/-- A single edge: count 0. -/
example : squareCountOrdered RuleSignatureExecMetrics.edge12 = 0 := by native_decide

/-- The path `[{1,2}, {2,3}]`: count 0. -/
example : squareCountOrdered RuleSignatureExecMetrics.path123 = 0 := by native_decide

/-! ## The identity rule on the 4-cycle -/

/-- The identity rule on the 4-cycle for 2 steps gives the trace
`[8, 8, 8]`. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        OllivierRicciExec.cycle4 2).squareCountTrace = [8, 8, 8] := by
  native_decide

/-- The square-count trace of the identity rule on the 4-cycle is
constant. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        OllivierRicciExec.cycle4 2).squareCountConstant = true := by
  native_decide

end SquareCountScreener
end InfraFormalization
