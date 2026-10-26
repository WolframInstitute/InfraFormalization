/-
Computable Forman-Ricci values on engine states.

This module defines, on `ExecHG ℕ` with carrier `vertexList H`, adjacency,
adjacency degree, triangle counts through a pair, the triangle-corrected
Forman-Ricci value `4 − deg u − deg v + 3·#triangles(u,v)` of a pair, and
its sum over ordered adjacent pairs. The arithmetic is that of
`Hypergraph.formanRicciEdgeTriangle` and
`Hypergraph.formanRicciTriangleDoubled`, with the sum over `vertexList H`
in place of `Finset.univ`; no theorem relates the two. It also defines
traces and tests on dossiers. Values on fixed graphs and runs are checked
by `decide` or `native_decide`.
-/

import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecCorpus

namespace InfraFormalization
namespace RuleSignatureExecMetrics

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecCorpus

/-! ## Adjacency and degree -/

/-- `u ≠ v` and some hyperedge of `H` contains both `u` and `v`. -/
def execAdj (H : ExecHG ℕ) (u v : ℕ) : Bool :=
  (u != v) && H.any (fun e => e.verts.contains u && e.verts.contains v)

/-- The number of vertices of `H` adjacent to `v`. -/
def execAdjDegree (H : ExecHG ℕ) (v : ℕ) : ℕ :=
  ((vertexList H).filter (fun u => execAdj H v u)).length

/-- The number of vertices of `H` adjacent to both `u` and `v`. -/
def execTriangles (H : ExecHG ℕ) (u v : ℕ) : ℕ :=
  ((vertexList H).filter (fun x => execAdj H u x && execAdj H v x)).length

/-! ## Triangle-corrected Forman-Ricci values -/

/-- `4 − deg u − deg v + 3·#triangles(u,v)`. -/
def execFormanEdge (H : ExecHG ℕ) (u v : ℕ) : ℤ :=
  4 - (execAdjDegree H u : ℤ) - (execAdjDegree H v : ℤ)
    + 3 * (execTriangles H u v : ℤ)

/-- The sum of `execFormanEdge H u v` over ordered adjacent pairs
`(u, v)` of vertices of `H`; each undirected edge is counted twice. -/
def execFormanScalar (H : ExecHG ℕ) : ℤ :=
  let vs := vertexList H
  vs.foldr (fun u acc =>
    acc + (vs.filter (fun v => execAdj H u v)).foldr
      (fun v acc2 => acc2 + execFormanEdge H u v) 0) 0

/-! ## Dossier traces -/

/-- The list of `execFormanScalar` values of the states of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarTrace
    (d : Dossier) : List ℤ :=
  d.states.map execFormanScalar

/-- The edge-count, vertex-count and Forman-scalar traces of a dossier. -/
structure SignatureVerdict where
  edgeCounts    : List Nat
  vertexCounts  : List Nat
  formanScalars : List ℤ
deriving DecidableEq, Repr

/-- The three traces of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.signatureVerdict
    (d : Dossier) : SignatureVerdict :=
  ⟨d.edgeCountTrace, d.vertexCountTrace, d.formanScalarTrace⟩

/-! ## Tests on traces -/

/-- Every entry of the list equals its first entry. -/
def allEqHead : List ℤ → Bool
  | [] => true
  | x :: xs => xs.all (· == x)

/-- The Forman-scalar trace is constant. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarConstant
    (d : Dossier) : Bool :=
  allEqHead d.formanScalarTrace

/-- The last entry of the Forman-scalar trace equals `tgt`. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarReaches
    (d : Dossier) (tgt : ℤ) : Bool :=
  match d.formanScalarTrace.getLast? with
  | some x => x == tgt
  | none   => false

/-- No entry of the Forman-scalar trace equals `tgt`. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarPersistentGap
    (d : Dossier) (tgt : ℤ) : Bool :=
  d.formanScalarTrace.all (· != tgt)

/-! ## Values on fixed graphs -/

/-- A single edge `{1,2}`. -/
def edge12 : ExecHG ℕ := [⟨[1, 2], by decide⟩]

/-- Path `1 — 2 — 3`. -/
def path123 : ExecHG ℕ := [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩]

/-- Triangle `K₃` on `{1,2,3}`. -/
def triangleK3 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[1, 3], by decide⟩]

/-- 4-cycle `1—2—3—4—1`. -/
def cycle4 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩,
   ⟨[3, 4], by decide⟩, ⟨[1, 4], by decide⟩]

/-- Single edge: each ordered pair has value `4 − 1 − 1 = 2`; the sum over
two ordered pairs is 4. -/
example : execFormanScalar edge12 = 4 := by decide

/-- Path `1—2—3`: each edge has value 1; the sum over four ordered pairs
is 4. -/
example : execFormanScalar path123 = 4 := by decide

/-- `K₃`: each edge has value `4 − 2 − 2 + 3 = 3`; the sum over six ordered
pairs is 18. -/
example : execFormanScalar triangleK3 = 18 := by decide

/-- 4-cycle: each edge has value `4 − 2 − 2 = 0`; the sum is 0. -/
example : execFormanScalar cycle4 = 0 := by decide

/-- The values on `K₃` and on the 4-cycle differ. -/
example : execFormanScalar triangleK3 ≠ execFormanScalar cycle4 := by decide

/-! ## Runs -/

/-- The dossier of the edge-append rule `{a,b} → {a,b},{b,c}` (`c` fresh)
for 3 steps from a single edge. -/
def appendDossier3 : Dossier :=
  canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule edge12 3

/-- Edge counts `[1, 2, 4, 8]`, vertex counts `[2, 3, 5, 9]` and Forman
scalars `[4, 4, 0, -12]`. -/
example : appendDossier3.signatureVerdict =
    ⟨[1, 2, 4, 8], [2, 3, 5, 9], [4, 4, 0, -12]⟩ := by native_decide

/-- The Forman-scalar trace of `appendDossier3` is not constant. -/
example : appendDossier3.formanScalarConstant = false := by native_decide

/-- No entry of the Forman-scalar trace of `appendDossier3` equals 18. -/
example : appendDossier3.formanScalarPersistentGap 18 = true := by native_decide

/-- The dossier of the identity rule for 2 steps from the 4-cycle. -/
def cycle4IdDossier2 : Dossier :=
  canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule cycle4 2

example : cycle4IdDossier2.signatureVerdict.formanScalars = [0, 0, 0] := by
  native_decide

example : cycle4IdDossier2.formanScalarConstant = true := by native_decide

example : cycle4IdDossier2.formanScalarReaches 0 = true := by native_decide

end RuleSignatureExecMetrics
end InfraFormalization
