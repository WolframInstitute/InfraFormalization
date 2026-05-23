/-
**ExecHG-native signature metrics** (#384).

Computable curvature/conservation metrics defined *directly* on the
executable engine's states (`ExecHG ℕ = List (Hyperedge ℕ)`), via
`vertexList`, with no detour through the abstract `[Fintype V]`
`Hypergraph` machinery and no `Trajectory` reconstruction.

**Why this exists.** Two project goals converge here.

  1. *Rule search using Lean alone.* A candidate rule's run
     (`canonicalDossier` / `singleWayEvolve`) is a `List (ExecHG ℕ)`.
     To screen it we need a signature value per state that is
     `decide`/`native_decide`-computable. The abstract Forman-Ricci
     definitions (`Hypergraph.formanRicciTriangleDoubled`) require a
     `Fintype` carrier and are not directly runnable on the ℕ-vertex
     engine states. The defs below close that gap: they recompute the
     *same arithmetic* on the finite carrier `vertexList H`.

  2. *Metric set to port to the fast engine.* RASSAR's
     `HypergraphRewritingEngine` paclet is the at-scale search
     accelerator (#190/#375). The combinatorial primitives below —
     `execAdj`, `execAdjDegree`, `execTriangles`, `execFormanEdge`,
     and their `execFormanScalar` reduction — are precisely the metric
     set that engine needs to compute per state to run curvature-screened
     rule search. This file is the machine-checked *specification* of
     those primitives: each is a total `decide`-able function, and the
     concrete cross-checks (`K3 = 18`, flat 4-cycle `= 0`, …) pin the
     intended numerics for the port.

**Soundness anchor.** `execFormanEdge H u v` is, by construction, the
identical expression to `Hypergraph.formanRicciEdgeTriangle` (4 − deg u
− deg w + 3·#triangles), and `execFormanScalar` mirrors
`Hypergraph.formanRicciTriangleDoubled` (sum over ordered adjacent
pairs). The only difference is the carrier: the abstract version sums
over `Finset.univ`, the executable version over `vertexList H`. The
cross-checks below verify the executable numerics on graphs whose
abstract Forman scalar is hand-computable.
-/

import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecCorpus

namespace InfraFormalization
namespace RuleSignatureExecMetrics

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecCorpus

/-! ## Executable adjacency and degree -/

/-- Executable adjacency on `ExecHG ℕ`: `u` and `v` are adjacent when
they are distinct and co-occur in some hyperedge. This is the
order-blind 1-skeleton relation; it is the executable counterpart of
`Hypergraph.Adj`. Fully `decide`-computable. -/
def execAdj (H : ExecHG ℕ) (u v : ℕ) : Bool :=
  (u != v) && H.any (fun e => e.verts.contains u && e.verts.contains v)

/-- Executable adjacency degree of `v`: number of distinct vertices of
`H` adjacent to `v`. Counterpart of `Hypergraph.adjDegree`. -/
def execAdjDegree (H : ExecHG ℕ) (v : ℕ) : ℕ :=
  ((vertexList H).filter (fun u => execAdj H v u)).length

/-- Executable triangle count through the (unordered) pair `{u, v}`:
number of distinct vertices adjacent to both. Counterpart of
`Hypergraph.trianglesThroughEdge`. -/
def execTriangles (H : ExecHG ℕ) (u v : ℕ) : ℕ :=
  ((vertexList H).filter (fun x => execAdj H u x && execAdj H v x)).length

/-! ## Triangle-corrected Forman-Ricci on the executable side -/

/-- Triangle-corrected 1-D Forman-Ricci curvature of the edge `{u, v}`:
`F(u,v) = 4 − deg u − deg v + 3·#triangles(u,v)`. Identical arithmetic
to `Hypergraph.formanRicciEdgeTriangle`, on the carrier `vertexList H`. -/
def execFormanEdge (H : ExecHG ℕ) (u v : ℕ) : ℤ :=
  4 - (execAdjDegree H u : ℤ) - (execAdjDegree H v : ℤ)
    + 3 * (execTriangles H u v : ℤ)

/-- Doubled Forman scalar: sum of `execFormanEdge H u v` over every
*ordered* adjacent pair `(u, v)` with `u, v ∈ vertexList H`. Each
undirected edge is counted twice, exactly as
`Hypergraph.formanRicciTriangleDoubled`. -/
def execFormanScalar (H : ExecHG ℕ) : ℤ :=
  let vs := vertexList H
  vs.foldr (fun u acc =>
    acc + (vs.filter (fun v => execAdj H u v)).foldr
      (fun v acc2 => acc2 + execFormanEdge H u v) 0) 0

/-! ## Dossier-level signature traces -/

/-- The Forman-scalar trace of a dossier: one value per recorded state. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarTrace
    (d : Dossier) : List ℤ :=
  d.states.map execFormanScalar

/-- A `decide`-checkable bundle of the three first-class signature
traces of a dossier. This record is the metric vector a rule-search
loop reads per candidate, and the precise per-state output spec for the
`HypergraphRewritingEngine` port: edge count, vertex count, and
triangle-corrected Forman scalar. -/
structure SignatureVerdict where
  edgeCounts    : List Nat
  vertexCounts  : List Nat
  formanScalars : List ℤ
deriving DecidableEq, Repr

/-- Assemble the full signature verdict of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.signatureVerdict
    (d : Dossier) : SignatureVerdict :=
  ⟨d.edgeCountTrace, d.vertexCountTrace, d.formanScalarTrace⟩

/-! ## Screener predicates (Lean-alone search verdicts)

These give a candidate rule a `decide`-checkable pass/fail directly
from its executable run, with no abstract `Trajectory`. -/

/-- Every entry of a list equals its head (constancy test). -/
def allEqHead : List ℤ → Bool
  | [] => true
  | x :: xs => xs.all (· == x)

/-- **Conservative pass.** The Forman scalar is constant along the run:
the candidate rule preserves macroscopic curvature on this seed. A
flat-target screen passes iff this holds with head value `0`. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarConstant
    (d : Dossier) : Bool :=
  allEqHead d.formanScalarTrace

/-- **Target-reach (positive) verdict.** The final recorded state has
Forman scalar equal to `tgt`. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarReaches
    (d : Dossier) (tgt : ℤ) : Bool :=
  match d.formanScalarTrace.getLast? with
  | some x => x == tgt
  | none   => false

/-- **Persistent-gap (negative) verdict.** *No* recorded state attains
`tgt`. This is the executable analogue of the abstract screener's
persistent-gap negative discharge: a rule that never reaches the target
curvature on a seed is rejected for that seed. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.formanScalarPersistentGap
    (d : Dossier) (tgt : ℤ) : Bool :=
  d.formanScalarTrace.all (· != tgt)

/-! ## Concrete cross-checks (pin the engine-port numerics)

Each graph below has a hand-computable triangle-Forman scalar; the
`decide` checks fix the intended numerics the fast engine must
reproduce. -/

/-- A single edge `{1,2}`. -/
def edge12 : ExecHG ℕ := [⟨[1, 2], by decide⟩]

/-- Path `1 — 2 — 3`. -/
def path123 : ExecHG ℕ := [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩]

/-- Triangle `K₃` on `{1,2,3}`. -/
def triangleK3 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[1, 3], by decide⟩]

/-- 4-cycle `1—2—3—4—1` (flat: every edge has Forman curvature 0). -/
def cycle4 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩,
   ⟨[3, 4], by decide⟩, ⟨[1, 4], by decide⟩]

/-- Single edge: both endpoints degree 1, no triangles,
`F = 4 − 1 − 1 = 2`; doubled over the two ordered pairs `= 4`. -/
example : execFormanScalar edge12 = 4 := by decide

/-- Path `1—2—3`: `F(1,2) = F(2,3) = 1`; doubled over four ordered
pairs `= 4`. -/
example : execFormanScalar path123 = 4 := by decide

/-- Triangle `K₃`: each edge `F = 4 − 2 − 2 + 3·1 = 3`; six ordered
pairs `= 18`. The triangle correction is what makes this strictly
positive (curved), separating `K₃` from a 3-path. -/
example : execFormanScalar triangleK3 = 18 := by decide

/-- 4-cycle: each vertex degree 2, no triangles, `F = 4 − 2 − 2 = 0`;
the whole scalar vanishes — a flat signature. -/
example : execFormanScalar cycle4 = 0 := by decide

/-- The triangle correction strictly separates `K₃` (curved) from the
flat 4-cycle, on the executable side. -/
example : execFormanScalar triangleK3 ≠ execFormanScalar cycle4 := by decide

/-! ## End-to-end: a candidate run yields a Lean-alone verdict

The edge-doubling rule on the path seed, screened entirely from its
executable dossier. -/

/-- Edge-append canonical dossier, 3 steps, from a single edge
(`{a,b} → {a,b},{b,c}`, `c` fresh — branching extension, no duplicate
edges, so the per-binding match enumeration is exact). -/
def appendDossier3 : Dossier :=
  canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule edge12 3

/-- The full signature verdict, computed from the run alone — the exact
triple `(edgeCounts, vertexCounts, formanScalars)` the fast engine must
emit per candidate. Edge count `[1,2,4,8]` and vertex count
`[2,3,5,9]`; the Forman scalar `[4, 4, 0, -12]` turns **negative**, the
tree-like / hyperbolic signature of an unboundedly branching append
rule. This is exactly the kind of negative verdict a curvature screen
uses to *reject* a candidate aiming at a flat or positively-curved
target. -/
example : appendDossier3.signatureVerdict =
    ⟨[1, 2, 4, 8], [2, 3, 5, 9], [4, 4, 0, -12]⟩ := by native_decide

/-- The append rule fails a flat-target (Forman ≡ 0) screen on this
seed: its Forman scalar is non-constant. -/
example : appendDossier3.formanScalarConstant = false := by native_decide

/-- It also fails a positive-curvature target `+18` (the `K₃` value):
no state along the run ever attains it — a `decide`-checked negative
discharge. -/
example : appendDossier3.formanScalarPersistentGap 18 = true := by native_decide

/-- Flat seed stays flat: the 4-cycle has a constant (zero) Forman
scalar under the identity rule, so the conservative flat-target screen
passes Lean-internally. -/
def cycle4IdDossier2 : Dossier :=
  canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule cycle4 2

example : cycle4IdDossier2.signatureVerdict.formanScalars = [0, 0, 0] := by
  native_decide

example : cycle4IdDossier2.formanScalarConstant = true := by native_decide

example : cycle4IdDossier2.formanScalarReaches 0 = true := by native_decide

end RuleSignatureExecMetrics
end InfraFormalization
