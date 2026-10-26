/-
An integer transport-cost scalar on executable hypergraphs and rule dossiers.

For adjacent `u, v`, `w1IntegerUpper H u v` is the sum of the hop costs `hopCostInt H x y` over `x`
in
the closed neighbourhood of `u` and `y` in the closed neighbourhood of `v`. The per-edge scalar is
`1 − w1IntegerUpper H u v`, and `transportScalarH H` sums it over ordered adjacent pairs. The
product
weight used here is not a coupling of the uniform neighbourhood measures, so these quantities are
not
the Ollivier–Ricci curvature. The module defines the trace of `transportScalarH` along a dossier and
checks its value on `K₃`, the 4-cycle, a single edge and two rule dossiers by `native_decide`.
-/

import InfraFormalization.OllivierRicciExec
import InfraFormalization.RuleSignatureSchema
import InfraFormalization.RuleSignatureExecMetrics

namespace InfraFormalization
namespace OllivierRicciScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open OllivierRicciExec

/-! ## Integer primitives -/

/-- Integer hop cost: `0` if equal, `1` if adjacent, `2` if distinct
non-adjacent. -/
def hopCostInt (H : ExecHG ℕ) (u v : ℕ) : ℕ :=
  if u = v then 0
  else if execAdj H u v then 1
  else 2

/-- Integer membership indicator. -/
def indicatorInt (vs : List ℕ) (v : ℕ) : ℕ :=
  if v ∈ vs then 1 else 0

/-- The sum of `hopCostInt H x y` over `(x, y)` in `cN(u) × cN(v)`, where `cN` is the closed
neighbourhood. -/
def w1IntegerUpper (H : ExecHG ℕ) (u v : ℕ) : ℕ :=
  let carrier := vertexList H
  let cNu := closedNeighbourhood H u
  let cNv := closedNeighbourhood H v
  (carrier.flatMap (fun x =>
    carrier.map (fun y =>
      hopCostInt H x y * indicatorInt cNu x * indicatorInt cNv y))).foldr
    (· + ·) 0

/-- `1 − w1IntegerUpper H u v` for adjacent `u, v`, and 0 otherwise. -/
def transportScalarAdj (H : ExecHG ℕ) (u v : ℕ) : ℤ :=
  if execAdj H u v then 1 - (w1IntegerUpper H u v : ℤ) else 0

/-- The sum of `transportScalarAdj H u v` over ordered pairs of adjacent vertices of `H`. -/
def transportScalarH (H : ExecHG ℕ) : ℤ :=
  let vs := vertexList H
  (vs.flatMap (fun u =>
    vs.filterMap (fun v =>
      if execAdj H u v then some (transportScalarAdj H u v) else none))).foldr
    (· + ·) 0

/-! ## Dossier-level trace + screener -/

/-- The list of `transportScalarH` over the states of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.transportScalarTrace
    (d : Dossier) : List ℤ :=
  d.states.map transportScalarH

/-- `true` when all values of `transportScalarTrace` are equal. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.transportScalarConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.transportScalarTrace

/-! ## Values on small graphs -/

/-- The triangle K₃'s aggregate transport scalar. All 6 directed
edges are adjacent in K₃; each `cN(u) = {1, 2, 3}` (whole vertex
set); `w1IntegerUpper(u, v)` sums all 9 hop-costs over carrier² = 6
(3 diagonal zeros + 6 unit hops). Per-edge scalar = `1 − 6 = −5`;
aggregate over 6 directed adjacent pairs = `−30`. -/
example : transportScalarH OllivierRicciExec.k3 = -30 := by native_decide

/-- The 4-cycle's aggregate transport scalar. For pair `(1, 2)`:
`cN(1) = {1, 2, 4}`, `cN(2) = {1, 2, 3}`; the 9 cross-pair hop-costs
sum to `9`; per-edge scalar = `1 − 9 = −8`. By rotational symmetry
all 8 directed adjacent pairs give `−8`; aggregate = `−64`. -/
example : transportScalarH OllivierRicciExec.cycle4 = -64 := by native_decide

/-- Single edge `{1, 2}`. `cN(1) = cN(2) = {1, 2}`;
`w1IntegerUpper(1, 2)` = sum of hop-costs over `{1,2}² = {(1,1),(1,2),
(2,1),(2,2)}` = `0 + 1 + 1 + 0 = 2`. Per-edge = `1 − 2 = −1`;
aggregate over 2 directed adjacent pairs = `−2`. -/
example : transportScalarH RuleSignatureExecMetrics.edge12 = -2 := by
  native_decide

/-- `transportScalarH` takes different values on `K₃` (−30) and the 4-cycle (−64). -/
example :
    transportScalarH OllivierRicciExec.k3 ≠
    transportScalarH OllivierRicciExec.cycle4 := by native_decide

/-! ## Values on rule dossiers

The traces below are computed for two rules of `RuleSignatureExecCorpus` on `edge12`. -/

/-- For the identity rule on `edge12`, the trace over 2 steps is `[-2, -2, -2]`. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        RuleSignatureExecMetrics.edge12 2).transportScalarTrace
      = [-2, -2, -2] := by
  native_decide

/-- For the edge-append rule on `edge12`, the trace over 2 steps is not constant. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).transportScalarConstant = false := by
  native_decide

end OllivierRicciScreener
end InfraFormalization
