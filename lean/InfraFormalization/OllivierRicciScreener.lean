/-
**Ollivier-Ricci-style screener on ExecHG dossiers** (#402).

Builds on `OllivierRicciExec.lean` (#401) to provide a `decide`-
checkable, integer-valued **transport-cost scalar** per state — a
coarse Ollivier-Ricci-style discriminator that:

  * sums the pairwise hop costs between vertex closed
    neighbourhoods (the `productCoupling`-style transport cost);
  * gives a per-edge "transport scalar" `1 − W₁_int_upper`;
  * aggregates over directed adjacent pairs in `H` to a per-state
    integer scalar.

**Honest framing.** This is NOT the true Ollivier-Ricci κ(u, v),
because the unnormalised `productCoupling` is not a valid coupling of
the two uniform measures (it doesn't respect the marginals). It IS a
concrete, integer-valued graph invariant that captures "how far apart
the two vertex neighbourhoods are in pairwise hop cost." It's a real
*discriminator* for rule search — distinct rule outputs give distinct
scalars — and it sits in the same `SignatureVerdict`-shape as the
triangle-Forman screener from #384. The true LP-optimal W₁ (and thus
the genuine Ollivier-Ricci κ) requires the `w1InfimumOver` machinery
with a carefully-chosen candidate-coupling set, which is staged
separately.

The integer form keeps `decide`/`native_decide` usable — paralleling
the triangle-Forman scalar of #384.
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

/-- **Integer W₁ upper bound** between two vertex-neighbourhood
uniform measures via the unscaled product coupling: sum over
`carrier × carrier` of `hopCost(x, y) · 𝟙(x ∈ cN(u)) · 𝟙(y ∈ cN(v))`.
Equivalently, sum of `hopCost(x, y)` over `(x, y) ∈ cN(u) × cN(v)`. -/
def w1IntegerUpper (H : ExecHG ℕ) (u v : ℕ) : ℕ :=
  let carrier := vertexList H
  let cNu := closedNeighbourhood H u
  let cNv := closedNeighbourhood H v
  (carrier.flatMap (fun x =>
    carrier.map (fun y =>
      hopCostInt H x y * indicatorInt cNu x * indicatorInt cNv y))).foldr
    (· + ·) 0

/-- **Per-edge transport scalar** for adjacent `(u, v)`:
`1 − W₁_int_upper`. For non-adjacent or equal vertices, returns `0`. -/
def transportScalarAdj (H : ExecHG ℕ) (u v : ℕ) : ℤ :=
  if execAdj H u v then 1 - (w1IntegerUpper H u v : ℤ) else 0

/-- **Aggregate transport scalar** of `H`: sum of `transportScalarAdj`
over directed pairs `(u, v)` in `vertexList H × vertexList H` that are
adjacent. -/
def transportScalarH (H : ExecHG ℕ) : ℤ :=
  let vs := vertexList H
  (vs.flatMap (fun u =>
    vs.filterMap (fun v =>
      if execAdj H u v then some (transportScalarAdj H u v) else none))).foldr
    (· + ·) 0

/-! ## Dossier-level trace + screener -/

/-- The per-state transport-scalar trace of a dossier. -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.transportScalarTrace
    (d : Dossier) : List ℤ :=
  d.states.map transportScalarH

/-- A candidate rule's transport scalar is constant along its run on
this seed (analogue of `formanScalarConstant`). -/
def _root_.InfraFormalization.RuleSignatureSchema.Dossier.transportScalarConstant
    (d : Dossier) : Bool :=
  RuleSignatureExecMetrics.allEqHead d.transportScalarTrace

/-! ## Concrete cross-checks pin the numerics

These pin the integer-arithmetic values across small graphs so the
engine port (and any reader) knows exactly what the screener
computes. -/

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

/-- **K₃ vs C₄: the screener distinguishes them strongly.** `−30` vs
`−64` — the 4-cycle has further-apart neighbourhood pairs (Hamming-style)
than the triangle. -/
example :
    transportScalarH OllivierRicciExec.k3 ≠
    transportScalarH OllivierRicciExec.cycle4 := by native_decide

/-! ## Integration with rule-search dossiers

`witnessRule0` from #392's rate-(0, 12) selection, run on `edge12`,
yields a `transportScalarTrace` whose `decide`-checkable values can
be compared against the existing Forman trace. Two parallel
discriminators for the same candidate. -/

/-- Trivial identity rule on `edge12` at 2 steps — the trace is
constant at `−2` (state never changes, so the aggregate scalar
doesn't change). -/
example :
    (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
        RuleSignatureExecMetrics.edge12 2).transportScalarTrace
      = [-2, -2, -2] := by
  native_decide

/-- Edge-append rule on `edge12` at 2 steps — the transport scalar
trace evolves as the graph branches; the rule is NOT constant on
this scalar. -/
example :
    (canonicalDossier RuleSignatureExecCorpus.edgeAppendExecRule
        RuleSignatureExecMetrics.edge12 2).transportScalarConstant = false := by
  native_decide

end OllivierRicciScreener
end InfraFormalization
