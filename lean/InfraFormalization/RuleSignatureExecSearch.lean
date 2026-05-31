/-
**Lean-alone rule search driver** (#385).

A computable, `decide`/`native_decide`-checkable rule-search loop built
on top of the #384 ExecHG-native screener. This is the first concrete
instance of *"rule search using Lean alone"*:

  1. **Generate** a bounded family of candidate `ExecRule`s.
  2. **Run** each candidate with the Lean executor (`canonicalDossier`).
  3. **Classify** the run by its triangle-Forman scalar trace into a
     coarse `CurvatureTrend`.
  4. **Select** the candidates matching a target trend — a certified
     search result.

The bounded family searched here: single-edge LHS `{0,1}`, RHS any
nonempty subset (size ≤ `maxRHS`) of the ordered vertex pairs over
`Fin 3` (two bound vertices `0,1` plus one fresh vertex `2`). This is a
small but genuine open enumeration — the rules are *generated*, not
hand-listed, and the screener is what tells flat from curved.

The point for the wider programme: the curvature trend that
distinguishes candidates is computed by exactly the
`RuleSignatureExecMetrics` formulas, so the same discriminator is what
must be ported into the fast `HypergraphRewritingEngine` to run this
search at scale.
-/

import InfraFormalization.RuleSignatureExecMetrics

namespace InfraFormalization
namespace RuleSignatureExecSearch

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecCorpus
open RuleSignatureExecMetrics

/-! ## Coarse curvature classification of a run -/

/-- A coarse finite-horizon curvature trend extracted from a
Forman-scalar trace: `flat` (constant), or the sign of the final
recorded scalar. -/
inductive CurvatureTrend
  | flat | positive | negative | zero
deriving DecidableEq, Repr

/-- Classify a Forman-scalar trace. Constant ⇒ `flat`; otherwise the
sign of the final state's scalar (the finite-horizon limiting trend). -/
def classifyForman (trace : List ℤ) : CurvatureTrend :=
  if allEqHead trace then CurvatureTrend.flat
  else match trace.getLast? with
    | some x => if x > 0 then CurvatureTrend.positive
                else if x < 0 then CurvatureTrend.negative
                else CurvatureTrend.zero
    | none => CurvatureTrend.flat

/-- Run a candidate rule with the Lean executor and read off its
curvature trend. -/
def trendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) : CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).formanScalarTrace)

/-! ## Bounded rule generator -/

/-- A 2-vertex hyperedge `[i, j]` over `Fin p`. -/
def mkEdgeFin {p : Nat} (i j : Fin p) : Hyperedge (Fin p) :=
  ⟨[i, j], List.cons_ne_nil i [j]⟩

/-- All ordered pairs `[i, j]` with `i ≠ j` over `Fin p`. -/
def allOrderedPairsFin (p : Nat) : List (Hyperedge (Fin p)) :=
  (List.finRange p).flatMap (fun i =>
    (List.finRange p).filterMap (fun j =>
      if i = j then none else some (mkEdgeFin i j)))

/-- The candidate family: single-edge LHS `{0,1}` over the two bound
vertices, RHS any nonempty subset (size ≤ `maxRHS`) of the ordered
pairs over `Fin 3` (= 2 bound + 1 fresh). -/
def enumerateRules2_1 (maxRHS : Nat) : List ExecRule :=
  let edges := allOrderedPairsFin 3
  let lhsE : ExecHG (Fin 2) := [mkEdgeFin 0 1]
  (edges.sublists.filter (fun s => !s.isEmpty && decide (s.length ≤ maxRHS))).map
    (fun s => { numBound := 2, numFresh := 1, lhs := lhsE, rhs := s })

/-! ## Search results (certified)

Each candidate is run on the single-edge seed `edge12 = [{1,2}]` for two
steps. -/

/-- The two-edge-RHS candidate family has 21 members:
`C(6,1) + C(6,2) = 6 + 15`. -/
example : (enumerateRules2_1 2).length = 21 := by decide

/-! ## Select-by-trend filter -/

/-- The search-selection primitive: keep the candidates whose run lands
in the target curvature trend. -/
def selectByTrend (cands : List ExecRule) (seed : ExecHG ℕ) (n : Nat)
    (tgt : CurvatureTrend) : List ExecRule :=
  cands.filter (fun r => decide (trendOf r seed n = tgt))

/-! ### Certified search distribution

Running the whole family on the single-edge seed `edge12 = [{1,2}]` for
two steps and partitioning by curvature trend: the screener separates
the 21 candidates into 13 flat, 4 zero-but-non-constant, 2 negatively
curved (tree-like / hyperbolic) and 2 positively curved. Every count is
`native_decide`-certified; together they show the screener is a genuine
discriminator, not a trivial pass-through. -/

/-- **Flat selection: 13 candidates.** -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.flat).length = 13 := by
  native_decide

/-- **Zero-but-non-constant selection: 4 candidates.** -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.zero).length = 4 := by
  native_decide

/-- **Negatively-curved (tree-like / hyperbolic) selection: 2 candidates** —
a certified "search found rules with hyperbolic signatures" result. -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.negative).length = 2 := by
  native_decide

/-- **Positively-curved selection: 2 candidates.** -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.positive).length = 2 := by
  native_decide

/-- The four selections partition the whole family (`13 + 4 + 2 + 2 = 21`):
the trend classification is total on the candidate set. -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.flat).length
    + (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.zero).length
    + (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.negative).length
    + (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.positive).length
      = (enumerateRules2_1 2).length := by
  native_decide

/-! ## Multi-seed stability filter (#386)

A rule's curvature class should be a property of the rule, not of a
particular seed. The single-seed classification above can over-accept:
a rule may register `negative` on one seed by coincidence while
producing a flat trace on another. To filter such pseudo-passes, run
every candidate across a topologically diverse seed set and demand the
trend agrees on all seeds. Only candidates that pass the stability
filter have a well-defined rule-level curvature signature on this
family. -/

/-- A small topologically diverse seed set: a single edge (`edge12`),
a simple path (`path123`), and a 4-cycle (`cycle4`). Three distinct
1-skeleton shapes, none containing a triangle. -/
def seedSet : List (ExecHG ℕ) := [edge12, path123, cycle4]

/-- The list of curvature trends a candidate produces across a seed
set. -/
def trendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ)) (n : Nat) :
    List CurvatureTrend :=
  seeds.map (fun s => trendOf r s n)

/-- A candidate stably exhibits the target trend iff every seed in the
set lands at `tgt`. -/
def isStablyTrend (r : ExecRule) (seeds : List (ExecHG ℕ)) (n : Nat)
    (tgt : CurvatureTrend) : Bool :=
  (trendsAcross r seeds n).all (fun t => decide (t = tgt))

/-- A candidate is *stably classifiable* iff every seed produces the
same trend (without specifying which). -/
def stablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match trendsAcross r seeds n with
  | [] => true
  | t :: rest => rest.all (fun t' => decide (t' = t))

/-- The stable-select primitive: keep only candidates whose run is
trend-`tgt` on every seed in `seeds`. -/
def stableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : CurvatureTrend) : List ExecRule :=
  cands.filter (fun r => isStablyTrend r seeds n tgt)

/-! ### Certified stability distribution

Over `seedSet = [edge12, path123, cycle4]` at 2 steps, partitioning the
21 candidates by stable trend (and the seed-dependent remainder). -/

/-- **Stably flat: 7 candidates** — every seed in `seedSet` yields a
constant Forman scalar. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.flat).length = 7 := by
  native_decide

/-- **Stably negative (tree-like / hyperbolic on every seed):
2 candidates** — the genuine seed-independent hyperbolic rules of this
family. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.negative).length = 2 := by
  native_decide

/-- **Stably positive: 2 candidates** — the genuine seed-independent
positively-curved rules of this family. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.positive).length = 2 := by
  native_decide

/-- **Stably zero: 0 candidates.** -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.zero).length = 0 := by
  native_decide

/-- **Total stably classifiable: 11 candidates** — every seed agrees
on the trend. The remaining `21 − 11 = 10` candidates are seed-dependent
and have no rule-level curvature class on this family; they are not
admissible for a curvature-target search. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- The four stable selections sum to the total stably-classifiable
count (`7 + 2 + 2 + 0 = 11`) — the stable classification partitions
the stably-classifiable subset. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.flat).length
    + (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.negative).length
    + (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.positive).length
    + (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.zero).length
      = ((enumerateRules2_1 2).filter
          (fun r => stablyClassifiable r seedSet 2)).length := by
  native_decide

/-- **Seed-dependent (rejected) count: 10 candidates** — these rules
land on different trends for different seeds and so have no rule-level
curvature signature. The stability filter is doing genuine work: it
rejects nearly half the single-seed pass rate. -/
example :
    (enumerateRules2_1 2).length
      - ((enumerateRules2_1 2).filter
          (fun r => stablyClassifiable r seedSet 2)).length = 10 := by
  native_decide

/-! ### Enlarged family: `maxRHS = 3` (single-edge LHS, RHS size ≤ 3)

Growing the family from 21 candidates (`maxRHS = 2`) to substantially
more by allowing RHS up to 3 edges. New certified distribution data
on the larger family. -/

/-- The enlarged 3-edge-RHS candidate family. `C(6, 1) + C(6, 2) +
C(6, 3) = 6 + 15 + 20 = 41`. -/
example : (enumerateRules2_1 3).length = 41 := by decide

/-- **The enlarged 3-edge-RHS family has 41 candidates** (almost
double the 21 at `maxRHS = 2`). -/
example : (enumerateRules2_1 3).length = 41 := by decide

/-! ### Certified stability distribution on the 41-candidate family

At one engine step (`n = 1`) across the `seedSet`. Larger family →
more nuanced distribution. -/

/-- **Stably classifiable: 19 candidates** — almost half (19/41) of
the enlarged family have a seed-independent curvature class at `n = 1`. -/
example :
    ((enumerateRules2_1 3).filter
        (fun r => stablyClassifiable r seedSet 1)).length = 19 := by
  native_decide

/-- **Stably flat: 11 candidates** at `n = 1`. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.flat).length = 11 := by
  native_decide

/-- **Stably positive: 8 candidates** at `n = 1` — the enlarged family
exposes more curved candidates than the small one. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.positive).length = 8 := by
  native_decide

/-- **Stably negative: 0 candidates** at `n = 1` — short traces don't
yet show the hyperbolic signature on every seed (it emerges at higher
`n` as branching accumulates). -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.negative).length = 0 := by
  native_decide

/-- **Stably zero (non-constant): 0 candidates** at `n = 1`. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.zero).length = 0 := by
  native_decide

/-- **Seed-dependent (rejected) count: 22 candidates** — over half the
enlarged family. Confirms the stability filter does substantial work
at scale. -/
example :
    (enumerateRules2_1 3).length
      - ((enumerateRules2_1 3).filter
          (fun r => stablyClassifiable r seedSet 1)).length = 22 := by
  native_decide

/-- The four stable selections sum to the stably-classifiable total
(`11 + 8 + 0 + 0 = 19`). -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.flat).length
    + (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.negative).length
    + (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.positive).length
    + (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.zero).length
      = ((enumerateRules2_1 3).filter
          (fun r => stablyClassifiable r seedSet 1)).length := by
  native_decide

/-! ## Rate-based, target-aware screener (#391)

The coarse trend classification (flat / positive / negative / zero)
loses quantitative information. This section adds a `decide`-checkable
*rate-bound* predicate on the Forman-scalar trace, parallel to the
abstract `ConvergenceRateObligation` in `RuleSignatureScreener`:

  `|trace[i] − tgt| · (i + 1) ≤ C`  for every recorded state `i`.

Equivalently, `|Forman(state_i) − tgt| ≤ C / (i+1)` — the canonical
finite-horizon `O(1/n)` rate at the integer-arithmetic level. This is
the shape of obligation that ultimately feeds
`HypergraphMetricOriginObligationStrong`. -/

/-- Per-state rate check, threading the index. -/
def rateBoundedAux : Nat → List ℤ → ℤ → ℕ → Bool
  | _, [], _, _ => true
  | i, x :: xs, tgt, c =>
    decide ((x - tgt).natAbs * (i + 1) ≤ c) && rateBoundedAux (i + 1) xs tgt c

/-- `rateBounded trace tgt c = true` iff `|trace[i] − tgt| · (i + 1) ≤ c`
for every `i`. The canonical integer-arithmetic encoding of an
`O(1/n)`-rate convergence-to-target on a finite trace. -/
def rateBounded (trace : List ℤ) (tgt : ℤ) (c : ℕ) : Bool :=
  rateBoundedAux 0 trace tgt c

/-- A dossier converges to target Forman scalar `tgt` at rate `C` iff
its Forman-scalar trace satisfies the rate bound. -/
def dossierConvergesToAt (d : Dossier) (tgt : ℤ) (c : ℕ) : Bool :=
  rateBounded d.formanScalarTrace tgt c

/-- A candidate rule stably converges to `tgt` at rate `c` iff every
seed in `seeds` produces a run satisfying the rate bound. -/
def stablyConvergesToAt (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : ℤ) (c : ℕ) : Bool :=
  seeds.all (fun s => dossierConvergesToAt (canonicalDossier r s n) tgt c)

/-- The rate-screener selection: candidates whose every-seed run lies
within the `(tgt, c)` rate envelope. -/
def stableRateSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : ℤ) (c : ℕ) : List ExecRule :=
  cands.filter (fun r => stablyConvergesToAt r seeds n tgt c)

/-! ### Discovery via `#eval` of pass-counts at several `(tgt, c)`.

The four targets exercise the spectrum: exact zero (`tgt=0, c=0`),
zero with slack (`tgt=0, c=12`), exact `4` (the single-edge / path-123
Forman value), and a generous envelope around `4`. -/

/-! ### Certified rate-screener distribution -/

/-- **No rule has exact zero Forman scalar on every state across every
seed** (`tgt = 0, c = 0`). -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 0).length = 0 := by
  native_decide

/-- **At the canonical envelope `c = 12` (= max-`|x|`·(max-index+1) for
the stably-flat traces), the rate-(0, 12) selection has 7 candidates.**
This matches the stably-flat count exactly. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 12).length = 7 := by
  native_decide

/-- **Loosening to `c = 36` picks up 9 candidates** — 2 more than the
canonical envelope. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 36).length = 9 := by
  native_decide

/-- **At a generous `c = 200`, 17 candidates pass.** This is *more* than
the 11 stably-classifiable count from #386: rate-stability is strictly
weaker than trend-stability — a rule can keep its Forman scalar
bounded near `0` on every seed without producing the same trend on
every seed. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 200).length = 17 := by
  native_decide

/-- **Negative-target convergence (`tgt = -4, c = 12`) is empty.** No
rule in this family produces Forman scalars stably near `-4` at this
rate on every seed. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 (-4) 12).length = 0 := by
  native_decide

/-- **A shifted-target envelope `(tgt = 4, c = 16)` also picks up 7
candidates** — the stably-flat rules whose traces sit either at 0
(on `cycle4`) or 4 (on `edge12` / `path123`) all fit this envelope. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 4 16).length = 7 := by
  native_decide

/-! ### Structural connection: rate-(0, 12) = stably-flat

The tight `c = 12` envelope is exactly the canonical rate at which the
stably-flat traces (constants in `{0, 4, -4}` on the seeds, max index
`2`) fit `|x| · (i + 1) ≤ c`. The two selections coincide as sets. -/

/-- Every candidate passing the rate-(0, 12) envelope is stably flat. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 12).all
      (fun r => isStablyTrend r seedSet 2 CurvatureTrend.flat) = true := by
  native_decide

/-- And every stably-flat candidate passes the rate-(0, 12) envelope. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.flat).all
      (fun r => stablyConvergesToAt r seedSet 2 0 12) = true := by
  native_decide

/-! ### Rate-stability is strictly weaker than trend-stability

At `c = 200`, the rate-(0, c) selection has 17 elements while the
stably-classifiable selection has 11 — so rate-(0, 200) cannot be a
subset of stably-classifiable. Some rate-passing rules are seed-dependent
in their trend yet stay bounded near 0 on every seed. -/

/-- Strict inequality between the two counts. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length
      < (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 200).length := by
  native_decide

end RuleSignatureExecSearch
end InfraFormalization
