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

end RuleSignatureExecSearch
end InfraFormalization
