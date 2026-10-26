/-
Seed-stable classification by five scalar traces.

The module applies the classification `classifyForman` (constant, or sign of the last entry) to
the transport, Higuchi, degree-variance and square-count traces of `canonicalDossier`, which
applies `singleWayStep`. A rule is stably classifiable for a scalar if the class is the same on
every seed. The module defines the conjunctions of two, three, four and five of these conditions,
the Forman condition included, and counts the rules of `enumerateRules2_1 2` on `seedSet` at depth
2 that satisfy each: 11 (Forman), 17 (transport), 17 (Higuchi), 11 (degree variance),
11 (square count), 11 (two, three), 5 (four, five). All counts are checked by `native_decide`.
-/

import InfraFormalization.RuleSignatureExecSearch
import InfraFormalization.OllivierRicciScreener
import InfraFormalization.HiguchiScreener
import InfraFormalization.DegreeVarianceScreener
import InfraFormalization.SquareCountScreener

namespace InfraFormalization
namespace DualCurvatureScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecSearch
open OllivierRicciScreener
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener

/-- `classifyForman` applied to the transport trace of `canonicalDossier r seed n`. -/
def transportTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).transportScalarTrace)

/-- The transport classes on each seed. -/
def transportTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => transportTrendOf r s n)

/-- `true` iff the transport class is the same on every seed. -/
def transportStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match transportTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- `stablyClassifiable && transportStablyClassifiable`. -/
def dualStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n && transportStablyClassifiable r seeds n

/-- The candidates satisfying `dualStablyClassifiable`. -/
def dualStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => dualStablyClassifiable r seeds n)

/-! ### Counts for Forman and transport -/

/-- 11 rules are Forman-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- 17 rules are transport-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length = 17 := by
  native_decide

/-- 11 rules satisfy `dualStablyClassifiable`. -/
example :
    (dualStableSelect (enumerateRules2_1 2) seedSet 2).length = 11 := by
  native_decide

/-- Every Forman-stably classifiable rule is transport-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).all
      (fun r => transportStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- The Forman count is less than the transport count: 11 < 17. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length
    < ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length := by
  native_decide

/-- The `dualStableSelect` count equals the Forman count. -/
example :
    (dualStableSelect (enumerateRules2_1 2) seedSet 2).length
      = ((enumerateRules2_1 2).filter
          (fun r => stablyClassifiable r seedSet 2)).length := by
  native_decide

/-- The transport count minus the Forman count is 6. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length
    - ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 6 := by
  native_decide

/-! ## Forman, transport and Higuchi -/

/-- `classifyForman` applied to the Higuchi trace of `canonicalDossier r seed n`. -/
def higuchiTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).higuchiScalarTrace)

/-- The Higuchi classes on each seed. -/
def higuchiTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => higuchiTrendOf r s n)

/-- `true` iff the Higuchi class is the same on every seed. -/
def higuchiStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match higuchiTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- The Forman, transport and Higuchi classes are each the same on every seed. -/
def tripleStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n
    && transportStablyClassifiable r seeds n
    && higuchiStablyClassifiable r seeds n

/-- The candidates satisfying `tripleStablyClassifiable`. -/
def tripleStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => tripleStablyClassifiable r seeds n)

/-! ### Counts for Forman, transport and Higuchi -/

/-- 17 rules are Higuchi-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).length = 17 := by
  native_decide

/-- 11 rules satisfy `tripleStablyClassifiable`. -/
example :
    (tripleStableSelect (enumerateRules2_1 2) seedSet 2).length = 11 := by
  native_decide

/-- Every Forman-stably classifiable rule is Higuchi-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).all
      (fun r => higuchiStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- Every Higuchi-stably classifiable rule is transport-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).all
      (fun r => transportStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- Every transport-stably classifiable rule is Higuchi-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).all
      (fun r => higuchiStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- The counts 11 (Forman), 17 (transport), 17 (Higuchi) and 11 (all three). -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11
  ∧ ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length = 17
  ∧ ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).length = 17
  ∧ (tripleStableSelect (enumerateRules2_1 2) seedSet 2).length = 11 := by
  native_decide

/-! ## Adding degree variance -/

/-- `classifyForman` applied to the degree-variance trace of `canonicalDossier r seed n`. -/
def degVarianceTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).degVarianceTrace)

/-- The degree-variance classes on each seed. -/
def degVarianceTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => degVarianceTrendOf r s n)

/-- `true` iff the degree-variance class is the same on every seed. -/
def degVarianceStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match degVarianceTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- The Forman, transport, Higuchi and degree-variance classes are each the same on every
seed. -/
def quadStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n
    && transportStablyClassifiable r seeds n
    && higuchiStablyClassifiable r seeds n
    && degVarianceStablyClassifiable r seeds n

/-- The candidates satisfying `quadStablyClassifiable`. -/
def quadStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => quadStablyClassifiable r seeds n)

/-! ### Counts including degree variance -/

/-- 11 rules are degree-variance-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => degVarianceStablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- 5 rules satisfy `quadStablyClassifiable`. -/
example :
    (quadStableSelect (enumerateRules2_1 2) seedSet 2).length = 5 := by
  native_decide

/-- Some Forman-stably classifiable rule is not degree-variance-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).all
      (fun r => degVarianceStablyClassifiable r seedSet 2) = false := by
  native_decide

/-- Some degree-variance-stably classifiable rule is not Forman-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => degVarianceStablyClassifiable r seedSet 2)).all
      (fun r => stablyClassifiable r seedSet 2) = false := by
  native_decide

/-- The counts 11 (Forman), 17 (transport), 17 (Higuchi), 11 (degree variance), 11 (three
conditions) and 5 (four conditions). -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11
  ∧ ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length = 17
  ∧ ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).length = 17
  ∧ ((enumerateRules2_1 2).filter
        (fun r => degVarianceStablyClassifiable r seedSet 2)).length = 11
  ∧ (tripleStableSelect (enumerateRules2_1 2) seedSet 2).length = 11
  ∧ (quadStableSelect (enumerateRules2_1 2) seedSet 2).length = 5 := by
  native_decide

/-! ## Adding square count -/

/-- `classifyForman` applied to the square-count trace of `canonicalDossier r seed n`. -/
def squareCountTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).squareCountTrace)

/-- The square-count classes on each seed. -/
def squareCountTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => squareCountTrendOf r s n)

/-- `true` iff the square-count class is the same on every seed. -/
def squareCountStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match squareCountTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- The Forman, transport, Higuchi, degree-variance and square-count classes are each the same
on every seed. -/
def quintStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n
    && transportStablyClassifiable r seeds n
    && higuchiStablyClassifiable r seeds n
    && degVarianceStablyClassifiable r seeds n
    && squareCountStablyClassifiable r seeds n

/-- The candidates satisfying `quintStablyClassifiable`. -/
def quintStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => quintStablyClassifiable r seeds n)

/-! ### Counts including square count -/

/-- 11 rules are square-count-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => squareCountStablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- 5 rules satisfy `quintStablyClassifiable`. -/
example :
    (quintStableSelect (enumerateRules2_1 2) seedSet 2).length = 5 := by
  native_decide

/-- Every rule satisfying `quadStablyClassifiable` is square-count-stably classifiable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => quadStablyClassifiable r seedSet 2)).all
      (fun r => squareCountStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- The counts 11 (Forman), 17 (transport), 17 (Higuchi), 11 (degree variance), 11 (square
count), 11 (three conditions), 5 (four conditions) and 5 (five conditions). -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11
  ∧ ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length = 17
  ∧ ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).length = 17
  ∧ ((enumerateRules2_1 2).filter
        (fun r => degVarianceStablyClassifiable r seedSet 2)).length = 11
  ∧ ((enumerateRules2_1 2).filter
        (fun r => squareCountStablyClassifiable r seedSet 2)).length = 11
  ∧ (tripleStableSelect (enumerateRules2_1 2) seedSet 2).length = 11
  ∧ (quadStableSelect (enumerateRules2_1 2) seedSet 2).length = 5
  ∧ (quintStableSelect (enumerateRules2_1 2) seedSet 2).length = 5 := by
  native_decide

end DualCurvatureScreener
end InfraFormalization
