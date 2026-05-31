/-
**Dual-curvature select: combine Forman (#384) and Transport (#402)
screeners** (#403).

After #402 we have two parallel curvature scalar families on `ExecHG ℕ`:

  * `Dossier.formanScalarTrace`     — triangle-Forman (#384)
  * `Dossier.transportScalarTrace`  — Ollivier-style product-coupling
                                       upper bound (#402)

A candidate rule's curvature class is more credible if BOTH scalars are
seed-stable. This module defines the dual-curvature filter and certifies
the new distribution on the 21-candidate `enumerateRules2_1 2` family
over the standard `seedSet`.

Stronger discriminator: a rule passing the dual-curvature filter has a
seed-independent verdict on two *independent* curvature definitions —
genuine convergent evidence that the rule has a well-defined curvature
class on the family.
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

/-- The transport-scalar trend of a rule on a seed at depth `n`. Uses
the same `classifyForman` shape (constant ⇒ `flat`, else sign of final
value) since the scalar lives in `ℤ`. -/
def transportTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).transportScalarTrace)

/-- The transport trend across a list of seeds. -/
def transportTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => transportTrendOf r s n)

/-- A candidate's transport trend is stably-classifiable iff every
seed gives the same trend. -/
def transportStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match transportTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- **Dual-curvature stably classifiable**: BOTH the Forman trend AND
the transport trend are seed-stable. -/
def dualStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n && transportStablyClassifiable r seeds n

/-- Dual-curvature selection: keep candidates passing both screeners. -/
def dualStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => dualStablyClassifiable r seeds n)

/-! ### Certified dual-stability distribution -/

/-- **Forman stably-classifiable count: 11** (matches #386). -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- **Transport stably-classifiable count: 17** — the transport
screener is *more permissive* than the Forman screener on this family. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length = 17 := by
  native_decide

/-- **Dual stably-classifiable count: 11** — exactly the Forman-stable
candidates also pass the transport stability. -/
example :
    (dualStableSelect (enumerateRules2_1 2) seedSet 2).length = 11 := by
  native_decide

/-- **Containment**: every Forman-stably-classifiable candidate is
also transport-stably-classifiable. The Forman screener is *strictly
stricter* than the transport screener on this family (`11 < 17`). -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).all
      (fun r => transportStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- **Forman strictly stricter than transport**: 11 < 17. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length
    < ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length := by
  native_decide

/-- **Dual-screener-survivors equal Forman-survivors** on this family
— the transport screener adds no candidates that Forman didn't already
classify. -/
example :
    (dualStableSelect (enumerateRules2_1 2) seedSet 2).length
      = ((enumerateRules2_1 2).filter
          (fun r => stablyClassifiable r seedSet 2)).length := by
  native_decide

/-- **6 candidates pass transport but NOT Forman**: these are
transport-classifiable in a sense the triangle-Forman screener cannot
detect. The two screeners are not equivalent — they expose different
aspects of curvature. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length
    - ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 6 := by
  native_decide

/-! ## Triple-curvature select: Forman + Transport + Higuchi -/

/-- The Higuchi-scalar trend of a rule on a seed at depth `n`. -/
def higuchiTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).higuchiScalarTrace)

/-- The Higuchi trend across a list of seeds. -/
def higuchiTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => higuchiTrendOf r s n)

/-- A candidate's Higuchi trend is stably-classifiable. -/
def higuchiStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match higuchiTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- **Triple-curvature stably classifiable**: ALL three screeners give
seed-independent verdicts. -/
def tripleStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n
    && transportStablyClassifiable r seeds n
    && higuchiStablyClassifiable r seeds n

/-- The triple-curvature selection. -/
def tripleStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => tripleStablyClassifiable r seeds n)

/-! ### Certified triple-stability distribution -/

/-- **Higuchi stably-classifiable: 17 candidates** — same count as
Transport (#403). -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).length = 17 := by
  native_decide

/-- **Triple stably-classifiable: 11 candidates** — same as Forman
alone, consistent with Forman ⊆ Transport ∩ Higuchi (since the
intersection of Transport and Higuchi can't be smaller than Forman). -/
example :
    (tripleStableSelect (enumerateRules2_1 2) seedSet 2).length = 11 := by
  native_decide

/-- **Higuchi-stable contains Forman-stable**: every Forman-stable
rule is also Higuchi-stable. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).all
      (fun r => higuchiStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- **Higuchi-stable ⊆ Transport-stable** (and the converse holds too:
both have count 17, see the summary below). So the two more-permissive
screeners agree on this family. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).all
      (fun r => transportStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- **Transport-stable ⊆ Higuchi-stable** — combined with the
matching counts (17 = 17), the two screeners produce the same set. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).all
      (fun r => higuchiStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- **Triple-curvature distribution summary**:
  - Forman-stable    = 11
  - Transport-stable = 17  (= Higuchi-stable)
  - Higuchi-stable   = 17  (= Transport-stable)
  - Triple-stable    = 11  (= Forman-stable, since Forman ⊆ T = H)
The two more-permissive screeners agree exactly; the strict screener
(Forman) determines the triple intersection. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11
  ∧ ((enumerateRules2_1 2).filter
        (fun r => transportStablyClassifiable r seedSet 2)).length = 17
  ∧ ((enumerateRules2_1 2).filter
        (fun r => higuchiStablyClassifiable r seedSet 2)).length = 17
  ∧ (tripleStableSelect (enumerateRules2_1 2) seedSet 2).length = 11 := by
  native_decide

/-! ## Quad-curvature select: Forman + Transport + Higuchi + DegVariance -/

/-- The degree-variance scalar trend of a rule on a seed at depth `n`. -/
def degVarianceTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).degVarianceTrace)

/-- The degree-variance trend across a list of seeds. -/
def degVarianceTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => degVarianceTrendOf r s n)

/-- A candidate's degree-variance trend is stably-classifiable. -/
def degVarianceStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match degVarianceTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- **Quad-curvature stably classifiable**: ALL FOUR screeners give
seed-independent verdicts. -/
def quadStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n
    && transportStablyClassifiable r seeds n
    && higuchiStablyClassifiable r seeds n
    && degVarianceStablyClassifiable r seeds n

/-- The quad-curvature selection. -/
def quadStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => quadStablyClassifiable r seeds n)

/-! ### Certified quad-stability distribution -/

/-- **DegVariance stably-classifiable: 11 candidates** — same total as
Forman, but a **DIFFERENT SET** (mutual non-containment certified
below). DegVariance is a genuine fourth angle, not a relabelling. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => degVarianceStablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- **Quad stably-classifiable: 5 candidates** — adding DegVariance
to the Triple cascade SHRINKS the stable set from 11 to 5, a strict
refinement. Six rules that pass Forman + Transport + Higuchi fail the
degree-variance check; the fourth screener finds new structure. -/
example :
    (quadStableSelect (enumerateRules2_1 2) seedSet 2).length = 5 := by
  native_decide

/-- **Forman-stable ⊄ DegVariance-stable**: NOT every Forman-stable
rule is DegVariance-stable. Six rules in the Forman-stable set fail
the degree-variance test. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).all
      (fun r => degVarianceStablyClassifiable r seedSet 2) = false := by
  native_decide

/-- **DegVariance-stable ⊄ Forman-stable**: NOT every DegVariance-stable
rule is Forman-stable. Six rules in the DegVariance-stable set fail
the Forman test. The two screeners are **independent** — they classify
different curvature aspects. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => degVarianceStablyClassifiable r seedSet 2)).all
      (fun r => stablyClassifiable r seedSet 2) = false := by
  native_decide

/-- **Quad-curvature distribution summary**:
  - Forman-stable      = 11
  - Transport-stable   = 17
  - Higuchi-stable     = 17  (= Transport-stable as sets)
  - DegVariance-stable = 11  (same total as Forman, DIFFERENT set)
  - Triple-stable      = 11  (= Forman ⊆ Transport ∩ Higuchi)
  - Quad-stable        =  5  (strict refinement: Triple ∩ DegVariance)
DegVariance is the first screener to **shrink** the stable set
below 11, because it's the first independent of the local
combinatorial-Forman family. The fourfold cross-confirmation
identifies 5 rules with maximally-stable curvature signatures. -/
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

/-! ## Quint-curvature select: Forman + Transport + Higuchi + DegVariance + SquareCount -/

/-- The square-count scalar trend of a rule on a seed at depth `n`. -/
def squareCountTrendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).squareCountTrace)

/-- The square-count trend across a list of seeds. -/
def squareCountTrendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List CurvatureTrend :=
  seeds.map (fun s => squareCountTrendOf r s n)

/-- A candidate's square-count trend is stably-classifiable. -/
def squareCountStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match squareCountTrendsAcross r seeds n with
  | []      => true
  | t :: ts => ts.all (fun t' => decide (t' = t))

/-- **Quint-curvature stably classifiable**: ALL FIVE screeners give
seed-independent verdicts. -/
def quintStablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  stablyClassifiable r seeds n
    && transportStablyClassifiable r seeds n
    && higuchiStablyClassifiable r seeds n
    && degVarianceStablyClassifiable r seeds n
    && squareCountStablyClassifiable r seeds n

/-- The quint-curvature selection. -/
def quintStableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : List ExecRule :=
  cands.filter (fun r => quintStablyClassifiable r seeds n)

/-! ### Certified quint-stability distribution -/

/-- **SquareCount stably-classifiable: 11 candidates** — same total
as Forman / DegVariance. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => squareCountStablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- **Quint stably-classifiable: 5 candidates** — the same as Quad.
SquareCount is a *redundant filter* on top of Quad: every quad-stable
rule is also square-count-stable on this family. The five-fold
intersection equals the four-fold intersection. -/
example :
    (quintStableSelect (enumerateRules2_1 2) seedSet 2).length = 5 := by
  native_decide

/-- **Quad-stable ⊆ SquareCount-stable**: every quad-stable rule
also has a seed-stable square-count verdict. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => quadStablyClassifiable r seedSet 2)).all
      (fun r => squareCountStablyClassifiable r seedSet 2) = true := by
  native_decide

/-- **Quint-curvature distribution summary**:
  - Forman-stable      = 11
  - Transport-stable   = 17
  - Higuchi-stable     = 17  (= Transport set-wise)
  - DegVariance-stable = 11  (different set from Forman)
  - SquareCount-stable = 11
  - Triple-stable      = 11
  - Quad-stable        =  5  (Triple ∩ DegVariance — first strict refinement)
  - Quint-stable       =  5  (= Quad — SquareCount agrees on the quad-survivors)
The 5 quint-stable rules survive ALL FIVE independent screeners.
The five-fold cross-confirmation identifies the maximally robust
curvature-class on this family. -/
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
