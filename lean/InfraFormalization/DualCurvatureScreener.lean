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

namespace InfraFormalization
namespace DualCurvatureScreener

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecSearch
open OllivierRicciScreener

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

end DualCurvatureScreener
end InfraFormalization
