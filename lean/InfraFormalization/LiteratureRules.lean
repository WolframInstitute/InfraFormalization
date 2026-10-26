/-
Curvature traces of rules from the Wolfram-model literature.

The module defines six rules with multi-edge or growing right-hand sides, including the rule
`{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` from G3, and two seeds, a triangle and a
path on five vertices. It evaluates the Forman, transport, Higuchi, degree-variance and
square-count traces of `canonicalDossier`, which applies `singleWayStep`, at depth 2 on selected
seeds. All values are checked by `native_decide`.
-/

import InfraFormalization.DualCurvatureScreener

namespace InfraFormalization
namespace LiteratureRules

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch

/-! ## Two-vertex hyperedge over `Fin n` -/

private def mkE {n : Nat} (i j : Fin n) : Hyperedge (Fin n) :=
  ⟨[i, j], List.cons_ne_nil _ _⟩

/-! ## Rules -/

/-- The rule `{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` from G3, with fresh
vertex `u`. Both sides have four edges. -/
def jgorardNamedRule : ExecRule where
  numBound := 5
  numFresh := 1
  lhs := [mkE 0 1, mkE 1 2, mkE 2 3, mkE 3 4]
  rhs := [mkE 1 5, mkE 5 4, mkE 3 0, mkE 0 5]

/-- `{{x,y}} → {{x,y},{x,z},{y,z}}` with fresh vertex `z`. -/
def triangulationRule : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [mkE 0 1]
  rhs := [mkE 0 1, mkE 0 2, mkE 1 2]

/-- `{{x,y},{y,z}} → {{x,y},{y,z},{x,z}}`. The rule adds the edge `{x,z}` to a path of length
2. -/
def triangleClosureRule : ExecRule where
  numBound := 3
  numFresh := 0
  lhs := [mkE 0 1, mkE 1 2]
  rhs := [mkE 0 1, mkE 1 2, mkE 0 2]

/-- `{{x,y}} → {{x,z},{z,y}}` with fresh vertex `z`. -/
def subdivisionRuleLit : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [mkE 0 1]
  rhs := [mkE 0 2, mkE 2 1]

/-- `{{x,y},{x,z}} → {{x,y},{x,w},{y,w},{z,w}}` with fresh vertex `w`. -/
def wheelerRule : ExecRule where
  numBound := 3
  numFresh := 1
  lhs := [mkE 0 1, mkE 0 2]
  rhs := [mkE 0 1, mkE 0 3, mkE 1 3, mkE 2 3]

/-- `{{x,y}} → {{x,y},{y,z},{z,w}}` with fresh vertices `z`, `w`. -/
def tripleExtendRule : ExecRule where
  numBound := 2
  numFresh := 2
  lhs := [mkE 0 1]
  rhs := [mkE 0 1, mkE 1 2, mkE 2 3]

/-! ## Seeds -/

/-- The triangle `{0,1},{1,2},{0,2}`. -/
def triangleSeed : ExecHG ℕ :=
  [⟨[0,1], List.cons_ne_nil _ _⟩,
   ⟨[1,2], List.cons_ne_nil _ _⟩,
   ⟨[0,2], List.cons_ne_nil _ _⟩]

/-- The path `0→1→2→3→4`, which has the shape of the left-hand side of `jgorardNamedRule`. -/
def path5Seed : ExecHG ℕ :=
  [⟨[0,1], List.cons_ne_nil _ _⟩,
   ⟨[1,2], List.cons_ne_nil _ _⟩,
   ⟨[2,3], List.cons_ne_nil _ _⟩,
   ⟨[3,4], List.cons_ne_nil _ _⟩]

/-! ## Traces at depth 2 -/

/-! ### `jgorardNamedRule` on `path5Seed` -/

/-- Forman trace of `jgorardNamedRule` on `path5Seed` at depth 2. -/
example : (canonicalDossier jgorardNamedRule path5Seed 2).formanScalarTrace
    = [4, 0, 0] := by native_decide
example : (canonicalDossier jgorardNamedRule path5Seed 2).transportScalarTrace
    = [-52, -64, -64] := by native_decide
example : (canonicalDossier jgorardNamedRule path5Seed 2).higuchiScalarTrace
    = [2, 2, 2] := by native_decide
example : (canonicalDossier jgorardNamedRule path5Seed 2).degVarianceTrace
    = [6, 16, 16] := by native_decide
example : (canonicalDossier jgorardNamedRule path5Seed 2).squareCountTrace
    = [0, 0, 0] := by native_decide

/-! ### `jgorardNamedRule` on `triangleSeed`

The triangle seed has 3 edges and the left-hand side has 4, so the rule has no match and every
trace is constant. -/

example : (canonicalDossier jgorardNamedRule triangleSeed 2).formanScalarTrace
    = [18, 18, 18] := by native_decide
example : (canonicalDossier jgorardNamedRule triangleSeed 2).transportScalarTrace
    = [-30, -30, -30] := by native_decide
example : (canonicalDossier jgorardNamedRule triangleSeed 2).higuchiScalarTrace
    = [0, 0, 0] := by native_decide
example : (canonicalDossier jgorardNamedRule triangleSeed 2).degVarianceTrace
    = [0, 0, 0] := by native_decide
example : (canonicalDossier jgorardNamedRule triangleSeed 2).squareCountTrace
    = [0, 0, 0] := by native_decide

/-! ### `triangleClosureRule` on `path123`

The first step adds the edge `{1,3}`. The traces are Forman `[4, 18, 18]`, transport
`[-16, -30, -30]`, Higuchi `[2, 0, 0]`, degree variance `[2, 0, 0]` and square count `[0, 0, 0]`. -/

example : (canonicalDossier triangleClosureRule path123 2).formanScalarTrace
    = [4, 18, 18] := by native_decide
example : (canonicalDossier triangleClosureRule path123 2).transportScalarTrace
    = [-16, -30, -30] := by native_decide
example : (canonicalDossier triangleClosureRule path123 2).higuchiScalarTrace
    = [2, 0, 0] := by native_decide
example : (canonicalDossier triangleClosureRule path123 2).degVarianceTrace
    = [2, 0, 0] := by native_decide
example : (canonicalDossier triangleClosureRule path123 2).squareCountTrace
    = [0, 0, 0] := by native_decide

/-! ### `triangleClosureRule` on `triangleSeed` -/

example : (canonicalDossier triangleClosureRule triangleSeed 2).formanScalarTrace
    = [18, 18, 18] := by native_decide
example : (canonicalDossier triangleClosureRule triangleSeed 2).higuchiScalarTrace
    = [0, 0, 0] := by native_decide

/-! ### `triangulationRule` on `edge12`

The Forman trace is `[4, 18, 24]`, the Higuchi trace is `[2, 0, -6]` and the square-count trace is
`[0, 0, 24]`. The value 24 counts ordered 4-cycle tuples. -/

example : (canonicalDossier triangulationRule edge12 2).formanScalarTrace
    = [4, 18, 24] := by native_decide
example : (canonicalDossier triangulationRule edge12 2).higuchiScalarTrace
    = [2, 0, -6] := by native_decide
example : (canonicalDossier triangulationRule edge12 2).squareCountTrace
    = [0, 0, 24] := by native_decide

/-! ## Rate bounds with `c = 0`

`rateBounded trace tgt 0` holds iff every entry of `trace` equals `tgt`. The theorems below state
this for the constant traces of `jgorardNamedRule` and `triangleClosureRule` on `triangleSeed`. -/

theorem jgorardNamedRule_triangle_forman_rateBounded :
    rateBounded (canonicalDossier jgorardNamedRule triangleSeed 2).formanScalarTrace
      18 0 = true := by native_decide

theorem jgorardNamedRule_triangle_transport_rateBounded :
    rateBounded (canonicalDossier jgorardNamedRule triangleSeed 2).transportScalarTrace
      (-30) 0 = true := by native_decide

theorem jgorardNamedRule_triangle_higuchi_rateBounded :
    rateBounded (canonicalDossier jgorardNamedRule triangleSeed 2).higuchiScalarTrace
      0 0 = true := by native_decide

theorem jgorardNamedRule_triangle_degvariance_rateBounded :
    rateBounded (canonicalDossier jgorardNamedRule triangleSeed 2).degVarianceTrace
      0 0 = true := by native_decide

theorem jgorardNamedRule_triangle_squarecount_rateBounded :
    rateBounded (canonicalDossier jgorardNamedRule triangleSeed 2).squareCountTrace
      0 0 = true := by native_decide

theorem triangleClosureRule_triangle_forman_rateBounded :
    rateBounded (canonicalDossier triangleClosureRule triangleSeed 2).formanScalarTrace
      18 0 = true := by native_decide

theorem triangleClosureRule_triangle_higuchi_rateBounded :
    rateBounded (canonicalDossier triangleClosureRule triangleSeed 2).higuchiScalarTrace
      0 0 = true := by native_decide

end LiteratureRules
end InfraFormalization
