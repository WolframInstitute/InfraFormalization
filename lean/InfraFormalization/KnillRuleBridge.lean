/-
Knill sums on paths, under the subdivision rule, and on two disjoint tetrahedra.

The module evaluates `knillEulerScaled`, the sum of `K6(v) = 6 − 3·deg v + 2·tri v`, on
`pathHG n` for `n ∈ {3, 5, 8, 16}` (value 6), on the states of `singleWayEvolve subdivisionSys`
from one edge after 0 to 3 steps and from `pathHG 3` after 1 and 2 steps (value 6), and on the
disjoint union of two tetrahedra (value 24 = 12 + 12). All values are checked by `native_decide`.
The subdivision rule `{a, b} → {a, c}, {c, b}` adds a vertex `c` of degree 2 in no triangle, with
`K6(c) = 0`, and leaves the degrees of `a` and `b` unchanged. Invariance for all step counts is
not formalized.
-/

import InfraFormalization.KnillHigherGenus
import InfraFormalization.SubdivisionPath
import InfraFormalization.PathContinuumLimit

namespace InfraFormalization
namespace KnillRuleBridge

open MultiwayExec
open RuleSignatureExecMetrics
open SphereTriangulationAudit
open KnillDiscreteGaussBonnet
open KnillHigherGenus
open PathContinuumLimit

/-! ## Paths

On a path the two endpoints have degree 1 and `K6 = 3`, and the interior vertices have degree 2
and `K6 = 0`, so the sum is 6. -/

theorem path_3_knillEuler : knillEulerScaled (pathHG 3) = 6 := by native_decide
theorem path_5_knillEuler : knillEulerScaled (pathHG 5) = 6 := by native_decide
theorem path_8_knillEuler : knillEulerScaled (pathHG 8) = 6 := by native_decide
theorem path_16_knillEuler : knillEulerScaled (pathHG 16) = 6 := by native_decide

/-- `knillEulerScaled (pathHG n) = 6` for `n ∈ {3, 5, 8, 16}`. -/
theorem path_knill_const_six :
    knillEulerScaled (pathHG 3) = 6 ∧
    knillEulerScaled (pathHG 5) = 6 ∧
    knillEulerScaled (pathHG 8) = 6 ∧
    knillEulerScaled (pathHG 16) = 6 :=
  ⟨path_3_knillEuler, path_5_knillEuler, path_8_knillEuler, path_16_knillEuler⟩

/-! ## Subdivision rule

`knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] k) = 6` for `k ∈ {0, 1, 2, 3}`. -/

theorem subdivision_step_0_knill :
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 0) = 6 := by
  native_decide

theorem subdivision_step_1_knill :
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 1) = 6 := by
  native_decide

theorem subdivision_step_2_knill :
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 2) = 6 := by
  native_decide

theorem subdivision_step_3_knill :
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 3) = 6 := by
  native_decide

/-- The conjunction of the four values above. -/
theorem subdivision_knill_at_steps_0_to_3 :
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 0) = 6 ∧
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 1) = 6 ∧
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 2) = 6 ∧
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 3) = 6 :=
  ⟨subdivision_step_0_knill, subdivision_step_1_knill,
   subdivision_step_2_knill, subdivision_step_3_knill⟩

/-- `knillEulerScaled (singleWayEvolve subdivisionSys (pathHG 3) 1) = 6`. -/
theorem subdivision_on_path_3_knill_step_1 :
    knillEulerScaled (singleWayEvolve subdivisionSys (pathHG 3) 1) = 6 := by
  native_decide

theorem subdivision_on_path_3_knill_step_2 :
    knillEulerScaled (singleWayEvolve subdivisionSys (pathHG 3) 2) = 6 := by
  native_decide

/-! ## Two disjoint tetrahedra

The Knill sum of two vertex-disjoint tetrahedra is 24, the sum of their values 12 and 12. The
general additivity statement for disjoint unions is not formalized. -/

/-- The complete graph `K₄` on vertices 100, 101, 102, 103. -/
def shiftedTetrahedronHG : ExecHG ℕ :=
  [⟨[100, 101], List.cons_ne_nil _ _⟩,
   ⟨[100, 102], List.cons_ne_nil _ _⟩,
   ⟨[100, 103], List.cons_ne_nil _ _⟩,
   ⟨[101, 102], List.cons_ne_nil _ _⟩,
   ⟨[101, 103], List.cons_ne_nil _ _⟩,
   ⟨[102, 103], List.cons_ne_nil _ _⟩]

theorem shiftedTetrahedron_knillEuler :
    knillEulerScaled shiftedTetrahedronHG = 12 := by native_decide

/-- The edge list `tetrahedronHG ++ shiftedTetrahedronHG`. -/
def twoDisjointTetrahedraHG : ExecHG ℕ :=
  tetrahedronHG ++ shiftedTetrahedronHG

theorem two_disjoint_tetrahedra_knillEuler :
    knillEulerScaled twoDisjointTetrahedraHG = 24 := by native_decide

/-- The Knill sum of `twoDisjointTetrahedraHG` is the sum of the Knill sums of the two
tetrahedra. -/
theorem knill_additive_on_disjoint_tetra_sample :
    knillEulerScaled twoDisjointTetrahedraHG =
    knillEulerScaled tetrahedronHG + knillEulerScaled shiftedTetrahedronHG := by
  rw [two_disjoint_tetrahedra_knillEuler, tetrahedron_knillEuler,
      shiftedTetrahedron_knillEuler]
  rfl

/-! ## Conjunction -/

/-- The conjunction of `knillEulerScaled (pathHG 8) = 6`, the value 6 after three subdivision
steps from one edge, and the additivity equation for the two tetrahedra. -/
theorem knill_path_subdivision_disjoint_values :
    knillEulerScaled (pathHG 8) = 6 ∧
    knillEulerScaled (singleWayEvolve subdivisionSys [consEdge 1 2] 3) = 6 ∧
    knillEulerScaled twoDisjointTetrahedraHG =
      knillEulerScaled tetrahedronHG + knillEulerScaled shiftedTetrahedronHG :=
  ⟨path_8_knillEuler, subdivision_step_3_knill,
   knill_additive_on_disjoint_tetra_sample⟩

end KnillRuleBridge
end InfraFormalization
