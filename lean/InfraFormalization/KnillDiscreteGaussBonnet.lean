/-
Knill's vertex curvature on three triangulations of the sphere.

For a vertex `v` with degree `deg(v)` and `tri(v)` triangles through it, Knill's discrete
Gauss–Bonnet curvature is `K(v) = 1 − deg(v)/2 + tri(v)/3`, and on a closed triangulated surface
`∑_v K(v) = V − E + F = χ`. This module defines the scaled curvature
`K6(v) = 6 − 3·deg(v) + 2·tri(v)`
and its sum `knillEulerScaled` on `ExecHG ℕ`, and shows that the sum equals 12 on the tetrahedron,
octahedron and icosahedron, while `execFormanScalar` takes the values 48 and 0 on the tetrahedron
and
icosahedron. The values are checked by `native_decide`.
-/

import InfraFormalization.SphereTriangulationAudit

namespace InfraFormalization
namespace KnillDiscreteGaussBonnet

open MultiwayExec
open RuleSignatureExecMetrics
open SphereTriangulationAudit

/-! ## Triangles through a vertex -/

/-- The number of pairs `x < y` of neighbours of `v` that are adjacent to each other, which is the
number of 3-cliques containing `v`. -/
def execTriangleCountAtVertex (H : ExecHG ℕ) (v : ℕ) : ℕ :=
  let vs := vertexList H
  let nbrs := vs.filter (fun x => decide (x ≠ v) && execAdj H v x)
  nbrs.foldr (fun x acc =>
    acc + (nbrs.filter (fun y => x < y && execAdj H x y)).length) 0

/-! ## Knill vertex curvature scaled by 6

`K6(v) = 6 − 3·deg(v) + 2·tri(v)`. On a closed triangulated surface, `∑_v K6(v) = 6χ`. -/

/-- `K6(v) = 6 − 3·deg(v) + 2·tri(v)`, six times Knill's vertex curvature. -/
def knillVertexK6 (H : ExecHG ℕ) (v : ℕ) : ℤ :=
  6 - 3 * (execAdjDegree H v : ℤ) + 2 * (execTriangleCountAtVertex H v : ℤ)

/-- `∑_v K6(v)` over the vertices of `H`. -/
def knillEulerScaled (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => acc + knillVertexK6 H v) 0

/-! ## Values on the three Platonic triangulations of S²

The sum of `K6` equals 12 = 6 · χ(S²) on the tetrahedron, octahedron and icosahedron, checked by
`native_decide`. -/

theorem tetrahedron_knillEuler : knillEulerScaled tetrahedronHG = 12 := by native_decide
theorem octahedron_knillEuler : knillEulerScaled octahedronHG = 12 := by native_decide
theorem icosahedron_knillEuler : knillEulerScaled icosahedronHG = 12 := by native_decide

/-- `knillEulerScaled` equals 12 on the tetrahedron, the octahedron and the icosahedron. -/
theorem knill_recovers_chi_S2 :
    knillEulerScaled tetrahedronHG = 12 ∧
    knillEulerScaled octahedronHG = 12 ∧
    knillEulerScaled icosahedronHG = 12 :=
  ⟨tetrahedron_knillEuler, octahedron_knillEuler, icosahedron_knillEuler⟩

/-- `knillEulerScaled` takes the same value on the tetrahedron, the octahedron and the icosahedron.
-/
theorem knill_values_three_S2_triangulations :
    knillEulerScaled tetrahedronHG = knillEulerScaled octahedronHG ∧
    knillEulerScaled octahedronHG = knillEulerScaled icosahedronHG ∧
    knillEulerScaled tetrahedronHG = knillEulerScaled icosahedronHG := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tetrahedron_knillEuler, octahedron_knillEuler]
  · rw [octahedron_knillEuler, icosahedron_knillEuler]
  · rw [tetrahedron_knillEuler, icosahedron_knillEuler]

/-! ## Comparison with the Forman scalar -/

/-- `execFormanScalar` equals 48 on the tetrahedron and 0 on the icosahedron, and `knillEulerScaled`
equals 12 on the tetrahedron, the octahedron and the icosahedron. -/
theorem forman_and_knill_values_S2_triangulations :
    -- Forman scalar on the tetrahedron and the icosahedron.
    (execFormanScalar tetrahedronHG = 48 ∧
     execFormanScalar icosahedronHG = 0) ∧
    -- Knill sum on the three triangulations.
    (knillEulerScaled tetrahedronHG = 12 ∧
     knillEulerScaled octahedronHG = 12 ∧
     knillEulerScaled icosahedronHG = 12) :=
  ⟨⟨tetrahedron_forman, icosahedron_forman⟩, knill_recovers_chi_S2⟩

/-! ## Summary

The sum of `K6` equals 12 on the three Platonic triangulations of S². The identity
`knillEulerScaled = 6χ` for every closed triangulated surface is not proved here. -/

end KnillDiscreteGaussBonnet
end InfraFormalization
