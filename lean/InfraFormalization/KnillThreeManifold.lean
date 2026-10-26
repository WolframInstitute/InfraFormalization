/-
Knill's vertex curvature in dimension 3 on the boundary of the 4-simplex.

The three-dimensional vertex curvature, scaled by `12 = lcm(2, 3, 4)`, is
`K12(v) = 12 − 6·deg(v) + 4·tri(v) − 3·tet(v)`, where `tet(v)` counts the 4-cliques containing `v`.
Its sum over vertices is `12 · (V − E + F − T)`. This module defines `K12` and its sum on
`ExecHG ℕ` and shows, by `native_decide`, that both are 0 on the complete graph `K₅`, the 1-skeleton
of the boundary of the 4-simplex, which is homeomorphic to `S³` with `χ(S³) = 0`.
-/

import InfraFormalization.KnillRuleBridge

namespace InfraFormalization
namespace KnillThreeManifold

open MultiwayExec
open RuleSignatureExecMetrics
open SphereTriangulationAudit
open KnillDiscreteGaussBonnet

/-! ## Tetrahedra through a vertex -/

/-- The number of triples `x < y < z` of neighbours of `v` that are pairwise adjacent, which is the
number of 4-cliques containing `v`. -/
def execTetCountAtVertex (H : ExecHG ℕ) (v : ℕ) : ℕ :=
  let vs := vertexList H
  let nbrs := vs.filter (fun x => decide (x ≠ v) && execAdj H v x)
  nbrs.foldr (fun x acc1 =>
    acc1 + nbrs.foldr (fun y acc2 =>
      if x < y && execAdj H x y then
        acc2 + (nbrs.filter (fun z =>
          y < z && execAdj H x z && execAdj H y z)).length
      else acc2) 0) 0

/-! ## Three-dimensional vertex curvature scaled by 12

`K12(v) = 12 − 6·deg(v) + 4·tri(v) − 3·tet(v)`. On a closed triangulated 3-manifold,
`∑_v K12(v) = 12χ`. -/

/-- `K12(v) = 12 − 6·deg(v) + 4·tri(v) − 3·tet(v)`. -/
def knillVertexK12 (H : ExecHG ℕ) (v : ℕ) : ℤ :=
  12 - 6 * (execAdjDegree H v : ℤ)
     + 4 * (execTriangleCountAtVertex H v : ℤ)
     - 3 * (execTetCountAtVertex H v : ℤ)

/-- `∑_v K12(v)` over the vertices of `H`. -/
def knillEulerScaled12 (H : ExecHG ℕ) : ℤ :=
  (vertexList H).foldr (fun v acc => acc + knillVertexK12 H v) 0

/-! ## Boundary of the 4-simplex

The boundary of the 4-simplex has 5 vertices, 10 edges, 10 triangles and 5 tetrahedra, is
homeomorphic to `S³`, and has 1-skeleton `K₅`. -/

/-- The complete graph `K₅` on vertices `{0, 1, 2, 3, 4}`. -/
def k5HG : ExecHG ℕ :=
  [⟨[0, 1], List.cons_ne_nil _ _⟩, ⟨[0, 2], List.cons_ne_nil _ _⟩,
   ⟨[0, 3], List.cons_ne_nil _ _⟩, ⟨[0, 4], List.cons_ne_nil _ _⟩,
   ⟨[1, 2], List.cons_ne_nil _ _⟩, ⟨[1, 3], List.cons_ne_nil _ _⟩,
   ⟨[1, 4], List.cons_ne_nil _ _⟩, ⟨[2, 3], List.cons_ne_nil _ _⟩,
   ⟨[2, 4], List.cons_ne_nil _ _⟩, ⟨[3, 4], List.cons_ne_nil _ _⟩]

/-! ## K12 on K₅

Every vertex of `K₅` has degree 4 and lies in 6 triangles and 4 tetrahedra, so
`K12(v) = 12 − 24 + 24 − 12 = 0`. -/

theorem k5_vertex_0_K12 : knillVertexK12 k5HG 0 = 0 := by native_decide
theorem k5_vertex_1_K12 : knillVertexK12 k5HG 1 = 0 := by native_decide
theorem k5_vertex_2_K12 : knillVertexK12 k5HG 2 = 0 := by native_decide
theorem k5_vertex_3_K12 : knillVertexK12 k5HG 3 = 0 := by native_decide
theorem k5_vertex_4_K12 : knillVertexK12 k5HG 4 = 0 := by native_decide

/-! ## Sum of K12 on K₅

`χ(S³) = 0`, so `12·χ(S³) = 0`. -/

/-- `knillEulerScaled12 k5HG = 0`, checked by `native_decide`. -/
theorem k5_knillEuler12 : knillEulerScaled12 k5HG = 0 := by native_decide

/-! ## Dimensions 2 and 3 -/

/-- `knillEulerScaled tetrahedronHG = 12` and `knillEulerScaled12 k5HG = 0`. -/
theorem knill_values_tetrahedron_and_k5 :
    -- 2D: K4 triangulation of S² gives knillEulerScaled = 12 = 6·χ(S²).
    knillEulerScaled tetrahedronHG = 12 ∧
    -- 3D: K5 triangulation of S³ gives knillEulerScaled12 = 0 = 12·χ(S³).
    knillEulerScaled12 k5HG = 0 :=
  ⟨tetrahedron_knillEuler, k5_knillEuler12⟩

/-! ## Summary

In dimension `d`, Knill's vertex curvature is
`K(v) = Σ_{k=0}^{d} (-1)^k · (number of (k+1)-cliques containing v) / (k+1)`; for `d = 1, 2, 3` its
sum over vertices is `V − E`, `V − E + F` and `V − E + F − T`. This module evaluates the case
`d = 3` on `K₅`. The general-dimension identity is not proved here. -/

end KnillThreeManifold
end InfraFormalization
