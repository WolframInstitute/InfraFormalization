/-
Forman and Higuchi totals of three triangulations of the 2-sphere.

The module defines the edge graphs of the tetrahedron, octahedron and icosahedron and evaluates
their Forman scalars (48, 48, 0) and doubled Higuchi totals (-4, -12, -36), each checked by
`native_decide`. The per-vertex Forman values are 12, 8 and 0. It proves that the Forman scalar
of the icosahedron differs from the other two and that the three Higuchi totals are pairwise
distinct.
-/

import InfraFormalization.PolynomialDensityLimits

namespace InfraFormalization
namespace SphereTriangulationAudit

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener

/-! ## Three triangulations of the 2-sphere -/

/-- Tetrahedron `K_4`: complete graph on 4 vertices, 6 edges, all degree 3. -/
def tetrahedronHG : ExecHG ℕ :=
  [⟨[0, 1], List.cons_ne_nil _ _⟩,
   ⟨[0, 2], List.cons_ne_nil _ _⟩,
   ⟨[0, 3], List.cons_ne_nil _ _⟩,
   ⟨[1, 2], List.cons_ne_nil _ _⟩,
   ⟨[1, 3], List.cons_ne_nil _ _⟩,
   ⟨[2, 3], List.cons_ne_nil _ _⟩]

/-- Octahedron: 6 vertices, 12 edges, all degree 4, antipodal pairs
`(0,1), (2,3), (4,5)`. Each vertex connects to its 4 non-antipodal
others. -/
def octahedronHG : ExecHG ℕ :=
  [⟨[0, 2], List.cons_ne_nil _ _⟩, ⟨[0, 3], List.cons_ne_nil _ _⟩,
   ⟨[0, 4], List.cons_ne_nil _ _⟩, ⟨[0, 5], List.cons_ne_nil _ _⟩,
   ⟨[1, 2], List.cons_ne_nil _ _⟩, ⟨[1, 3], List.cons_ne_nil _ _⟩,
   ⟨[1, 4], List.cons_ne_nil _ _⟩, ⟨[1, 5], List.cons_ne_nil _ _⟩,
   ⟨[2, 4], List.cons_ne_nil _ _⟩, ⟨[2, 5], List.cons_ne_nil _ _⟩,
   ⟨[3, 4], List.cons_ne_nil _ _⟩, ⟨[3, 5], List.cons_ne_nil _ _⟩]

/-- Icosahedron: 12 vertices, 30 edges, all degree 5. Vertex 0 is the north pole, vertices
1-5 form the upper ring, vertices 6-10 form the lower ring and vertex 11 is the south pole. -/
def icosahedronHG : ExecHG ℕ :=
  [⟨[0,1], List.cons_ne_nil _ _⟩, ⟨[0,2], List.cons_ne_nil _ _⟩,
   ⟨[0,3], List.cons_ne_nil _ _⟩, ⟨[0,4], List.cons_ne_nil _ _⟩,
   ⟨[0,5], List.cons_ne_nil _ _⟩,
   ⟨[1,2], List.cons_ne_nil _ _⟩, ⟨[2,3], List.cons_ne_nil _ _⟩,
   ⟨[3,4], List.cons_ne_nil _ _⟩, ⟨[4,5], List.cons_ne_nil _ _⟩,
   ⟨[5,1], List.cons_ne_nil _ _⟩,
   ⟨[1,6], List.cons_ne_nil _ _⟩, ⟨[1,7], List.cons_ne_nil _ _⟩,
   ⟨[2,7], List.cons_ne_nil _ _⟩, ⟨[2,8], List.cons_ne_nil _ _⟩,
   ⟨[3,8], List.cons_ne_nil _ _⟩, ⟨[3,9], List.cons_ne_nil _ _⟩,
   ⟨[4,9], List.cons_ne_nil _ _⟩, ⟨[4,10], List.cons_ne_nil _ _⟩,
   ⟨[5,10], List.cons_ne_nil _ _⟩, ⟨[5,6], List.cons_ne_nil _ _⟩,
   ⟨[6,7], List.cons_ne_nil _ _⟩, ⟨[7,8], List.cons_ne_nil _ _⟩,
   ⟨[8,9], List.cons_ne_nil _ _⟩, ⟨[9,10], List.cons_ne_nil _ _⟩,
   ⟨[10,6], List.cons_ne_nil _ _⟩,
   ⟨[6,11], List.cons_ne_nil _ _⟩, ⟨[7,11], List.cons_ne_nil _ _⟩,
   ⟨[8,11], List.cons_ne_nil _ _⟩, ⟨[9,11], List.cons_ne_nil _ _⟩,
   ⟨[10,11], List.cons_ne_nil _ _⟩]

/-! ## Forman values

Checked by `native_decide`. -/

theorem tetrahedron_forman : execFormanScalar tetrahedronHG = 48 := by native_decide
theorem octahedron_forman : execFormanScalar octahedronHG = 48 := by native_decide
theorem icosahedron_forman : execFormanScalar icosahedronHG = 0 := by native_decide

/-! ## Higuchi values

`higuchiTotalDoubled` is `Σ (2 − deg v)`, which equals `V · (2 − k)` for a `k`-regular graph on
`V` vertices. Checked by `native_decide`. -/

theorem tetrahedron_higuchi : higuchiTotalDoubled tetrahedronHG = -4 := by native_decide
theorem octahedron_higuchi : higuchiTotalDoubled octahedronHG = -12 := by native_decide
theorem icosahedron_higuchi : higuchiTotalDoubled icosahedronHG = -36 := by native_decide

/-! ## Comparisons -/

/-- The Forman scalar of the icosahedron differs from that of the tetrahedron and from that of
the octahedron. -/
theorem forman_inconsistent_across_sphere_triangulations :
    execFormanScalar tetrahedronHG ≠ execFormanScalar icosahedronHG ∧
    execFormanScalar octahedronHG ≠ execFormanScalar icosahedronHG := by
  refine ⟨?_, ?_⟩
  · rw [tetrahedron_forman, icosahedron_forman]; decide
  · rw [octahedron_forman, icosahedron_forman]; decide

/-- The doubled Higuchi totals of the tetrahedron, octahedron and icosahedron are pairwise
distinct. -/
theorem higuchi_inconsistent_across_sphere_triangulations :
    higuchiTotalDoubled tetrahedronHG ≠ higuchiTotalDoubled octahedronHG ∧
    higuchiTotalDoubled octahedronHG ≠ higuchiTotalDoubled icosahedronHG ∧
    higuchiTotalDoubled tetrahedronHG ≠ higuchiTotalDoubled icosahedronHG := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tetrahedron_higuchi, octahedron_higuchi]; decide
  · rw [octahedron_higuchi, icosahedron_higuchi]; decide
  · rw [tetrahedron_higuchi, icosahedron_higuchi]; decide

/-- The conjunction of the six values: Forman scalars 48, 48, 0 and doubled Higuchi totals
-4, -12, -36 for the tetrahedron, octahedron and icosahedron. -/
theorem sphere_triangulation_scalar_values :
    (execFormanScalar tetrahedronHG = 48 ∧ execFormanScalar octahedronHG = 48 ∧
     execFormanScalar icosahedronHG = 0) ∧
    (higuchiTotalDoubled tetrahedronHG = -4 ∧
     higuchiTotalDoubled octahedronHG = -12 ∧
     higuchiTotalDoubled icosahedronHG = -36) :=
  ⟨⟨tetrahedron_forman, octahedron_forman, icosahedron_forman⟩,
   ⟨tetrahedron_higuchi, octahedron_higuchi, icosahedron_higuchi⟩⟩

end SphereTriangulationAudit
end InfraFormalization
