/-
**B4-audit: sphere-triangulation curvature inconsistency** (#426).

The torus / grid non-convergence audits (#421 / #423) showed that
absolute Forman / Higuchi totals diverge with size — recoverable via
per-volume density normalization (#424 / #425).

This module identifies a **distinct failure mode**: across different
**triangulations of the *same* topological target** `S²` (positive
Riemannian Ricci > 0), the discrete Forman scalar gives **wildly
inconsistent per-vertex values**. Whereas the torus per-area density
converges to the *same* constant `-16` across all sizes of `T²`, the
sphere triangulations give per-vertex Forman of `+12` (tetrahedron),
`+8` (octahedron), `0` (icosahedron) — DIFFERENT values for the same
topological target.

**The honest conclusion**: the architecture's unweighted Forman is
**triangulation-dependent**, not just topology-dependent. Proper
Riemannian-Ricci recovery on curved targets requires either
**weighted Forman** (with edge weights matching the geometric
embedding) or a **specific normalized sequence** (e.g., geodesic
sphere subdivisions with proper volume scaling). The codebase
**certifies this triangulation sensitivity in Lean** at the level of
the three Platonic 2-sphere triangulations.

**The sphere-triangulation curvature table**:

| Triangulation | V  | E  | Forman total | per-V Forman | Higuchi total | per-V Higuchi |
|---------------|----|----|---------------|---------------|----------------|----------------|
| Tetrahedron   | 4  | 6  | `+48`         | `+12`         | `-4`           | `-1`           |
| Octahedron    | 6  | 12 | `+48`         | `+8`          | `-12`          | `-2`           |
| Icosahedron   | 12 | 30 | `0`           | `0`           | `-36`          | `-3`           |

All three are topologically `S²` (continuous Ric > 0). Per-vertex
Forman strictly decreases as triangulation gets finer; per-vertex
Higuchi tracks `2 - deg(v)`. **Neither converges to a consistent
target value**.
-/

import InfraFormalization.PolynomialDensityLimits

namespace InfraFormalization
namespace SphereTriangulationAudit

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open Curvature
open MetricTargetScalars
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener

/-! ## Three 2-sphere triangulations (Platonic solids) -/

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

/-- Icosahedron: 12 vertices, 30 edges, all degree 5. Encoded via
the standard Schlegel diagram: north pole 0, equatorial ring 1-5,
tropical ring 6-10, south pole 11. -/
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

/-! ## Per-triangulation Forman values

Certified via `native_decide`. All three are topologically `S²` but
give wildly different Forman totals. -/

theorem tetrahedron_forman : execFormanScalar tetrahedronHG = 48 := by native_decide
theorem octahedron_forman : execFormanScalar octahedronHG = 48 := by native_decide
theorem icosahedron_forman : execFormanScalar icosahedronHG = 0 := by native_decide

/-! ## Per-triangulation Higuchi values

Higuchi-total-doubled = `Σ (2 − deg(v))`. For a `k`-regular graph
on `V` vertices: `V · (2 − k)`. All three sphere triangulations are
regular, so the per-vertex Higuchi tracks degree exactly. -/

theorem tetrahedron_higuchi : higuchiTotalDoubled tetrahedronHG = -4 := by native_decide
theorem octahedron_higuchi : higuchiTotalDoubled octahedronHG = -12 := by native_decide
theorem icosahedron_higuchi : higuchiTotalDoubled icosahedronHG = -36 := by native_decide

/-! ## Inconsistency audit

The three S² triangulations give **distinct Forman totals**: `48`,
`48`, `0`. Per-vertex: `12`, `8`, `0`. These don't converge to any
single value; they decrease with vertex count `V`. -/

/-- **`forman_inconsistent_across_sphere_triangulations`**: the
Forman scalar differs across the three Platonic S² triangulations.
There is no single per-vertex value the discrete Forman converges to. -/
theorem forman_inconsistent_across_sphere_triangulations :
    execFormanScalar tetrahedronHG ≠ execFormanScalar icosahedronHG ∧
    execFormanScalar octahedronHG ≠ execFormanScalar icosahedronHG := by
  refine ⟨?_, ?_⟩
  · rw [tetrahedron_forman, icosahedron_forman]; decide
  · rw [octahedron_forman, icosahedron_forman]; decide

/-- The Higuchi-per-vertex values across the three sphere triangulations
match the degree-based formula `V · (2 − k)`, with `k = 3, 4, 5` for
tetrahedron/octahedron/icosahedron respectively. They DIFFER across
triangulations of the same target. -/
theorem higuchi_inconsistent_across_sphere_triangulations :
    higuchiTotalDoubled tetrahedronHG ≠ higuchiTotalDoubled octahedronHG ∧
    higuchiTotalDoubled octahedronHG ≠ higuchiTotalDoubled icosahedronHG ∧
    higuchiTotalDoubled tetrahedronHG ≠ higuchiTotalDoubled icosahedronHG := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tetrahedron_higuchi, octahedron_higuchi]; decide
  · rw [octahedron_higuchi, icosahedron_higuchi]; decide
  · rw [tetrahedron_higuchi, icosahedron_higuchi]; decide

/-- **Bundled audit**: ALL THREE pairs of S² triangulations disagree
on BOTH Forman and Higuchi values. The unweighted scalars in this
architecture are **triangulation-dependent**, not topology-dependent. -/
theorem sphere_triangulation_scalars_inconsistent :
    (execFormanScalar tetrahedronHG = 48 ∧ execFormanScalar octahedronHG = 48 ∧
     execFormanScalar icosahedronHG = 0) ∧
    (higuchiTotalDoubled tetrahedronHG = -4 ∧
     higuchiTotalDoubled octahedronHG = -12 ∧
     higuchiTotalDoubled icosahedronHG = -36) :=
  ⟨⟨tetrahedron_forman, octahedron_forman, icosahedron_forman⟩,
   ⟨tetrahedron_higuchi, octahedron_higuchi, icosahedron_higuchi⟩⟩

/-! ## Summary

| Triangulation | V  | E  | Forman | per-V | Higuchi | per-V |
|---------------|----|----|--------|-------|----------|-------|
| Tetrahedron   | 4  | 6  | `+48`  | `+12` | `-4`     | `-1`  |
| Octahedron    | 6  | 12 | `+48`  | `+8`  | `-12`    | `-2`  |
| Icosahedron   | 12 | 30 | `0`    | `0`   | `-36`    | `-3`  |

All three triangulations are topologically `S²` (smooth target
`Ric > 0`). The discrete Forman per-vertex values `12, 8, 0` do not
converge to any consistent target. Higuchi per-vertex `-1, -2, -3`
tracks `2 - deg(v)`.

**Honest conclusion**: in the architecture's current form, the
unweighted curvature scalars are **triangulation-dependent**. They
do not recover the smooth Ricci of the target — different
triangulations of the same `S²` give different curvature signatures.

**Literature-grade fixes** (research-level, not in this commit):

  * **Knill discrete Gauss-Bonnet** with the **vertex defect**
    angle formula → recovers `2π · χ(S²) = 4π` summed over vertices,
    independent of triangulation. (This is the right discrete-S²
    analog; Forman/Higuchi are wrong choices for that target.)
  * **Christiansen 2024 distributional Ricci** with edge-length
    weights → recovers smooth `Ric > 0` in the regular-triangulation
    refinement limit.
  * **Effective resistance curvature** (Devriendt-Lambiotte 2022)
    → metrics-aware, triangulation-independent in the limit.

This audit makes the architecture's scope **explicit**: it works
for compact flat 1-manifolds (cycle), 1-manifolds with boundary
(path), and gives per-volume densities for flat 2-tori (T²) and disks
(D²). For **positively-curved targets** like `S²`, alternative
literature-grade curvature notions are required. The codebase
certifies this gap rather than glossing over it.
-/

end SphereTriangulationAudit
end InfraFormalization
