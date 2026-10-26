/-
Knill's vertex curvature on triangulated tori.

This module defines `triangulatedTorusHG n`, the n × n grid on the torus with one diagonal in each
square, and shows that `knillEulerScaled` equals 0 = 6 · χ(T²) for `n = 4, 5, 6` and 54 for `n = 3`.
For `n = 3`, the wrapped edges form additional 3-cycles. The values are checked by `native_decide`.
The identity `knillEulerScaled = 6 · (2 − 2g)` for a closed orientable surface of genus `g` is not
proved here.
-/

import InfraFormalization.KnillDiscreteGaussBonnet

namespace InfraFormalization
namespace KnillHigherGenus

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open SphereTriangulationAudit

/-! ## Triangulated torus T²(n, n)

The vertices are the `n²` grid points with indices taken mod `n`. The edges are horizontal, vertical
and diagonal. -/

/-- The triangulated torus `T²(n, n)` as `ExecHG ℕ`, with horizontal, vertical and diagonal edges
`(i, j) – (i + 1, j + 1)`, all indices mod `n`. -/
def triangulatedTorusHG (n : ℕ) : ExecHG ℕ :=
  let nodeId : ℕ → ℕ → ℕ := fun i j => i * n + j
  let horiz : List (Hyperedge ℕ) :=
    (List.range n).flatMap (fun i =>
      (List.range n).map (fun j =>
        ⟨[nodeId i j, nodeId i ((j + 1) % n)], List.cons_ne_nil _ _⟩))
  let vert : List (Hyperedge ℕ) :=
    (List.range n).flatMap (fun i =>
      (List.range n).map (fun j =>
        ⟨[nodeId i j, nodeId ((i + 1) % n) j], List.cons_ne_nil _ _⟩))
  let diag : List (Hyperedge ℕ) :=
    (List.range n).flatMap (fun i =>
      (List.range n).map (fun j =>
        ⟨[nodeId i j, nodeId ((i + 1) % n) ((j + 1) % n)], List.cons_ne_nil _ _⟩))
  horiz ++ vert ++ diag

/-! ## Values of `knillEulerScaled` on T²(n, n)

For `n = 4, 5, 6` the value is 0, checked by `native_decide`. For `n = 3` the value is 54. -/

theorem triangulatedTorus_4_knillEuler :
    knillEulerScaled (triangulatedTorusHG 4) = 0 := by native_decide

theorem triangulatedTorus_5_knillEuler :
    knillEulerScaled (triangulatedTorusHG 5) = 0 := by native_decide

theorem triangulatedTorus_6_knillEuler :
    knillEulerScaled (triangulatedTorusHG 6) = 0 := by native_decide

/-- `knillEulerScaled (triangulatedTorusHG 3) = 54`. For `n = 3`, the wrapped edges form additional
3-cycles. -/
theorem triangulatedTorus_3_knillEuler_special :
    knillEulerScaled (triangulatedTorusHG 3) = 54 := by native_decide

/-! ## The three tori n = 4, 5, 6 -/

/-- `knillEulerScaled (triangulatedTorusHG n) = 0` for `n = 4, 5, 6`. -/
theorem knill_values_torus_triangulations :
    knillEulerScaled (triangulatedTorusHG 4) = 0 ∧
    knillEulerScaled (triangulatedTorusHG 5) = 0 ∧
    knillEulerScaled (triangulatedTorusHG 6) = 0 :=
  ⟨triangulatedTorus_4_knillEuler,
   triangulatedTorus_5_knillEuler,
   triangulatedTorus_6_knillEuler⟩

/-! ## Genus 0 and genus 1 -/

/-- `knillEulerScaled` equals 12 on the three Platonic triangulations of S² and 0 on
`triangulatedTorusHG n` for `n = 4, 5, 6`. -/
theorem knill_genus_zero_one_pattern :
    -- Genus 0 (S²): 6χ = 12 on three Platonic triangulations.
    (knillEulerScaled tetrahedronHG = 12 ∧
     knillEulerScaled octahedronHG = 12 ∧
     knillEulerScaled icosahedronHG = 12) ∧
    -- Genus 1 (T²): 6χ = 0 on triangulated tori with n = 4, 5, 6.
    (knillEulerScaled (triangulatedTorusHG 4) = 0 ∧
     knillEulerScaled (triangulatedTorusHG 5) = 0 ∧
     knillEulerScaled (triangulatedTorusHG 6) = 0) :=
  ⟨knill_recovers_chi_S2, knill_values_torus_triangulations⟩

/-! ## Comparison with the Forman scalar

On the tetrahedron, octahedron and icosahedron, `execFormanScalar` takes the values 48, 48 and 0. -/

/-- `execFormanScalar` equals 48, 48 and 0 on the tetrahedron, octahedron and icosahedron;
`knillEulerScaled` equals 12 on all three and 0 on `triangulatedTorusHG n` for `n = 4, 5, 6`. -/
theorem knill_vs_forman_across_genera :
    -- Forman scalar on the S² triangulations: 48, 48, 0.
    (execFormanScalar tetrahedronHG = 48 ∧
     execFormanScalar octahedronHG = 48 ∧
     execFormanScalar icosahedronHG = 0) ∧
    -- Knill sum on the S² triangulations: 12, 12, 12 = 6·χ(S²).
    (knillEulerScaled tetrahedronHG = 12 ∧
     knillEulerScaled octahedronHG = 12 ∧
     knillEulerScaled icosahedronHG = 12) ∧
    -- Knill sum on the T² triangulations: 0, 0, 0 = 6·χ(T²).
    (knillEulerScaled (triangulatedTorusHG 4) = 0 ∧
     knillEulerScaled (triangulatedTorusHG 5) = 0 ∧
     knillEulerScaled (triangulatedTorusHG 6) = 0) :=
  ⟨⟨SphereTriangulationAudit.tetrahedron_forman,
    SphereTriangulationAudit.octahedron_forman,
    SphereTriangulationAudit.icosahedron_forman⟩,
   knill_recovers_chi_S2,
   knill_values_torus_triangulations⟩

/-! ## Summary

`knillEulerScaled` equals 6χ on three triangulations of S² and on the triangulated tori with
`n = 4, 5, 6`. No genus-2 surface is encoded here. -/

end KnillHigherGenus
end InfraFormalization
