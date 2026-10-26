/-
Curvature scalars of the 2D open grid.

The module defines the open `m × n` grid `gridHG m n` without wraparound and evaluates four
scalars on `gridHG n n` at sampled `n`: the Forman scalar, the doubled Higuchi total, the ordered
square count and the scaled degree variance. Each value is checked by `native_decide`, and all
values are non-zero.
-/

import InfraFormalization.CycleContinuumLimit
import InfraFormalization.HiguchiScreener
import InfraFormalization.DegreeVarianceScreener
import InfraFormalization.SquareCountScreener
import InfraFormalization.OllivierRicciScreener

namespace InfraFormalization
namespace GridContinuumLimit

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener
open OllivierRicciScreener

/-- The 2D open grid `gridHG m n` as `ExecHG ℕ`. Vertices encoded
as `i · n + j` for `i ∈ {0..m-1}, j ∈ {0..n-1}`. Edges: horizontal
`(i, j) → (i, j+1)` and vertical `(i, j) → (i+1, j)`, with no
wraparound. -/
def gridHG (m n : ℕ) : ExecHG ℕ :=
  let nodeId : ℕ → ℕ → ℕ := fun i j => i * n + j
  let horiz : List (Hyperedge ℕ) :=
    (List.range m).flatMap (fun i =>
      (List.range (n - 1)).map (fun j =>
        ⟨[nodeId i j, nodeId i (j + 1)], List.cons_ne_nil _ _⟩))
  let vert : List (Hyperedge ℕ) :=
    (List.range (m - 1)).flatMap (fun i =>
      (List.range n).map (fun j =>
        ⟨[nodeId i j, nodeId (i + 1) j], List.cons_ne_nil _ _⟩))
  horiz ++ vert

/-! ## Forman scalar

`execFormanScalar (gridHG n n)` equals -40, -112, -216, -352 at `n = 3, 4, 5, 6`. -/

theorem grid_3_3_forman_neg : execFormanScalar (gridHG 3 3) = -40 := by native_decide
theorem grid_4_4_forman_neg : execFormanScalar (gridHG 4 4) = -112 := by native_decide
theorem grid_5_5_forman_neg : execFormanScalar (gridHG 5 5) = -216 := by native_decide
theorem grid_6_6_forman_neg : execFormanScalar (gridHG 6 6) = -352 := by native_decide

/-- The Forman scalars of `gridHG n n` for `n = 3, 4, 5, 6`. -/
def gridFormanSampleTrace : List ℤ :=
  [execFormanScalar (gridHG 3 3),
   execFormanScalar (gridHG 4 4),
   execFormanScalar (gridHG 5 5),
   execFormanScalar (gridHG 6 6)]

theorem gridFormanSampleTrace_eq :
    gridFormanSampleTrace = [-40, -112, -216, -352] := by
  show [execFormanScalar (gridHG 3 3), execFormanScalar (gridHG 4 4),
        execFormanScalar (gridHG 5 5), execFormanScalar (gridHG 6 6)]
       = [-40, -112, -216, -352]
  rw [grid_3_3_forman_neg, grid_4_4_forman_neg, grid_5_5_forman_neg,
      grid_6_6_forman_neg]

/-- The Forman scalar of `gridHG n n` is non-zero for `n = 3, 4, 5, 6`. -/
theorem grid_forman_nonzero_at_samples :
    execFormanScalar (gridHG 3 3) ≠ 0 ∧
    execFormanScalar (gridHG 4 4) ≠ 0 ∧
    execFormanScalar (gridHG 5 5) ≠ 0 ∧
    execFormanScalar (gridHG 6 6) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [grid_3_3_forman_neg]; decide
  · rw [grid_4_4_forman_neg]; decide
  · rw [grid_5_5_forman_neg]; decide
  · rw [grid_6_6_forman_neg]; decide

/-! ## Higuchi total

`higuchiTotalDoubled (gridHG n n)` equals -6, -16, -30, -48 at `n = 3, 4, 5, 6`. Each interior
vertex has degree 4 and contributes `2 − 4 = −2`. -/

theorem grid_3_3_higuchi_neg : higuchiTotalDoubled (gridHG 3 3) = -6 := by native_decide
theorem grid_4_4_higuchi_neg : higuchiTotalDoubled (gridHG 4 4) = -16 := by native_decide
theorem grid_5_5_higuchi_neg : higuchiTotalDoubled (gridHG 5 5) = -30 := by native_decide
theorem grid_6_6_higuchi_neg : higuchiTotalDoubled (gridHG 6 6) = -48 := by native_decide

def gridHiguchiSampleTrace : List ℤ :=
  [higuchiTotalDoubled (gridHG 3 3),
   higuchiTotalDoubled (gridHG 4 4),
   higuchiTotalDoubled (gridHG 5 5),
   higuchiTotalDoubled (gridHG 6 6)]

theorem gridHiguchiSampleTrace_eq :
    gridHiguchiSampleTrace = [-6, -16, -30, -48] := by
  show [higuchiTotalDoubled (gridHG 3 3), higuchiTotalDoubled (gridHG 4 4),
        higuchiTotalDoubled (gridHG 5 5), higuchiTotalDoubled (gridHG 6 6)]
       = [-6, -16, -30, -48]
  rw [grid_3_3_higuchi_neg, grid_4_4_higuchi_neg, grid_5_5_higuchi_neg,
      grid_6_6_higuchi_neg]

/-! ## Square count

`squareCountOrdered (gridHG n n)` equals 32, 72, 128 at `n = 3, 4, 5`, which is `8(n − 1)²`: each
of the `(n − 1)²` unit squares is counted 8 times. -/

theorem grid_3_3_squareCount_pos : squareCountOrdered (gridHG 3 3) = 32 := by native_decide
theorem grid_4_4_squareCount_pos : squareCountOrdered (gridHG 4 4) = 72 := by native_decide
theorem grid_5_5_squareCount_pos : squareCountOrdered (gridHG 5 5) = 128 := by native_decide

def gridSquareCountSampleTrace : List ℤ :=
  [squareCountOrdered (gridHG 3 3),
   squareCountOrdered (gridHG 4 4),
   squareCountOrdered (gridHG 5 5)]

theorem gridSquareCountSampleTrace_eq :
    gridSquareCountSampleTrace = [32, 72, 128] := by
  show [squareCountOrdered (gridHG 3 3), squareCountOrdered (gridHG 4 4),
        squareCountOrdered (gridHG 5 5)] = [32, 72, 128]
  rw [grid_3_3_squareCount_pos, grid_4_4_squareCount_pos,
      grid_5_5_squareCount_pos]

/-! ## Degree variance

`degVarianceScaled (gridHG n n)` equals 36, 128, 300 at `n = 3, 4, 5`. The grid has corner vertices
of degree 2, boundary vertices of degree 3 and interior vertices of degree 4. -/

theorem grid_3_3_degVariance_pos : degVarianceScaled (gridHG 3 3) = 36 := by native_decide
theorem grid_4_4_degVariance_pos : degVarianceScaled (gridHG 4 4) = 128 := by native_decide
theorem grid_5_5_degVariance_pos : degVarianceScaled (gridHG 5 5) = 300 := by native_decide

/-- The Forman scalar, doubled Higuchi total, ordered square count and scaled degree variance
of `gridHG 4 4` are all non-zero. -/
theorem grid_4_4_scalars_nonzero :
    execFormanScalar (gridHG 4 4) ≠ 0 ∧
    higuchiTotalDoubled (gridHG 4 4) ≠ 0 ∧
    squareCountOrdered (gridHG 4 4) ≠ 0 ∧
    degVarianceScaled (gridHG 4 4) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [grid_4_4_forman_neg]; decide
  · rw [grid_4_4_higuchi_neg]; decide
  · rw [grid_4_4_squareCount_pos]; decide
  · rw [grid_4_4_degVariance_pos]; decide

end GridContinuumLimit
end InfraFormalization
