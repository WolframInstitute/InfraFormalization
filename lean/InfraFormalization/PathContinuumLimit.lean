/-
Curvature scalars of the path hypergraph.

The module defines the path `pathHG n` with `n` vertices and `n − 1` edges and evaluates four
scalars on it at sampled sizes, each value checked by `native_decide`: the Forman scalar is 4,
the doubled Higuchi total is 2, the ordered square count is 0, and the scaled degree variance takes
the values 2, 4, 6, 12, 28 at `n = 3, 4, 5, 8, 16`. Closed forms for arbitrary `n` are not
formalized.
-/

import InfraFormalization.CycleContinuumLimit
import InfraFormalization.HiguchiScreener
import InfraFormalization.DegreeVarianceScreener
import InfraFormalization.SquareCountScreener
import InfraFormalization.OllivierRicciScreener

namespace InfraFormalization
namespace PathContinuumLimit

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener
open OllivierRicciScreener

/-- The path lattice `path_n` with `n` vertices and `n − 1` edges
encoded as the linear chain `0 — 1 — 2 — ⋯ — (n−1)`. Edges are
directed `i → i+1`. -/
def pathHG (n : ℕ) : ExecHG ℕ :=
  (List.range (n - 1)).map (fun i =>
    ⟨[i, i + 1], List.cons_ne_nil _ _⟩)

/-! ## Forman scalar

`execFormanScalar (pathHG n) = 4` for `n ∈ {3, 5, 8, 10, 16, 32}`. In the doubled per-edge
count, each interior edge contributes `2·(4 − 2 − 2) = 0` and each of the two end edges contributes
`2·(4 − 1 − 2) = 2`. -/

theorem path_3_forman_4 : execFormanScalar (pathHG 3) = 4 := by native_decide
theorem path_5_forman_4 : execFormanScalar (pathHG 5) = 4 := by native_decide
theorem path_8_forman_4 : execFormanScalar (pathHG 8) = 4 := by native_decide
theorem path_10_forman_4 : execFormanScalar (pathHG 10) = 4 := by native_decide
theorem path_16_forman_4 : execFormanScalar (pathHG 16) = 4 := by native_decide
theorem path_32_forman_4 : execFormanScalar (pathHG 32) = 4 := by native_decide

/-! ## Higuchi total

`higuchiTotalDoubled (pathHG n) = 2` for `n ∈ {3, 5, 8, 10, 16, 32}`. The informal count is
`Σ (2 − deg v) = 2·(2 − 1) + (n − 2)·0 = 2`. -/

theorem path_3_higuchi_2 : higuchiTotalDoubled (pathHG 3) = 2 := by native_decide
theorem path_5_higuchi_2 : higuchiTotalDoubled (pathHG 5) = 2 := by native_decide
theorem path_8_higuchi_2 : higuchiTotalDoubled (pathHG 8) = 2 := by native_decide
theorem path_10_higuchi_2 : higuchiTotalDoubled (pathHG 10) = 2 := by native_decide
theorem path_16_higuchi_2 : higuchiTotalDoubled (pathHG 16) = 2 := by native_decide
theorem path_32_higuchi_2 : higuchiTotalDoubled (pathHG 32) = 2 := by native_decide

/-! ## Square count

`squareCountOrdered (pathHG n) = 0` for `n ∈ {3, 5, 8, 16, 32}`. -/

theorem path_3_squareCount_0 : squareCountOrdered (pathHG 3) = 0 := by native_decide
theorem path_5_squareCount_0 : squareCountOrdered (pathHG 5) = 0 := by native_decide
theorem path_8_squareCount_0 : squareCountOrdered (pathHG 8) = 0 := by native_decide
theorem path_16_squareCount_0 : squareCountOrdered (pathHG 16) = 0 := by native_decide
theorem path_32_squareCount_0 : squareCountOrdered (pathHG 32) = 0 := by native_decide

/-! ## Degree variance

`degVarianceScaled (pathHG n)` equals `2(n − 2)` at `n ∈ {3, 4, 5, 8, 16}`. -/

theorem path_3_degVariance_2 : degVarianceScaled (pathHG 3) = 2 := by native_decide
theorem path_4_degVariance_4 : degVarianceScaled (pathHG 4) = 4 := by native_decide
theorem path_5_degVariance_6 : degVarianceScaled (pathHG 5) = 6 := by native_decide
theorem path_8_degVariance_12 : degVarianceScaled (pathHG 8) = 12 := by native_decide
theorem path_16_degVariance_28 : degVarianceScaled (pathHG 16) = 28 := by native_decide

/-- The list of `degVarianceScaled (pathHG n)` for `n = 3, 4, 5, 8, 16`. -/
def pathDegVarianceSampleTrace : List ℤ :=
  [degVarianceScaled (pathHG 3),
   degVarianceScaled (pathHG 4),
   degVarianceScaled (pathHG 5),
   degVarianceScaled (pathHG 8),
   degVarianceScaled (pathHG 16)]

theorem pathDegVarianceSampleTrace_eq :
    pathDegVarianceSampleTrace = [2, 4, 6, 12, 28] := by
  show [degVarianceScaled (pathHG 3), degVarianceScaled (pathHG 4),
        degVarianceScaled (pathHG 5), degVarianceScaled (pathHG 8),
        degVarianceScaled (pathHG 16)] = [2, 4, 6, 12, 28]
  rw [path_3_degVariance_2, path_4_degVariance_4, path_5_degVariance_6,
      path_8_degVariance_12, path_16_degVariance_28]

/-- The scaled degree variances of `pathHG 3`, `pathHG 5`, `pathHG 8` and `pathHG 16` are
pairwise distinct in consecutive order. -/
theorem path_degVariance_values_differ :
    degVarianceScaled (pathHG 3) ≠ degVarianceScaled (pathHG 5) ∧
    degVarianceScaled (pathHG 5) ≠ degVarianceScaled (pathHG 8) ∧
    degVarianceScaled (pathHG 8) ≠ degVarianceScaled (pathHG 16) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [path_3_degVariance_2, path_5_degVariance_6]; decide
  · rw [path_5_degVariance_6, path_8_degVariance_12]; decide
  · rw [path_8_degVariance_12, path_16_degVariance_28]; decide

end PathContinuumLimit
end InfraFormalization
