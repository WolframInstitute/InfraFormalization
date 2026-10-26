/-
Further curvature scalars on cycles, and the Forman scalar of the 2D torus.

The module evaluates the doubled Higuchi total, the ordered square count and the scaled degree
variance of `cycleHG n` at sampled `n`, and all three are 0. It defines the 2D torus
`torusHG m n` and evaluates its Forman scalar at `(4,4)`, `(4,5)`, `(5,5)` and `(6,6)`, where it
equals `-16 m n`. All values are checked by `native_decide`.
-/

import InfraFormalization.CycleContinuumLimit
import InfraFormalization.HiguchiScreener
import InfraFormalization.DegreeVarianceScreener
import InfraFormalization.SquareCountScreener
import InfraFormalization.OllivierRicciScreener

namespace InfraFormalization
namespace AdvancedContinuumLimits

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener
open OllivierRicciScreener

/-! ## Further scalars on cycles -/

/-! ### Higuchi total

The per-vertex Higuchi value is `2 − deg v`, which is 0 at every vertex of a cycle. -/

theorem cycleHG_4_higuchi_zero : higuchiTotalDoubled (cycleHG 4) = 0 := by native_decide
theorem cycleHG_5_higuchi_zero : higuchiTotalDoubled (cycleHG 5) = 0 := by native_decide
theorem cycleHG_8_higuchi_zero : higuchiTotalDoubled (cycleHG 8) = 0 := by native_decide
theorem cycleHG_16_higuchi_zero : higuchiTotalDoubled (cycleHG 16) = 0 := by native_decide
theorem cycleHG_32_higuchi_zero : higuchiTotalDoubled (cycleHG 32) = 0 := by native_decide

/-! ### Square count

A cycle with at least 5 vertices contains no 4-cycle. -/

theorem cycleHG_5_squareCount_zero : squareCountOrdered (cycleHG 5) = 0 := by native_decide
theorem cycleHG_6_squareCount_zero : squareCountOrdered (cycleHG 6) = 0 := by native_decide
theorem cycleHG_8_squareCount_zero : squareCountOrdered (cycleHG 8) = 0 := by native_decide
theorem cycleHG_16_squareCount_zero : squareCountOrdered (cycleHG 16) = 0 := by native_decide
theorem cycleHG_32_squareCount_zero : squareCountOrdered (cycleHG 32) = 0 := by native_decide

/-! ### Degree variance

The scaled degree variance is `|V|·Σ deg² − (Σ deg)²`. On the `n`-cycle every degree is 2, so it
equals `n·4n − (2n)² = 0`. -/

theorem cycleHG_4_degVariance_zero : degVarianceScaled (cycleHG 4) = 0 := by native_decide
theorem cycleHG_5_degVariance_zero : degVarianceScaled (cycleHG 5) = 0 := by native_decide
theorem cycleHG_8_degVariance_zero : degVarianceScaled (cycleHG 8) = 0 := by native_decide
theorem cycleHG_16_degVariance_zero : degVarianceScaled (cycleHG 16) = 0 := by native_decide
theorem cycleHG_32_degVariance_zero : degVarianceScaled (cycleHG 32) = 0 := by native_decide

/-! ### Transport scalar

The transport scalar uses the product-coupling upper bound on W₁. On `cycleHG 4` with the trivial
identity rule at depth 0 its trace is `[-64]`. -/

example : (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
            (cycleHG 4) 0).transportScalarTrace = [-64] := by native_decide

/-! ## Forman scalar of the 2D torus

For `n ≥ 4` every vertex of `torusHG n n` has degree 4 and no edge lies on a triangle, so the
doubled per-edge Forman value is `2·(4 − 4 − 4 + 0) = −8`. With `2n²` edges the total is `-16n²`.
The values below are checked by `native_decide`. -/

/-- The 2D torus `T²(m, n)` as `ExecHG ℕ`. Vertices encoded as
`i · n + j` for `i < m`, `j < n`. -/
def torusHG (m n : ℕ) : ExecHG ℕ :=
  let nodeId : ℕ → ℕ → ℕ := fun i j => i * n + j
  let horizEdges : List (Hyperedge ℕ) :=
    (List.range m).flatMap (fun i =>
      (List.range n).map (fun j =>
        ⟨[nodeId i j, nodeId i ((j + 1) % n)], List.cons_ne_nil _ _⟩))
  let vertEdges : List (Hyperedge ℕ) :=
    (List.range m).flatMap (fun i =>
      (List.range n).map (fun j =>
        ⟨[nodeId i j, nodeId ((i + 1) % m) j], List.cons_ne_nil _ _⟩))
  horizEdges ++ vertEdges

/-- T²(4,4) Forman = -256. -/
theorem torus_4_4_forman_neg : execFormanScalar (torusHG 4 4) = -256 := by native_decide

/-- T²(5,5) Forman = -400. -/
theorem torus_5_5_forman_neg : execFormanScalar (torusHG 5 5) = -400 := by native_decide

/-- T²(4,5) Forman = -320. -/
theorem torus_4_5_forman_neg : execFormanScalar (torusHG 4 5) = -320 := by native_decide

/-- T²(6,6) Forman = -576. -/
theorem torus_6_6_forman_neg : execFormanScalar (torusHG 6 6) = -576 := by native_decide

/-- The Forman scalar of `torusHG 4 4` is not 0. -/
theorem torus_forman_not_zero_at_4 : execFormanScalar (torusHG 4 4) ≠ 0 := by
  rw [torus_4_4_forman_neg]; decide

theorem torus_forman_not_zero_at_5 : execFormanScalar (torusHG 5 5) ≠ 0 := by
  rw [torus_5_5_forman_neg]; decide

theorem torus_forman_not_zero_at_6 : execFormanScalar (torusHG 6 6) ≠ 0 := by
  rw [torus_6_6_forman_neg]; decide

/-- The Forman scalars of `torusHG n n` for `n = 4, 5, 6`. -/
def torusFormanSampleTrace : List ℤ :=
  [execFormanScalar (torusHG 4 4),
   execFormanScalar (torusHG 5 5),
   execFormanScalar (torusHG 6 6)]

/-- The sample trace equals `[-256, -400, -576]`. -/
theorem torusFormanSampleTrace_eq :
    torusFormanSampleTrace = [-256, -400, -576] := by
  show [execFormanScalar (torusHG 4 4), execFormanScalar (torusHG 5 5),
        execFormanScalar (torusHG 6 6)] = [-256, -400, -576]
  rw [torus_4_4_forman_neg, torus_5_5_forman_neg, torus_6_6_forman_neg]

/-! ## Forman scalar of the torus is non-zero

In a triangle-free `d`-regular graph the undoubled per-edge Forman value is `4 − 2d`: 0 for
`d = 2`, `-4` for `d = 4`, `-8` for `d = 6`. -/

/-- The Forman scalars of `torusHG 4 4`, `torusHG 5 5` and `torusHG 6 6` are non-zero. -/
theorem torus_forman_nonzero_at_4_5_6 :
    execFormanScalar (torusHG 4 4) ≠ 0 ∧
    execFormanScalar (torusHG 5 5) ≠ 0 ∧
    execFormanScalar (torusHG 6 6) ≠ 0 := by
  refine ⟨torus_forman_not_zero_at_4, torus_forman_not_zero_at_5,
          torus_forman_not_zero_at_6⟩

/-- The Forman scalar of `torusHG 4 4` equals `-8 · 32`. The graph has 32 edges and the doubled
per-edge value is -8. -/
theorem torus_4_4_forman_eq_neg8_mul_32 :
    execFormanScalar (torusHG 4 4) = -8 * 32 := by native_decide

end AdvancedContinuumLimits
end InfraFormalization
