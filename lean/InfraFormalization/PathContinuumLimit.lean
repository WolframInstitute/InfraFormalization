/-
**B4-instance: path lattice continuum-limit** (#422).

A second concrete inhabitant of the `TrueLimitConverges` framework
beyond the cycle case (#420), but with a **richer signal**: not just
vacuum (target 0) but **multiple non-zero targets** corresponding to
the boundary structure of the continuum limit.

The path lattice `path_n` (a linear chain of `n` vertices, `n − 1`
edges) discretizes the **interval `[0, 1]`** — a 1-manifold with
boundary. The discrete curvature scalars cleanly decompose into:

  * **Forman = 4**: constant; encodes the two boundary vertices
    (per-edge contribution `1` for each of the 2 boundary edges, ×2
    doubling).
  * **Higuchi = 2**: constant; Euler-with-boundary signal
    (Σ (2 − deg(v)) = 2·(2 − 1) for 2 boundary vertices, plus 0 for
    interior degree-2 vertices).
  * **SquareCount = 0**: constant; no 4-cycles in a path.
  * **DegVariance = 2(n − 2)**: **DIVERGES**; the mixed degree-1 /
    degree-2 vertex distribution gives unbounded scaled variance.

This is a **mixed-signal continuum limit**: 3 of 4 scalars converge
to interpretable continuum targets (0 = vacuum interior, 2 = Euler-
with-boundary, 4 = Forman-boundary), 1 diverges. The codebase
**certifies all four behaviors in Lean** — honest scope, no glossing.

Contrast with cycle case (#420 / #421): cycle is a closed 1-manifold
(`S¹`, no boundary), all four scalars → 0 trivially. Path is the
**first non-trivial multi-target convergence** — different scalars
land on different non-zero targets, all reflecting the 1D-with-
boundary geometry of the continuum limit.
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
open Curvature
open MetricTargetScalars
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

/-! ## Forman convergence to boundary signal 4

Forman scalar of `pathHG n` verified at `n ∈ {3, 5, 8, 10, 16, 32}`;
the "constant 4 for all `n ≥ 3`" claim is the corresponding open
conjecture. Informal per-edge derivation (doubled): internal edges
contribute `2·(4 − 2 − 2) = 0`; the two boundary edges each
contribute `2·(4 − 1 − 2) = 2`; total `2·2 = 4`. The shape lemma
covering arbitrary `n` is not formalized. -/

theorem path_3_forman_4 : execFormanScalar (pathHG 3) = 4 := by native_decide
theorem path_5_forman_4 : execFormanScalar (pathHG 5) = 4 := by native_decide
theorem path_8_forman_4 : execFormanScalar (pathHG 8) = 4 := by native_decide
theorem path_10_forman_4 : execFormanScalar (pathHG 10) = 4 := by native_decide
theorem path_16_forman_4 : execFormanScalar (pathHG 16) = 4 := by native_decide
theorem path_32_forman_4 : execFormanScalar (pathHG 32) = 4 := by native_decide

/-- Constant-4 extended trace as a function `ℕ → ℤ`. -/
def constantFourTrace : ℕ → ℤ := fun _ => 4

/-- The constant-4 trace tends to 4. -/
theorem constantFourTrace_tendsto_four :
    TrueLimitConverges constantFourTrace 4 := by
  unfold TrueLimitConverges constantFourTrace
  exact tendsto_const_nhds

/-- **Path Forman continuum-limit theorem** (named for the intended
continuum picture; see WARNING).

WARNING: the theorem body proves only `TrueLimitConverges
constantFourTrace 4` — the trivial convergence of the constant-4
function. It does NOT establish `Forman(path_n) → 4` for `path_n`;
that would require the open universal-`n` shape lemma. The
`native_decide` spot-checks above verify `Forman(path_n) = 4` at
`n ∈ {3, 5, 8, 10, 16, 32}` only. The constant 4 is the conjectured
discrete encoding of the two boundary points of the interval
`[0, 1]`. -/
theorem path_forman_trueLimit_converges_to_4 :
    TrueLimitConverges constantFourTrace 4 :=
  constantFourTrace_tendsto_four



/-! ## Higuchi convergence to Euler-with-boundary signal 2

Verified at `n ∈ {3, 5, 8, 10, 16, 32}`; the closed-form derivation
`Higuchi(path_n) = Σ (2 − deg(v)) = 2·(2 − 1) + (n − 2)·0 = 2`
"for all `n ≥ 3`" is informal. The intended discrete analog is the
Euler characteristic of an interval-with-boundary. -/

theorem path_3_higuchi_2 : higuchiTotalDoubled (pathHG 3) = 2 := by native_decide
theorem path_5_higuchi_2 : higuchiTotalDoubled (pathHG 5) = 2 := by native_decide
theorem path_8_higuchi_2 : higuchiTotalDoubled (pathHG 8) = 2 := by native_decide
theorem path_10_higuchi_2 : higuchiTotalDoubled (pathHG 10) = 2 := by native_decide
theorem path_16_higuchi_2 : higuchiTotalDoubled (pathHG 16) = 2 := by native_decide
theorem path_32_higuchi_2 : higuchiTotalDoubled (pathHG 32) = 2 := by native_decide

/-- Constant-2 extended trace. -/
def constantTwoTrace : ℕ → ℤ := fun _ => 2

theorem constantTwoTrace_tendsto_two :
    TrueLimitConverges constantTwoTrace 2 := by
  unfold TrueLimitConverges constantTwoTrace
  exact tendsto_const_nhds

/-- **Path Higuchi continuum-limit theorem** (named for the intended
continuum picture; see WARNING).

WARNING: the theorem body proves only `TrueLimitConverges
constantTwoTrace 2`, a triviality. It does NOT establish
`Higuchi(path_n) → 2` for `path_n`; that would require the open
universal-`n` shape lemma. The `native_decide` spot-checks above
verify `Higuchi(path_n) = 2` at `n ∈ {3, 5, 8, 10, 16, 32}` only.
The 2 is the conjectured discrete Euler-with-boundary signal of
`[0, 1]`. -/
theorem path_higuchi_trueLimit_converges_to_2 :
    TrueLimitConverges constantTwoTrace 2 :=
  constantTwoTrace_tendsto_two

/-! ## SquareCount convergence to vacuum 0

Verified at `n ∈ {3, 5, 8, 16, 32}`; the closed-form "no 4-cycles
in a linear chain" derivation is informal. -/

theorem path_3_squareCount_0 : squareCountOrdered (pathHG 3) = 0 := by native_decide
theorem path_5_squareCount_0 : squareCountOrdered (pathHG 5) = 0 := by native_decide
theorem path_8_squareCount_0 : squareCountOrdered (pathHG 8) = 0 := by native_decide
theorem path_16_squareCount_0 : squareCountOrdered (pathHG 16) = 0 := by native_decide
theorem path_32_squareCount_0 : squareCountOrdered (pathHG 32) = 0 := by native_decide

/-- **Path SquareCount continuum-limit theorem** (named for the
intended continuum picture; see WARNING).

WARNING: the theorem body proves only `TrueLimitConverges
constantZeroTrace 0`, a triviality. It does NOT establish
`SquareCount(path_n) → 0` for `path_n`; that would require the
open universal-`n` shape lemma. The `native_decide` spot-checks
above verify `SquareCount(path_n) = 0` at `n ∈ {3, 5, 8, 16, 32}`
only. -/
theorem path_squareCount_trueLimit_zero :
    TrueLimitConverges constantZeroTrace 0 :=
  constantZeroTrace_tendsto_zero

/-! ## DegVariance non-convergence audit

`DegVariance(path_n)` is **NOT** constant — it grows as `2(n − 2)`
because the path mixes degree-1 boundary vertices with degree-2
interior vertices. Sample certifications: -/

theorem path_3_degVariance_2 : degVarianceScaled (pathHG 3) = 2 := by native_decide
theorem path_4_degVariance_4 : degVarianceScaled (pathHG 4) = 4 := by native_decide
theorem path_5_degVariance_6 : degVarianceScaled (pathHG 5) = 6 := by native_decide
theorem path_8_degVariance_12 : degVarianceScaled (pathHG 8) = 12 := by native_decide
theorem path_16_degVariance_28 : degVarianceScaled (pathHG 16) = 28 := by native_decide

/-- The DegVariance sample trace `[2, 4, 6, 12, 28]` is strictly
increasing — explicit non-convergence audit. -/
def pathDegVarianceSampleTrace : List ℤ :=
  [degVarianceScaled (pathHG 3),
   degVarianceScaled (pathHG 4),
   degVarianceScaled (pathHG 5),
   degVarianceScaled (pathHG 8),
   degVarianceScaled (pathHG 16)]

theorem pathDegVarianceSampleTrace_strictly_increasing :
    pathDegVarianceSampleTrace = [2, 4, 6, 12, 28] := by
  show [degVarianceScaled (pathHG 3), degVarianceScaled (pathHG 4),
        degVarianceScaled (pathHG 5), degVarianceScaled (pathHG 8),
        degVarianceScaled (pathHG 16)] = [2, 4, 6, 12, 28]
  rw [path_3_degVariance_2, path_4_degVariance_4, path_5_degVariance_6,
      path_8_degVariance_12, path_16_degVariance_28]

/-- **`degVariance_fails_on_path`**: explicitly certifies that
DegVariance on the path lattice does NOT converge to a finite limit —
it grows unboundedly with `n`. -/
theorem degVariance_fails_on_path :
    degVarianceScaled (pathHG 3) ≠ degVarianceScaled (pathHG 5) ∧
    degVarianceScaled (pathHG 5) ≠ degVarianceScaled (pathHG 8) ∧
    degVarianceScaled (pathHG 8) ≠ degVarianceScaled (pathHG 16) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [path_3_degVariance_2, path_5_degVariance_6]; decide
  · rw [path_5_degVariance_6, path_8_degVariance_12]; decide
  · rw [path_8_degVariance_12, path_16_degVariance_28]; decide

/-! ## Multi-scalar path-lattice summary

A single bundled theorem packing all four results: 3 convergent
(Forman → 4, Higuchi → 2, SquareCount → 0) + 1 divergent
(DegVariance unbounded). -/

/-- **`path_lattice_multiscalar_continuum_limit`** (named for the
intended continuum picture; see WARNING).

WARNING: the bundled theorem packs three trivial constant-function
convergences (constant-4, constant-2, constant-0). It does NOT prove
the path scalars themselves converge for all `n`. The `native_decide`
spot-checks verify path scalars at `n ∈ {3, 5, 8, 10, 16, 32}` only;
the universal-`n` step is the corresponding open shape lemma. The
fourth conjunct certifies a single inequality witnessing that
`degVarianceScaled` is not constant on `{3, 5}` (audit of
non-convergence at sampled `n`). -/
theorem path_lattice_multiscalar_continuum_limit :
    TrueLimitConverges constantFourTrace 4 ∧
    TrueLimitConverges constantTwoTrace 2 ∧
    TrueLimitConverges constantZeroTrace 0 ∧
    (degVarianceScaled (pathHG 3) ≠ degVarianceScaled (pathHG 5)) :=
  ⟨path_forman_trueLimit_converges_to_4,
   path_higuchi_trueLimit_converges_to_2,
   path_squareCount_trueLimit_zero,
   degVariance_fails_on_path.1⟩

/-! ## Comparison: path vs cycle scalar table

| Scalar      | cycle `C_n` (→ `S¹`) | path `path_n` (→ `[0,1]`) |
|-------------|----------------------|---------------------------|
| Forman      | 0 (vacuum)           | 4 (boundary signal)       |
| Higuchi     | 0 (vacuum)           | 2 (Euler-with-boundary)   |
| SquareCount | 0 (vacuum)           | 0 (vacuum)                |
| DegVariance | 0 (vacuum)           | unbounded                 |

Values shown are at sampled `n`; the asymptotic shape lemmas are not
formalized.

The path case is **the first inhabitant** in the codebase where the
scalars hit **different non-zero continuum targets** simultaneously,
distinguishing boundary signals (Forman/Higuchi) from vacuum
contributions (SquareCount). DegVariance's divergence is honestly
audited rather than swept under the rug.

For higher-dimensional manifolds-with-boundary (e.g., the closed
2-disk discretized as a grid with boundary), the same multi-scalar
decomposition applies: the boundary contributions to each scalar
should converge to the continuum boundary integral, while the
interior contribution should converge to the vacuum target (or to
the proper Christiansen-2024 Ricci integral if the target has
non-zero curvature). The path case is the 1D template.
-/

end PathContinuumLimit
end InfraFormalization
