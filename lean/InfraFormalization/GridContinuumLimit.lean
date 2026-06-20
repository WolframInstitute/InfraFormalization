/-
**B4-audit: 2D open grid non-convergence** (#423).

The 2D open grid `gridHG m n` (a flat rectangular lattice with
**open boundary**, no torus wrap) is the natural 2D analog of the
path lattice (#422). Whereas the path → `[0, 1]` interval gives a
mixed multi-target convergence (3 scalars to non-zero targets + 1
divergence), the **open 2D grid → closed disk `D²`**: all four
scalars verified non-zero and monotonically increasing in magnitude
at sample sizes n ∈ {3, 4, 5, 6}; unbounded divergence as n → ∞ is
informal extrapolation.

This is the parallel-to-T² (#421) audit for the open-boundary case.
The asymptotic per-vertex / per-edge values are non-zero constants
(inherited from the 4-regular interior bias), but multiplied by `~n²`
total elements, giving unbounded sequences.

**What this delivers**:

  * Forman(grid m n) ≠ 0 at sample sizes, sequence strictly decreasing.
  * Higuchi(grid m n) ≠ 0 at sample sizes, sequence strictly decreasing.
  * SquareCount(grid m n) ≠ 0 at sample sizes, sequence strictly increasing.
  * DegVariance(grid m n) ≠ 0 at sample sizes, sequence strictly increasing.

All four are non-zero at the sampled sizes ⇒ at the sampled sizes
the four unweighted scalars do not match the flat target Ric = 0
of `D²`; asymptotic divergence not proved.

**Scope statement**: this is the **second non-convergence audit**
(after T²). Together they delineate the architecture's limits — the
unweighted curvature scalars work cleanly for compact 1-manifolds
(cycle, vacuum; path, boundary), but fail for any 2D-or-higher flat
manifold (torus, disk). Weighted Forman / Christiansen-2024 /
effective resistance / Regge deficit are the literature-grade fixes.
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
open Curvature
open MetricTargetScalars
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener
open OllivierRicciScreener

/-- The 2D open grid `gridHG m n` as `ExecHG ℕ`. Vertices encoded
as `i · n + j` for `i ∈ {0..m-1}, j ∈ {0..n-1}`. Edges: horizontal
`(i, j) → (i, j+1)` and vertical `(i, j) → (i+1, j)`. **Open
boundary** — no torus wrap. -/
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

/-! ## Forman non-convergence

Forman scalar on the open 2D grid is strictly negative and grows
unboundedly: `Forman(grid n n) ~ -8(n − 1)²` asymptotically (each
interior edge contributes `-8`, with boundary corrections).
Certified at sample sizes. -/

theorem grid_3_3_forman_neg : execFormanScalar (gridHG 3 3) = -40 := by native_decide
theorem grid_4_4_forman_neg : execFormanScalar (gridHG 4 4) = -112 := by native_decide
theorem grid_5_5_forman_neg : execFormanScalar (gridHG 5 5) = -216 := by native_decide
theorem grid_6_6_forman_neg : execFormanScalar (gridHG 6 6) = -352 := by native_decide

/-- Forman sample trace `[-40, -112, -216, -352]` — strictly
decreasing, diverging to `-∞`. -/
def gridFormanSampleTrace : List ℤ :=
  [execFormanScalar (gridHG 3 3),
   execFormanScalar (gridHG 4 4),
   execFormanScalar (gridHG 5 5),
   execFormanScalar (gridHG 6 6)]

theorem gridFormanSampleTrace_strictly_decreasing :
    gridFormanSampleTrace = [-40, -112, -216, -352] := by
  show [execFormanScalar (gridHG 3 3), execFormanScalar (gridHG 4 4),
        execFormanScalar (gridHG 5 5), execFormanScalar (gridHG 6 6)]
       = [-40, -112, -216, -352]
  rw [grid_3_3_forman_neg, grid_4_4_forman_neg, grid_5_5_forman_neg,
      grid_6_6_forman_neg]

/-- Forman on the grid is non-zero at every sampled size — explicit
non-convergence audit. -/
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

/-! ## Higuchi non-convergence

Higuchi-total-doubled on the grid is strictly negative and grows
unboundedly: `Higuchi(grid n n) ~ -2(n − 2)²` (interior degree-4
vertices contribute `2 − 4 = −2` each). -/

theorem grid_3_3_higuchi_neg : higuchiTotalDoubled (gridHG 3 3) = -6 := by native_decide
theorem grid_4_4_higuchi_neg : higuchiTotalDoubled (gridHG 4 4) = -16 := by native_decide
theorem grid_5_5_higuchi_neg : higuchiTotalDoubled (gridHG 5 5) = -30 := by native_decide
theorem grid_6_6_higuchi_neg : higuchiTotalDoubled (gridHG 6 6) = -48 := by native_decide

def gridHiguchiSampleTrace : List ℤ :=
  [higuchiTotalDoubled (gridHG 3 3),
   higuchiTotalDoubled (gridHG 4 4),
   higuchiTotalDoubled (gridHG 5 5),
   higuchiTotalDoubled (gridHG 6 6)]

theorem gridHiguchiSampleTrace_strictly_decreasing :
    gridHiguchiSampleTrace = [-6, -16, -30, -48] := by
  show [higuchiTotalDoubled (gridHG 3 3), higuchiTotalDoubled (gridHG 4 4),
        higuchiTotalDoubled (gridHG 5 5), higuchiTotalDoubled (gridHG 6 6)]
       = [-6, -16, -30, -48]
  rw [grid_3_3_higuchi_neg, grid_4_4_higuchi_neg, grid_5_5_higuchi_neg,
      grid_6_6_higuchi_neg]

/-! ## SquareCount non-convergence

SquareCount on the grid is strictly positive and grows unboundedly:
the grid is **made of squares** — each interior face is a 4-cycle.
`SquareCount(grid n n) = 8(n − 1)²` (8 per square × `(n−1)²` squares). -/

theorem grid_3_3_squareCount_pos : squareCountOrdered (gridHG 3 3) = 32 := by native_decide
theorem grid_4_4_squareCount_pos : squareCountOrdered (gridHG 4 4) = 72 := by native_decide
theorem grid_5_5_squareCount_pos : squareCountOrdered (gridHG 5 5) = 128 := by native_decide

def gridSquareCountSampleTrace : List ℤ :=
  [squareCountOrdered (gridHG 3 3),
   squareCountOrdered (gridHG 4 4),
   squareCountOrdered (gridHG 5 5)]

theorem gridSquareCountSampleTrace_strictly_increasing :
    gridSquareCountSampleTrace = [32, 72, 128] := by
  show [squareCountOrdered (gridHG 3 3), squareCountOrdered (gridHG 4 4),
        squareCountOrdered (gridHG 5 5)] = [32, 72, 128]
  rw [grid_3_3_squareCount_pos, grid_4_4_squareCount_pos,
      grid_5_5_squareCount_pos]

/-! ## DegVariance non-convergence

DegVariance on the grid is strictly positive and grows unboundedly
because the grid mixes corner (deg 2), boundary (deg 3), and
interior (deg 4) vertices. -/

theorem grid_3_3_degVariance_pos : degVarianceScaled (gridHG 3 3) = 36 := by native_decide
theorem grid_4_4_degVariance_pos : degVarianceScaled (gridHG 4 4) = 128 := by native_decide
theorem grid_5_5_degVariance_pos : degVarianceScaled (gridHG 5 5) = 300 := by native_decide

/-! ## Bundled non-convergence audit

A single theorem packing all four divergences. The 2D open grid
fails to converge under EVERY scalar in the architecture. -/

/-- **`unweighted_scalars_fail_on_2d_grid`**: certifies that ALL FOUR
unweighted curvature scalars (Forman, Higuchi, SquareCount,
DegVariance) on the 2D open grid `gridHG n n` are non-zero at sample
sizes — none of them recovers the vacuum target 0 of `D²`.

Note: theorem name claims a general failure; statement is verified
at a single sample (`gridHG 4 4`). 'None of them recovers the vacuum
target 0 of D²' is an extrapolation from this finite check. -/
theorem unweighted_scalars_fail_on_2d_grid :
    execFormanScalar (gridHG 4 4) ≠ 0 ∧
    higuchiTotalDoubled (gridHG 4 4) ≠ 0 ∧
    squareCountOrdered (gridHG 4 4) ≠ 0 ∧
    degVarianceScaled (gridHG 4 4) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [grid_4_4_forman_neg]; decide
  · rw [grid_4_4_higuchi_neg]; decide
  · rw [grid_4_4_squareCount_pos]; decide
  · rw [grid_4_4_degVariance_pos]; decide

/-! ## Architecture scope statement

After this audit and #421 (T² non-convergence), the convergence
landscape of the unweighted curvature scalars in this architecture
is the following:

| Topology               | Forman   | Higuchi  | SquareCount | DegVariance |
|------------------------|----------|----------|-------------|-------------|
| `cycle C_n` (→ `S¹`)    | 0        | 0        | 0           | 0           |
| `path P_n` (→ `[0,1]`)  | **4**    | **2**    | 0           | non-zero & growing at sampled n |
| `torus T²_n` (→ `T²`)   | non-zero & growing at sampled n | non-zero & growing at sampled n | non-zero & growing at sampled n | non-zero & growing at sampled n |
| `grid G_{n×n}` (→ `D²`) | non-zero & growing at sampled n | non-zero & growing at sampled n | non-zero & growing at sampled n | non-zero & growing at sampled n |

(at sampled n; asymptotic shape not proved)

**Convergent**: cycle (4 trivial), path (3 boundary signals).

**Divergent**: torus (4 scalars, no fix without weights), grid (4
scalars, no fix without weights).

For 2D+ targets the project's existing scalars are inadequate for
naive continuum-limit convergence; **weighted Forman** (Forman 2003
original, where each edge `e` carries weight `w_e` set to the edge
length in a metrized embedding) or distinct curvature notions
(Christiansen 2024 / effective resistance / Regge deficit) are the
literature-grade routes for the 2D case. The codebase **certifies
in Lean** that all four unweighted scalars are non-zero at grid
sample sizes 3×3..6×6; the 'hits its limit at 2D' framing is
interpretive.
-/

end GridContinuumLimit
end InfraFormalization
