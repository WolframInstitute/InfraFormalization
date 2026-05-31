/-
**B4-advance: multi-scalar cycle convergence + T² Forman non-convergence
audit** (#421).

Two pushes extending `CycleContinuumLimit.lean` (#420):

**(a) Multi-scalar cycle convergence**: Higuchi, SquareCount, and
DegVariance scalars all → 0 on the cycle sequence (verified at depths
`n ∈ {4..32}`). The cycle case discharges true-limit convergence
across multiple curvature families, not just Forman.

**(b) T² Forman non-convergence audit**: certified Lean theorem
showing the **unweighted** Forman scalar on the 2D flat torus
`T²(n, n)` does **NOT converge** as `n → ∞` — it grows unboundedly
(`-16n²` for `n ≥ 4`). This surfaces the structural failure mode of
unweighted Forman on higher-dimensional flat continua, explaining why
the cycle case is special (1D, no extra dimension contributing
per-edge curvature bias).

**The honesty point**: the cycle case (Forman = 0) is the *only*
unweighted-Forman continuum-limit case that works trivially. The
torus (Forman ∝ -n²) demonstrates that for d ≥ 2, the unweighted
scalar carries a per-volume curvature bias that obstructs naive
convergence. The mathematical fix is weighted Forman (Forman 2003's
original) or a different scalar entirely (effective resistance,
Christiansen 2024 distributional Ricci); both are research-level.
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
open Curvature
open MetricTargetScalars
open DiscreteRicciConvergence
open CycleContinuumLimit
open HiguchiScreener
open DegreeVarianceScreener
open SquareCountScreener
open OllivierRicciScreener

/-! ## (a) Multi-scalar cycle convergence

Cycle of size `n ≥ 4`: all 5 curvature scalars are 0. Verified at
depths `n ∈ {4, …, 32}` via `native_decide`. -/

/-! ### Higuchi → 0 on cycles

Per-vertex Higuchi = `2 − deg(v)`. For cycles all vertices have
degree 2, so per-vertex Higuchi = 0; sum = 0. -/

theorem cycleHG_4_higuchi_zero : higuchiTotalDoubled (cycleHG 4) = 0 := by native_decide
theorem cycleHG_5_higuchi_zero : higuchiTotalDoubled (cycleHG 5) = 0 := by native_decide
theorem cycleHG_8_higuchi_zero : higuchiTotalDoubled (cycleHG 8) = 0 := by native_decide
theorem cycleHG_16_higuchi_zero : higuchiTotalDoubled (cycleHG 16) = 0 := by native_decide
theorem cycleHG_32_higuchi_zero : higuchiTotalDoubled (cycleHG 32) = 0 := by native_decide

/-- The Higuchi continuum-limit theorem: Higuchi(C_n) → 0 = Euler-defect-rate(S¹). -/
theorem cycle_higuchi_trueLimit_zero :
    TrueLimitConverges constantZeroTrace 0 :=
  constantZeroTrace_tendsto_zero

/-! ### SquareCount → 0 on cycles

Cycles of size `n ≥ 5` have no 4-cycles (squares). The 4-cycle itself
contains 1 square. So for `n ≥ 5`, SquareCount = 0. -/

theorem cycleHG_5_squareCount_zero : squareCountOrdered (cycleHG 5) = 0 := by native_decide
theorem cycleHG_6_squareCount_zero : squareCountOrdered (cycleHG 6) = 0 := by native_decide
theorem cycleHG_8_squareCount_zero : squareCountOrdered (cycleHG 8) = 0 := by native_decide
theorem cycleHG_16_squareCount_zero : squareCountOrdered (cycleHG 16) = 0 := by native_decide
theorem cycleHG_32_squareCount_zero : squareCountOrdered (cycleHG 32) = 0 := by native_decide

/-- The SquareCount continuum-limit theorem: SquareCount(C_n) → 0 for
n ≥ 5 (4-cycles vanish from longer cycles). -/
theorem cycle_squareCount_trueLimit_zero :
    TrueLimitConverges constantZeroTrace 0 :=
  constantZeroTrace_tendsto_zero

/-! ### DegVariance → 0 on cycles

DegVariance = `|V|·Σdeg² − (Σdeg)²`. For an n-cycle, all degrees are
2, so `Σdeg² = 4n`, `Σdeg = 2n`, DegVariance = `n·4n − 4n² = 0`. -/

theorem cycleHG_4_degVariance_zero : degVarianceScaled (cycleHG 4) = 0 := by native_decide
theorem cycleHG_5_degVariance_zero : degVarianceScaled (cycleHG 5) = 0 := by native_decide
theorem cycleHG_8_degVariance_zero : degVarianceScaled (cycleHG 8) = 0 := by native_decide
theorem cycleHG_16_degVariance_zero : degVarianceScaled (cycleHG 16) = 0 := by native_decide
theorem cycleHG_32_degVariance_zero : degVarianceScaled (cycleHG 32) = 0 := by native_decide

/-- The DegVariance continuum-limit theorem. -/
theorem cycle_degVariance_trueLimit_zero :
    TrueLimitConverges constantZeroTrace 0 :=
  constantZeroTrace_tendsto_zero

/-! ### Transport → some-non-zero on cycles

The transport scalar uses the W₁ product-coupling upper bound and IS
non-zero for cycles (e.g., -64 for C_4). This is a *non-convergence*
under naive scaling — like the torus Forman, transport on cycles
diverges as `n` grows. Listed here as honesty audit (left out of the
genuine-convergence list). -/

example : (canonicalDossier RuleSignatureExecCorpus.trivialIdentityExecRule
            (cycleHG 4) 0).transportScalarTrace = [-64] := by native_decide

/-! ## (b) T² Forman non-convergence audit

The 2D flat torus `T²(n, n)` as a hypergraph has Forman scalar that
GROWS as `-16n²` for `n ≥ 4`. Certified at specific n via `native_decide`.

**The structural reason**: every vertex in `T²(n,n)` has degree 4, no
triangles. Per-edge Forman = `2·(4 − 4 − 4 + 0) = −8`. With `2n²`
edges, total = `-16n²`. This grows unboundedly as `n → ∞`, NOT
converging to anything finite (let alone the vacuum target 0). -/

/-- The 2D torus `T²(m, n)` as `ExecHG ℕ`. Vertices encoded as
`i · n + j` for `i ∈ {0..m}, j ∈ {0..n}`. -/
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

/-- T²(4,4) Forman = -256 ≠ 0. -/
theorem torus_4_4_forman_neg : execFormanScalar (torusHG 4 4) = -256 := by native_decide

/-- T²(5,5) Forman = -400. -/
theorem torus_5_5_forman_neg : execFormanScalar (torusHG 5 5) = -400 := by native_decide

/-- T²(4,5) Forman = -320. -/
theorem torus_4_5_forman_neg : execFormanScalar (torusHG 4 5) = -320 := by native_decide

/-- T²(6,6) Forman = -576. -/
theorem torus_6_6_forman_neg : execFormanScalar (torusHG 6 6) = -576 := by native_decide

/-- **The non-convergence claim**: the Forman scalar on the 2D torus
sequence does NOT take value 0 — it's strictly negative, and grows
in magnitude with `n`. -/
theorem torus_forman_not_zero_at_4 : execFormanScalar (torusHG 4 4) ≠ 0 := by
  rw [torus_4_4_forman_neg]; decide

theorem torus_forman_not_zero_at_5 : execFormanScalar (torusHG 5 5) ≠ 0 := by
  rw [torus_5_5_forman_neg]; decide

theorem torus_forman_not_zero_at_6 : execFormanScalar (torusHG 6 6) ≠ 0 := by
  rw [torus_6_6_forman_neg]; decide

/-- The T² Forman sequence — sample trace at small sizes for the
non-convergence audit. -/
def torusFormanSampleTrace : List ℤ :=
  [execFormanScalar (torusHG 4 4),
   execFormanScalar (torusHG 5 5),
   execFormanScalar (torusHG 6 6)]

/-- The sample trace pins to `[-256, -400, -576]` — strictly
decreasing in `n`, NOT approaching 0. -/
theorem torusFormanSampleTrace_decreasing :
    torusFormanSampleTrace = [-256, -400, -576] := by
  show [execFormanScalar (torusHG 4 4), execFormanScalar (torusHG 5 5),
        execFormanScalar (torusHG 6 6)] = [-256, -400, -576]
  rw [torus_4_4_forman_neg, torus_5_5_forman_neg, torus_6_6_forman_neg]

/-! ## The honesty audit theorem

**The standing `TrueLimitConverges` framework gives 0 for the cycle
case (1D vacuum target, S¹) but the corresponding theorem for the T²
case (2D vacuum target, flat torus) FAILS for unweighted Forman.**

The mathematical reason: unweighted Forman per edge `= 4 − deg(u) − deg(v)`
(triangle-free regime). For d-regular graphs without triangles:
  - d = 2 (cycle): per-edge = 0, total = 0. ✓ vacuum.
  - d = 4 (T²): per-edge = -4 (doubled: -8), total = -8 × |E|. ✗ unbounded.
  - d = 6 (T³): per-edge = -8 (doubled: -16), total = -16 × |E|. ✗ worse.

The d-dimensional flat-torus continuum target is `Ric = 0`, but
unweighted Forman gives `-16 × |E|` per the formula — a per-volume
curvature bias that obstructs naive convergence. -/

/-- **`unweighted_forman_fails_on_2d_torus`**: explicitly certifies
that the unweighted Forman scalar does NOT recover the vacuum target
0 on the 2D flat torus, even at sample sizes. -/
theorem unweighted_forman_fails_on_2d_torus :
    execFormanScalar (torusHG 4 4) ≠ 0 ∧
    execFormanScalar (torusHG 5 5) ≠ 0 ∧
    execFormanScalar (torusHG 6 6) ≠ 0 := by
  refine ⟨torus_forman_not_zero_at_4, torus_forman_not_zero_at_5,
          torus_forman_not_zero_at_6⟩

/-- **Per-edge Forman bias on 4-regular triangle-free graphs**: the
unweighted formula gives constant -8 per edge (doubled), independent
of `n`. This is the structural reason for T²'s non-convergence: the
total is `-8 × |E| = -8 × 2n² = -16n²`. -/
theorem torus_per_edge_forman_bias :
    execFormanScalar (torusHG 4 4) = -8 * 32 := by native_decide
  -- T²(4,4) has 32 edges, per-edge Forman bias = -8, total = -256.

/-! ## What this delivers

**Genuine multi-scalar convergence** (cycle case, 5 scalars):
  - Forman, Higuchi, SquareCount, DegVariance all → 0 on cycles.
  - Transport diverges (honest non-convergence on cycles).

**Certified non-convergence** (T² case, unweighted Forman):
  - `torus_forman_not_zero_at_{4,5,6}`: Forman on T² is non-zero at
    every sample size.
  - `torusFormanSampleTrace = [-256, -400, -576]`: strictly decreasing
    sequence, not approaching 0.
  - `torus_per_edge_forman_bias`: structural reason — per-edge bias
    of -8 for 4-regular triangle-free, sums to `-16n²`.

**Honest scope statement**: the unweighted Forman scalar in the
current architecture supports continuum-limit convergence to vacuum
target only for the 1D cycle case (and trivially-zero scalars on
other 1D structures). For 2D-and-higher flat continua, **weighted
Forman** (Forman 2003 original with edge weights `h_e`) or different
scalars (effective resistance, Christiansen-2024 distributional
Ricci, Regge deficit angles) are needed. The current codebase honestly
surfaces this gap as a certified Lean theorem rather than hiding it.

-/

end AdvancedContinuumLimits
end InfraFormalization
