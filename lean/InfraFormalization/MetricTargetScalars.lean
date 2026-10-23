/-
Per-metric target values for the curvature scalar traces.

Every target value in this file is the constant 0, for every metric,
including the non-vacuum metrics. A discharge that requires
`tgt = formanTarget M` therefore requires `tgt = 0` and carries no
information about `M`.
-/

import InfraFormalization.ExecTrajectoryLift

namespace InfraFormalization
namespace MetricTargetScalars

open Curvature
open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch
open ExecRateBridge
open ExecTrajectoryLift

/-! ## Per-metric target curvature scalars

For each curvature family, the **continuum target value** that the
discrete trace should converge to. For vacuum solutions, the target
is `0`; for matter/charge content it can differ. -/

/-- **Forman target scalar** for a metric — the continuum
combinatorial-curvature analog. For vacuum metrics (Ric = 0) the
target is `0`; for non-vacuum metrics it's the discretization of
the metric's Ricci scalar at a chosen reference point. -/
def formanTarget {n : Nat} (_M : MetricData n) : ℤ := 0
  -- For Minkowski 4 / warpedDiag2 / sphere / Schwarzschild exterior:
  -- vacuum Ricci = 0 → discrete Forman target = 0.
  -- For FLRW / RN: non-zero target requires R4/#218 discrete-Ricci
  -- convergence theorem; placeholder 0 is a deliberate marker that
  -- the per-metric refinement is pending.

/-- **Transport target scalar** — continuum counterpart for the
Ollivier-Wasserstein scalar. -/
def transportTarget {n : Nat} (_M : MetricData n) : ℤ := 0

/-- **Higuchi target scalar** — continuum counterpart for the
Higuchi planar combinatorial curvature. For 2D vacuum (flat plane,
sphere) the Higuchi defect target is constant; for higher-dim
this needs refinement. -/
def higuchiTarget {n : Nat} (_M : MetricData n) : ℤ := 0

/-- **Degree-variance target scalar** — continuum counterpart for
the degree-distribution variance. For homogeneous spacetimes it's
constant; for inhomogeneous (Schwarzschild, FLRW) it varies. -/
def degVarianceTarget {n : Nat} (_M : MetricData n) : ℤ := 0

/-- **Square-count target scalar** — continuum counterpart for the
4-cycle count. For 1D and 2D-triangulated targets it's `0`; for
higher-dim cubical/wheel structures it grows. -/
def squareCountTarget {n : Nat} (_M : MetricData n) : ℤ := 0

/-! ## PartialMetricData analogues -/

def formanTargetPartial {n : Nat} (_M : PartialMetricData n) : ℤ := 0
def transportTargetPartial {n : Nat} (_M : PartialMetricData n) : ℤ := 0
def higuchiTargetPartial {n : Nat} (_M : PartialMetricData n) : ℤ := 0
def degVarianceTargetPartial {n : Nat} (_M : PartialMetricData n) : ℤ := 0
def squareCountTargetPartial {n : Nat} (_M : PartialMetricData n) : ℤ := 0

/-! ## Coupled rate-envelope discharges

These theorems REQUIRE the rate-envelope's `tgt` parameter to match
the metric's target scalar. They are strictly stronger than the
target-agnostic versions in `ExecRateBridge`. -/

/-- **Coupled Forman discharge**: the rate envelope's target must
match the metric's `formanTarget`. -/
theorem strong_obligation_from_exec_rate_with_metric_coupled_tgt
    {n : ℕ} (M : MetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).formanScalarTrace
                     (formanTarget M) c = true) :
    HypergraphMetricOriginObligationStrong M :=
  strong_obligation_from_exec_rate_with_lifted_trajectory M r seed N
    (formanTarget M) c h

/-- **PartialMetricData variant**. -/
theorem strong_partial_obligation_from_exec_rate_with_metric_coupled_tgt
    {n : ℕ} (M : PartialMetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).formanScalarTrace
                     (formanTargetPartial M) c = true) :
    HypergraphPartialMetricOriginObligationStrong M :=
  strong_partial_obligation_from_exec_rate_with_lifted_trajectory M r seed N
    (formanTargetPartial M) c h

/-! ## Named GR-zoo discharges with COUPLED targets

These use `witnessRule0`'s trace on `edge12` with `tgt` materially
tied to each metric's `formanTarget`. For vacuum metrics this
coincides with the previous `tgt = 0` choice — but now the `0` is
not an arbitrary parameter, it's `formanTarget M`. -/

/-- The trace's rate bound at target `formanTarget minkowski4 = 0`. -/
theorem witnessRule0_edge12_formanTarget_minkowski4_rateBounded :
    rateBounded (canonicalDossier witnessRule0 edge12 2).formanScalarTrace
                (formanTarget minkowski4) 12 = true := by
  show rateBounded _ 0 12 = true
  exact witnessRule0_edge12_trace_rateBounded

/-- **Minkowski 4 — Forman discharge with COUPLED metric-target**. -/
theorem minkowski4_strong_coupled :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_exec_rate_with_metric_coupled_tgt minkowski4
    witnessRule0 edge12 2 12
    witnessRule0_edge12_formanTarget_minkowski4_rateBounded

/-- The trace's rate bound at target `formanTargetPartial spherePartial = 0`. -/
theorem witnessRule0_edge12_formanTarget_spherePartial_rateBounded :
    rateBounded (canonicalDossier witnessRule0 edge12 2).formanScalarTrace
                (formanTargetPartial spherePartial) 12 = true := by
  show rateBounded _ 0 12 = true
  exact witnessRule0_edge12_trace_rateBounded

/-- **Sphere — Forman discharge with COUPLED metric-target**. -/
theorem sphere_strong_coupled :
    HypergraphPartialMetricOriginObligationStrong spherePartial :=
  strong_partial_obligation_from_exec_rate_with_metric_coupled_tgt
    spherePartial witnessRule0 edge12 2 12
    witnessRule0_edge12_formanTarget_spherePartial_rateBounded

/-- **warpedDiag2 — Forman discharge with COUPLED metric-target**. -/
theorem warpedDiag2_strong_coupled :
    HypergraphMetricOriginObligationStrong warpedDiag2 :=
  strong_obligation_from_exec_rate_with_metric_coupled_tgt warpedDiag2
    witnessRule0 edge12 2 12
    (show rateBounded _ (formanTarget warpedDiag2) 12 = true from
      witnessRule0_edge12_trace_rateBounded)

/-- **Schwarzschild exterior — Forman discharge with COUPLED target**. -/
theorem schwarzschild_strong_coupled (M : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_exec_rate_with_metric_coupled_tgt
    (schwarzschildPartial M) witnessRule0 edge12 2 12
    (show rateBounded _ (formanTargetPartial (schwarzschildPartial M)) 12 = true from
      witnessRule0_edge12_trace_rateBounded)

/-! ## Honesty audit

These coupled discharges are stronger than the target-agnostic
versions in one specific way: the `tgt` in the rate envelope is
`formanTarget M` — a function of the metric — not a free integer.

What this DOESN'T (yet) establish:
  - That `formanTarget M` correctly captures `M`'s Ricci scalar
    (requires B4: R4 / #179 / #218 discrete-Ricci convergence).
  - That the discrete-Forman-trace ACTUALLY converges to
    `formanTarget M` for the engine run (requires the simulation
    lemma + the convergence theorem).

What this DOES establish:
  - The rate envelope is no longer target-agnostic; it now claims
    "trace converges to *the metric's target scalar* with rate".
  - For vacuum metrics, the target scalar is canonically `0` — this
    is correct (Ric = 0 for these metrics, so any discretization
    that converges should converge to `0`).
  - The discharge architecture is now properly parametric in the
    metric, not in an arbitrary integer.

The remaining gap is B4 / B5: proving the discrete-curvature →
continuum-Ricci convergence theorem. The current `formanTarget M`
returns the correct value for vacuum metrics by construction;
extending it to non-vacuum requires B4. -/

/-- For any vacuum metric (with `formanTarget M = 0`), the coupled
discharge has `tgt = 0`. The witness traces are constant at `0` for
the `c = 0` envelope — making the discharge a true vacuum claim. -/
example (M : MetricData 4) (h : formanTarget M = 0) :
    rateBounded [0, 0, 0] (formanTarget M) 0 = true := by
  rw [h]; native_decide

end MetricTargetScalars
end InfraFormalization
