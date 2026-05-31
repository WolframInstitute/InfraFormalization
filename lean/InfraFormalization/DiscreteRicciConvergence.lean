/-
**B4: Discrete-curvature → continuum-Ricci convergence framework**
(#419, scaffold for #218 / R4 / #179).

This module distinguishes two notions of "convergence" that the
existing rate-bridge architecture conflates:

  1. **Finite-fit envelope**: `rateBounded trace tgt c` requires
     `|trace[k] − tgt| · (k+1) ≤ c` for `k < trace.length`. A
     FINITE-DEPTH bound; the trace itself need not approach `tgt`
     as depth → ∞. Choosing `c` loose enough always works.

  2. **True-limit convergence**: `trace n → tgt` as `n → ∞` (in the
     genuine `Filter.Tendsto` sense). This is what physics requires
     for the metric-emergence claim.

**The honesty audit**: the standing `witnessRule0`-on-`edge12` discharges
satisfy (1) at depth 2 with `c = 12` because `4 · 3 = 12 ≤ 12` works
for `k ∈ {0, 1, 2}`. But the actual trace is `[4, 4, 4]` — constant
at 4, not approaching the vacuum target `tgt = 0`. So:

  - Finite-fit at depth 2 with `c = 12`: **true** (4(k+1) ≤ 12 for k ≤ 2).
  - Finite-fit at depth 4 with `c = 12`: **false** (4 · 5 = 20 > 12).
  - True-limit `trace → 0`: **false** (constant 4 doesn't tend to 0).

This module:
  - Defines `FormanTrueLimitConverges` (the genuine `Tendsto` claim).
  - Proves the disconnect: a constant non-zero trace does NOT satisfy
    `FormanTrueLimitConverges tgt = 0` even when it satisfies a
    finite-fit envelope.
  - Provides the architectural framework for the eventual B4/B5
    convergence theorem.

This is the honest scaffolding: it makes the gap explicit rather than
glossing it. The fully-material convergence theorem (`trace → tgt` for
a rule that genuinely produces the metric) is research-level
mathematics; this module marks its statement-level shape.
-/

import InfraFormalization.MetricTargetScalars
import Mathlib.Topology.Order
import Mathlib.Order.Filter.AtTopBot.Basic

namespace InfraFormalization
namespace DiscreteRicciConvergence

open Curvature
open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch
open ExecRateBridge
open ExecTrajectoryLift
open MetricTargetScalars

/-! ## Two convergence notions

  - `FiniteFitEnvelope`: the existing `rateBounded`-style finite-depth check.
  - `TrueLimitConverges`: genuine `Filter.Tendsto` of the trace to the target. -/

/-- **Finite-fit envelope**: the trace fits in a `c/(k+1)` envelope
around `tgt` over its finite recorded length. This is what the
existing `rateBounded` checks. -/
def FiniteFitEnvelope (trace : List ℤ) (tgt : ℤ) (c : ℕ) : Prop :=
  ∀ k (hk : k < trace.length),
    (Int.natAbs (trace.get ⟨k, hk⟩ - tgt)) * (k + 1) ≤ c

/-- **True-limit convergence**: extended to an infinite trace
`extendedTrace : ℕ → ℤ` (e.g., engine state's Forman scalar at depth `n`),
the trace tends to `tgt` as `n → ∞`. This is what the physics actually
requires for "continuum Ricci emerges from discrete curvature". -/
def TrueLimitConverges (extendedTrace : ℕ → ℤ) (tgt : ℤ) : Prop :=
  Filter.Tendsto (fun n => ((extendedTrace n) : ℝ)) Filter.atTop (nhds ((tgt : ℝ)))

/-- The **true-limit Forman trace** of a rule on a seed: the infinite
sequence of Forman-scalar values at each depth. -/
def formanLimitTrace (r : ExecRule) (seed : ExecHG ℕ) : ℕ → ℤ :=
  fun n => execFormanScalar (singleWayEvolve ⟨[r]⟩ seed n)

/-! ## The honesty disconnect: constant trace at 4 doesn't tend to 0

For `witnessRule0` on `edge12`, the Forman trace is `[4, 4, 4]` at
depth 2. The TRUE-LIMIT trace is the constant 4 sequence (the rule
preserves the Forman scalar). This sequence does NOT tend to 0
(the vacuum-Ricci target). -/

/-- For `witnessRule0` on `edge12`, the true-limit Forman trace is
*constant 4* — every depth produces the same Forman scalar. -/
def witnessRule0_edge12_isFormanConstant : Prop :=
  ∀ n : ℕ, formanLimitTrace witnessRule0 edge12 n = 4

/-- The constant-4 sequence does NOT tend to 0. By uniqueness of
limits: a constant sequence has its value as limit, so if it also
tended to 0, then 4 = 0, contradiction. -/
theorem constant_4_not_tendsto_zero :
    ¬ Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
  intro h
  have h4 : Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) Filter.atTop (nhds (4 : ℝ)) :=
    tendsto_const_nhds
  have : (4 : ℝ) = (0 : ℝ) := tendsto_nhds_unique h4 h
  norm_num at this

/-- **The honesty point**: if `witnessRule0`'s Forman trace is constant 4,
then it does NOT satisfy `TrueLimitConverges _ 0`. The finite-fit envelope
(`c = 12` at depth 2) is satisfied, but the true-limit convergence to
the vacuum target `0` is NOT. -/
theorem witnessRule0_edge12_does_not_true_limit_converge_to_zero
    (h : witnessRule0_edge12_isFormanConstant) :
    ¬ TrueLimitConverges (formanLimitTrace witnessRule0 edge12) 0 := by
  intro htends
  unfold TrueLimitConverges at htends
  apply constant_4_not_tendsto_zero
  have heq : (fun n => ((formanLimitTrace witnessRule0 edge12 n : ℤ) : ℝ))
           = (fun _ : ℕ => (4 : ℝ)) := by
    funext n
    show ((formanLimitTrace witnessRule0 edge12 n : ℤ) : ℝ) = (4 : ℝ)
    rw [h n]
    norm_num
  rw [← heq]
  -- htends has target `((0 : ℤ) : ℝ)`; rewrite to `(0 : ℝ)`.
  have : ((0 : ℤ) : ℝ) = (0 : ℝ) := by norm_num
  rw [this] at htends
  exact htends

/-! ## A `TrueLimitConverges` predicate that the architecture should aim for

For an `ExecRule` to **materially generate** a metric `M` in the
continuum-Ricci sense, its Forman limit trace should tend to `M`'s
Forman target. This is the predicate B4-full would discharge. -/

/-- **Statement-level convergence claim**: an `ExecRule` generates a
`MetricData`'s Forman-target scalar in the true-limit sense. -/
def RuleGeneratesMetric_forman {n : ℕ} (r : ExecRule) (seed : ExecHG ℕ)
    (M : MetricData n) : Prop :=
  TrueLimitConverges (formanLimitTrace r seed) (formanTarget M)

/-- **Statement-level convergence claim** for `PartialMetricData`. -/
def RuleGeneratesPartialMetric_forman {n : ℕ} (r : ExecRule) (seed : ExecHG ℕ)
    (M : PartialMetricData n) : Prop :=
  TrueLimitConverges (formanLimitTrace r seed) (formanTargetPartial M)

/-! ## Examples — discharging the trivial cases

For the (degenerate) case where the rule's Forman limit trace IS
the metric's target value as a constant, true-limit convergence holds
by `Tendsto.const`. -/

/-- If the rule's limit trace is literally constant at the target,
then it true-limit converges (degenerate "no curvature dynamics" case). -/
theorem trueLimit_of_constant_at_target
    (extendedTrace : ℕ → ℤ) (tgt : ℤ) (h : ∀ n, extendedTrace n = tgt) :
    TrueLimitConverges extendedTrace tgt := by
  unfold TrueLimitConverges
  have : (fun n => ((extendedTrace n) : ℝ)) = (fun _ => ((tgt : ℝ))) := by
    funext n; rw [h n]
  rw [this]
  exact tendsto_const_nhds

/-! ## Honest framing: where genuine material convergence lives

The B4 framework above lets us state the *real* convergence claim:
`RuleGeneratesMetric_forman r seed M`. Discharging it for non-trivial
`(r, seed, M)` triples — i.e., **a rule whose curvature trace ACTUALLY
approaches the metric's target** — is the research-level content of
B4-full / R4 (#179) / #218.

What landed here:
  * The two-notion framework (finite-fit vs true-limit) makes the
    gap explicit.
  * The honesty theorem `witnessRule0_edge12_does_not_true_limit_converge_to_zero`
    proves the existing witness FAILS true-limit convergence to the
    vacuum target — so the discharge cascade's "discharges Minkowski 4"
    claim is precisely a finite-fit claim, not a continuum-limit claim.
  * `RuleGeneratesMetric_forman` is the statement-level shape the
    fully-material discharge would have. The research-level content
    is what makes it inhabitable for non-trivial `(r, M)`.

B4-full (the actual convergence theorem) is downstream of:
  - A scaling map from ExecHG vertices to manifold points.
  - A scaling map from rule-step depth to lattice spacing.
  - The continuum-Ricci-as-limit-of-discrete-Forman theorem
    (R4 / #179 / #218 / Christiansen 2024 et al.). -/

end DiscreteRicciConvergence
end InfraFormalization
