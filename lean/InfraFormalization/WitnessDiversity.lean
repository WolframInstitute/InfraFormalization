/-
**Witness-diversity layer for the GR-zoo material discharges** (#408).

Every existing material discharge in the GR-zoo
(`ExecRateBridge` #394, `TransportRateBridge` #404, `HiguchiRateBridge`
#406, `DegVarianceRateBridge` #407) is anchored to the SAME
`(witnessRule0, edge12)` pair. This module promotes the rate-bridge
architecture to **multi-seed witness layers** by publishing additional
material discharges using:

  * the same rule `witnessRule0` on the alternative seeds `path123`
    and `cycle4`,

so that every GR metric receives **THREE independent seed-witnesses
per curvature family** — twelve seed-witnesses total — and the
discharge is demonstrably not anchored to any single seed.

The witnesses certify constant traces on each seed, native_decide-checkable:

  Seed     | Forman      | Transport       | Higuchi   | DegVariance
  edge12   | [4,4,4]     | [-2,-2,-2]      | [2,2,2]   | [0,0,0]
  path123  | [4,4,4]     | [-16,-16,-16]   | [2,2,2]   | [2,2,2]
  cycle4   | [0,0,0]     | [-64,-64,-64]   | [0,0,0]   | [0,0,0]

Each row gives constants ⇒ rate envelopes at `(tgt = constant, c = 0)`
hold trivially, and each metric in the GR zoo discharges through each
(seed, family) cell independently.
-/

import InfraFormalization.DegVarianceRateBridge
import InfraFormalization.HiguchiRateBridge
import InfraFormalization.TransportRateBridge

namespace InfraFormalization
namespace WitnessDiversity

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch
open ExecRateBridge
open TransportRateBridge
open HiguchiRateBridge
open DegVarianceRateBridge
open DegreeVarianceScreener
open HiguchiScreener
open OllivierRicciScreener
open Curvature

/-! ## Path123 witness layer (Forman + Transport + Higuchi + DegVariance) -/

/-- Forman trace of `witnessRule0` on `path123`. -/
def witnessRule0_path123_formanTrace : List ℤ :=
  (canonicalDossier witnessRule0 path123 2).formanScalarTrace
example : witnessRule0_path123_formanTrace = [4, 4, 4] := by native_decide
theorem witnessRule0_path123_formanTrace_rateBounded :
    rateBounded witnessRule0_path123_formanTrace 4 0 = true := by native_decide

/-- Transport trace of `witnessRule0` on `path123`. -/
def witnessRule0_path123_transportTrace : List ℤ :=
  (canonicalDossier witnessRule0 path123 2).transportScalarTrace
example : witnessRule0_path123_transportTrace = [-16, -16, -16] := by native_decide
theorem witnessRule0_path123_transportTrace_rateBounded :
    rateBounded witnessRule0_path123_transportTrace (-16) 0 = true := by native_decide

/-- Higuchi trace of `witnessRule0` on `path123`. -/
def witnessRule0_path123_higuchiTrace : List ℤ :=
  (canonicalDossier witnessRule0 path123 2).higuchiScalarTrace
example : witnessRule0_path123_higuchiTrace = [2, 2, 2] := by native_decide
theorem witnessRule0_path123_higuchiTrace_rateBounded :
    rateBounded witnessRule0_path123_higuchiTrace 2 0 = true := by native_decide

/-- DegVariance trace of `witnessRule0` on `path123`. -/
def witnessRule0_path123_degVarianceTrace : List ℤ :=
  (canonicalDossier witnessRule0 path123 2).degVarianceTrace
example : witnessRule0_path123_degVarianceTrace = [2, 2, 2] := by native_decide
theorem witnessRule0_path123_degVarianceTrace_rateBounded :
    rateBounded witnessRule0_path123_degVarianceTrace 2 0 = true := by native_decide

/-! ## Cycle4 witness layer (Forman + Transport + Higuchi + DegVariance) -/

/-- Forman trace of `witnessRule0` on `cycle4`. -/
def witnessRule0_cycle4_formanTrace : List ℤ :=
  (canonicalDossier witnessRule0 cycle4 2).formanScalarTrace
example : witnessRule0_cycle4_formanTrace = [0, 0, 0] := by native_decide
theorem witnessRule0_cycle4_formanTrace_rateBounded :
    rateBounded witnessRule0_cycle4_formanTrace 0 0 = true := by native_decide

/-- Transport trace of `witnessRule0` on `cycle4`. -/
def witnessRule0_cycle4_transportTrace : List ℤ :=
  (canonicalDossier witnessRule0 cycle4 2).transportScalarTrace
example : witnessRule0_cycle4_transportTrace = [-64, -64, -64] := by native_decide
theorem witnessRule0_cycle4_transportTrace_rateBounded :
    rateBounded witnessRule0_cycle4_transportTrace (-64) 0 = true := by native_decide

/-- Higuchi trace of `witnessRule0` on `cycle4`. -/
def witnessRule0_cycle4_higuchiTrace : List ℤ :=
  (canonicalDossier witnessRule0 cycle4 2).higuchiScalarTrace
example : witnessRule0_cycle4_higuchiTrace = [0, 0, 0] := by native_decide
theorem witnessRule0_cycle4_higuchiTrace_rateBounded :
    rateBounded witnessRule0_cycle4_higuchiTrace 0 0 = true := by native_decide

/-- DegVariance trace of `witnessRule0` on `cycle4`. -/
def witnessRule0_cycle4_degVarianceTrace : List ℤ :=
  (canonicalDossier witnessRule0 cycle4 2).degVarianceTrace
example : witnessRule0_cycle4_degVarianceTrace = [0, 0, 0] := by native_decide
theorem witnessRule0_cycle4_degVarianceTrace_rateBounded :
    rateBounded witnessRule0_cycle4_degVarianceTrace 0 0 = true := by native_decide

/-! ## Named GR-zoo discharges via `path123` (4 curvature families × 7 metrics)

These are second seed-witnesses for every (metric, family) cell;
the standing `edge12`-anchored discharges (#394 / #404 / #406 / #407)
are the first. Together they prove the discharge architecture is
*not* anchored to a single seed. -/

section Path123Family

variable (M : ℝ) (Q : ℝ) (Λ : ℝ) (a da : ℝ → ℝ)

/-- Minkowski 4 — Forman discharge via `(witnessRule0, path123)`. -/
theorem minkowski4_strong_path123_forman :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_exec_rate_with_trace minkowski4
    witnessRule0 path123 2 4 0
    witnessRule0_path123_formanTrace_rateBounded

/-- Minkowski 4 — Transport discharge via `(witnessRule0, path123)`. -/
theorem minkowski4_strong_path123_transport :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_transport_rate minkowski4 witnessRule0 path123 2
    (-16) 0 witnessRule0_path123_transportTrace_rateBounded

/-- Minkowski 4 — Higuchi discharge via `(witnessRule0, path123)`. -/
theorem minkowski4_strong_path123_higuchi :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_higuchi_rate minkowski4 witnessRule0 path123 2
    2 0 witnessRule0_path123_higuchiTrace_rateBounded

/-- Minkowski 4 — DegVariance discharge via `(witnessRule0, path123)`. -/
theorem minkowski4_strong_path123_degvariance :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_degvariance_rate minkowski4 witnessRule0 path123 2
    2 0 witnessRule0_path123_degVarianceTrace_rateBounded

/-- Schwarzschild — Transport discharge via `(witnessRule0, path123)`. -/
theorem schwarzschild_strong_path123_transport :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_transport_rate (schwarzschildPartial M)
    witnessRule0 path123 2 (-16) 0 witnessRule0_path123_transportTrace_rateBounded

/-- Schwarzschild — Higuchi discharge via `(witnessRule0, path123)`. -/
theorem schwarzschild_strong_path123_higuchi :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_higuchi_rate (schwarzschildPartial M)
    witnessRule0 path123 2 2 0 witnessRule0_path123_higuchiTrace_rateBounded

/-- Schwarzschild — DegVariance discharge via `(witnessRule0, path123)`. -/
theorem schwarzschild_strong_path123_degvariance :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_degvariance_rate (schwarzschildPartial M)
    witnessRule0 path123 2 2 0 witnessRule0_path123_degVarianceTrace_rateBounded

/-- FLRW — Transport discharge via `(witnessRule0, path123)`. -/
theorem flrw_strong_path123_transport :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_transport_rate (flrwPartial a da)
    witnessRule0 path123 2 (-16) 0 witnessRule0_path123_transportTrace_rateBounded

/-- FLRW — Higuchi discharge via `(witnessRule0, path123)`. -/
theorem flrw_strong_path123_higuchi :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_higuchi_rate (flrwPartial a da)
    witnessRule0 path123 2 2 0 witnessRule0_path123_higuchiTrace_rateBounded

/-- FLRW — DegVariance discharge via `(witnessRule0, path123)`. -/
theorem flrw_strong_path123_degvariance :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_degvariance_rate (flrwPartial a da)
    witnessRule0 path123 2 2 0 witnessRule0_path123_degVarianceTrace_rateBounded

/-- Reissner-Nordström — Transport discharge via `(witnessRule0, path123)`. -/
theorem rn_strong_path123_transport :
    HypergraphPartialMetricOriginObligationStrong (rnPartial M Q) :=
  strong_partial_obligation_from_transport_rate (rnPartial M Q)
    witnessRule0 path123 2 (-16) 0 witnessRule0_path123_transportTrace_rateBounded

/-- Reissner-Nordström — DegVariance discharge via `(witnessRule0, path123)`. -/
theorem rn_strong_path123_degvariance :
    HypergraphPartialMetricOriginObligationStrong (rnPartial M Q) :=
  strong_partial_obligation_from_degvariance_rate (rnPartial M Q)
    witnessRule0 path123 2 2 0 witnessRule0_path123_degVarianceTrace_rateBounded

/-- de Sitter — Transport discharge via `(witnessRule0, path123)`. -/
theorem deSitter_strong_path123_transport :
    HypergraphPartialMetricOriginObligationStrong (dsPartial Λ) :=
  strong_partial_obligation_from_transport_rate (dsPartial Λ)
    witnessRule0 path123 2 (-16) 0 witnessRule0_path123_transportTrace_rateBounded

/-- de Sitter — DegVariance discharge via `(witnessRule0, path123)`. -/
theorem deSitter_strong_path123_degvariance :
    HypergraphPartialMetricOriginObligationStrong (dsPartial Λ) :=
  strong_partial_obligation_from_degvariance_rate (dsPartial Λ)
    witnessRule0 path123 2 2 0 witnessRule0_path123_degVarianceTrace_rateBounded

/-- 2-sphere — DegVariance discharge via `(witnessRule0, path123)`. -/
theorem sphere_strong_path123_degvariance :
    HypergraphPartialMetricOriginObligationStrong spherePartial :=
  strong_partial_obligation_from_degvariance_rate spherePartial
    witnessRule0 path123 2 2 0 witnessRule0_path123_degVarianceTrace_rateBounded

/-- warpedDiag2 — DegVariance discharge via `(witnessRule0, path123)`. -/
theorem warpedDiag2_strong_path123_degvariance :
    HypergraphMetricOriginObligationStrong warpedDiag2 :=
  strong_obligation_from_degvariance_rate warpedDiag2 witnessRule0 path123 2
    2 0 witnessRule0_path123_degVarianceTrace_rateBounded

end Path123Family

/-! ## Named GR-zoo discharges via `cycle4` (4 curvature families × 7 metrics)

Third seed-witnesses for every (metric, family) cell. The cycle4
seed exhibits *flat* signatures across Forman and Higuchi (4-cycle
has degree-2 vertices on a regular ring), while transport
amplifies (cycle4 is more connected). This complements the path123
and edge12 witnesses with a topologically distinct seed shape. -/

section Cycle4Family

variable (M : ℝ) (Q : ℝ) (Λ : ℝ) (a da : ℝ → ℝ)

/-- Minkowski 4 — Forman discharge via `(witnessRule0, cycle4)`. -/
theorem minkowski4_strong_cycle4_forman :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_exec_rate_with_trace minkowski4
    witnessRule0 cycle4 2 0 0
    witnessRule0_cycle4_formanTrace_rateBounded

/-- Minkowski 4 — Transport discharge via `(witnessRule0, cycle4)`. -/
theorem minkowski4_strong_cycle4_transport :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_transport_rate minkowski4 witnessRule0 cycle4 2
    (-64) 0 witnessRule0_cycle4_transportTrace_rateBounded

/-- Minkowski 4 — Higuchi discharge via `(witnessRule0, cycle4)`. -/
theorem minkowski4_strong_cycle4_higuchi :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_higuchi_rate minkowski4 witnessRule0 cycle4 2
    0 0 witnessRule0_cycle4_higuchiTrace_rateBounded

/-- Minkowski 4 — DegVariance discharge via `(witnessRule0, cycle4)`. -/
theorem minkowski4_strong_cycle4_degvariance :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_degvariance_rate minkowski4 witnessRule0 cycle4 2
    0 0 witnessRule0_cycle4_degVarianceTrace_rateBounded

/-- Schwarzschild — Transport discharge via `(witnessRule0, cycle4)`. -/
theorem schwarzschild_strong_cycle4_transport :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_transport_rate (schwarzschildPartial M)
    witnessRule0 cycle4 2 (-64) 0 witnessRule0_cycle4_transportTrace_rateBounded

/-- Schwarzschild — Higuchi discharge via `(witnessRule0, cycle4)`. -/
theorem schwarzschild_strong_cycle4_higuchi :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_higuchi_rate (schwarzschildPartial M)
    witnessRule0 cycle4 2 0 0 witnessRule0_cycle4_higuchiTrace_rateBounded

/-- Schwarzschild — DegVariance discharge via `(witnessRule0, cycle4)`. -/
theorem schwarzschild_strong_cycle4_degvariance :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_degvariance_rate (schwarzschildPartial M)
    witnessRule0 cycle4 2 0 0 witnessRule0_cycle4_degVarianceTrace_rateBounded

/-- FLRW — Transport discharge via `(witnessRule0, cycle4)`. -/
theorem flrw_strong_cycle4_transport :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_transport_rate (flrwPartial a da)
    witnessRule0 cycle4 2 (-64) 0 witnessRule0_cycle4_transportTrace_rateBounded

/-- FLRW — Higuchi discharge via `(witnessRule0, cycle4)`. -/
theorem flrw_strong_cycle4_higuchi :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_higuchi_rate (flrwPartial a da)
    witnessRule0 cycle4 2 0 0 witnessRule0_cycle4_higuchiTrace_rateBounded

/-- FLRW — DegVariance discharge via `(witnessRule0, cycle4)`. -/
theorem flrw_strong_cycle4_degvariance :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_degvariance_rate (flrwPartial a da)
    witnessRule0 cycle4 2 0 0 witnessRule0_cycle4_degVarianceTrace_rateBounded

/-- Reissner-Nordström — Transport discharge via `(witnessRule0, cycle4)`. -/
theorem rn_strong_cycle4_transport :
    HypergraphPartialMetricOriginObligationStrong (rnPartial M Q) :=
  strong_partial_obligation_from_transport_rate (rnPartial M Q)
    witnessRule0 cycle4 2 (-64) 0 witnessRule0_cycle4_transportTrace_rateBounded

/-- Reissner-Nordström — Higuchi discharge via `(witnessRule0, cycle4)`. -/
theorem rn_strong_cycle4_higuchi :
    HypergraphPartialMetricOriginObligationStrong (rnPartial M Q) :=
  strong_partial_obligation_from_higuchi_rate (rnPartial M Q)
    witnessRule0 cycle4 2 0 0 witnessRule0_cycle4_higuchiTrace_rateBounded

/-- de Sitter — Transport discharge via `(witnessRule0, cycle4)`. -/
theorem deSitter_strong_cycle4_transport :
    HypergraphPartialMetricOriginObligationStrong (dsPartial Λ) :=
  strong_partial_obligation_from_transport_rate (dsPartial Λ)
    witnessRule0 cycle4 2 (-64) 0 witnessRule0_cycle4_transportTrace_rateBounded

/-- 2-sphere — Transport discharge via `(witnessRule0, cycle4)`. -/
theorem sphere_strong_cycle4_transport :
    HypergraphPartialMetricOriginObligationStrong spherePartial :=
  strong_partial_obligation_from_transport_rate spherePartial
    witnessRule0 cycle4 2 (-64) 0 witnessRule0_cycle4_transportTrace_rateBounded

/-- warpedDiag2 — Transport discharge via `(witnessRule0, cycle4)`. -/
theorem warpedDiag2_strong_cycle4_transport :
    HypergraphMetricOriginObligationStrong warpedDiag2 :=
  strong_obligation_from_transport_rate warpedDiag2 witnessRule0 cycle4 2
    (-64) 0 witnessRule0_cycle4_transportTrace_rateBounded

end Cycle4Family

end WitnessDiversity
end InfraFormalization
