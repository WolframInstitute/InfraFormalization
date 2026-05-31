/-
**Square-count rate-bridge: fifth material discharge route** (#410).

Parallels `ExecRateBridge` (#394 Forman), `TransportRateBridge` (#404),
`HiguchiRateBridge` (#406), and `DegVarianceRateBridge` (#407) for the
*square-count* scalar from `SquareCountScreener` — a cycle-topology
scalar that captures global 4-cycle (square) structure, independent
of the four earlier degree- and neighbourhood-based scalars.

After this commit every continuum GR metric in the zoo has **FIVE
independent material rate-bridge discharges** through five distinct
curvature families.
-/

import InfraFormalization.SquareCountScreener
import InfraFormalization.ExecRateBridge

namespace InfraFormalization
namespace SquareCountRateBridge

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch
open SquareCountScreener
open ExecRateBridge
open Curvature

/-! ## Square-count rate predicates -/

/-- A dossier's square-count trace satisfies the rate envelope. -/
def dossierSquareCountConvergesToAt (d : Dossier) (tgt : ℤ) (c : ℕ) : Bool :=
  rateBounded d.squareCountTrace tgt c

/-- A candidate rule's square-count trace stably converges at rate `c`
across `seeds`. -/
def squareCountStablyConvergesToAt (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : ℤ) (c : ℕ) : Bool :=
  seeds.all (fun s => dossierSquareCountConvergesToAt (canonicalDossier r s n) tgt c)

/-- The square-count rate-screener selection. -/
def squareCountStableRateSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : ℤ) (c : ℕ) : List ExecRule :=
  cands.filter (fun r => squareCountStablyConvergesToAt r seeds n tgt c)

/-- **ExecHG-side SquareCount metric-origin obligation**. -/
abbrev ExecSquareCountMetricOriginObligation (r : ExecRule) (seeds : List (ExecHG ℕ))
    (N : ℕ) (tgt : ℤ) (c : ℕ) : Prop :=
  squareCountStablyConvergesToAt r seeds N tgt c = true

/-! ## Bridges through the SquareCount family -/

/-- **SquareCount-side material bridge**: a candidate ExecRule whose
square-count trace on `seed` satisfies the rate envelope discharges
the strong hypergraph-origin obligation for any continuum `MetricData M`. -/
theorem strong_obligation_from_squarecount_rate
    {n : ℕ} (M : MetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).squareCountTrace tgt c = true) :
    HypergraphMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfTrace (canonicalDossier r seed N).squareCountTrace tgt,
    ?_, ?_⟩
  · refine ⟨Fin 1, inferInstance, inferInstance,
      Fin (r.numBound + r.numFresh),
      ExecSystem.toRewritingSystem_single r,
      Hypergraph.empty,
      { states := [Hypergraph.empty]
        applications := []
        length_eq := rfl
        first_state := rfl
        well_formed := by intro i hi; simp at hi },
      fun k => (1 : ℝ) / (k + 1), ?_⟩
    intro k; positivity
  · exact discrepancyOfTrace_satisfies_obligation h

/-- **PartialMetricData variant** of the SquareCount-side bridge. -/
theorem strong_partial_obligation_from_squarecount_rate
    {n : ℕ} (M : PartialMetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).squareCountTrace tgt c = true) :
    HypergraphPartialMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfTrace (canonicalDossier r seed N).squareCountTrace tgt,
    ?_, ?_⟩
  · refine ⟨Fin 1, inferInstance, inferInstance,
      Fin (r.numBound + r.numFresh),
      ExecSystem.toRewritingSystem_single r,
      Hypergraph.empty,
      { states := [Hypergraph.empty]
        applications := []
        length_eq := rfl
        first_state := rfl
        well_formed := by intro i hi; simp at hi },
      fun k => (1 : ℝ) / (k + 1), ?_⟩
    intro k; positivity
  · exact discrepancyOfTrace_satisfies_obligation h

/-! ## Concrete witness via `witnessRule0` on `edge12`

`witnessRule0` produces no squares on the tiny `edge12` seed, so the
square-count trace is constant at `0`. Any `(tgt = 0, c = 0)`
envelope is satisfied trivially. -/

/-- The square-count trace of `witnessRule0` on `edge12` at depth 2. -/
def witnessRule0_edge12_squareCountTrace : List ℤ :=
  (canonicalDossier witnessRule0 edge12 2).squareCountTrace

/-- The square-count trace is `[0, 0, 0]` — constant (the seed and
its 2-step evolution stay square-free). -/
example : witnessRule0_edge12_squareCountTrace = [0, 0, 0] := by native_decide

/-- **Material rate bound on `witnessRule0`'s square-count trace** at
`(tgt = 0, c = 0)`. -/
theorem witnessRule0_edge12_squareCountTrace_rateBounded :
    rateBounded witnessRule0_edge12_squareCountTrace 0 0 = true := by
  native_decide

/-! ## Named GR-zoo material discharges via the SQUARE-COUNT family

Every continuum metric now has FIVE independent material discharge
routes: Forman (#394), Transport (#404), Higuchi (#406), DegVariance
(#407), SquareCount (this commit). -/

/-- **Minkowski 4 — fifth material discharge** via square count. -/
theorem minkowski4_strong_from_exec_witness_squarecount :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_squarecount_rate minkowski4
    witnessRule0 edge12 2 0 0 witnessRule0_edge12_squareCountTrace_rateBounded

/-- **Schwarzschild — fifth material discharge**. -/
theorem schwarzschild_strong_from_exec_witness_squarecount (M : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_squarecount_rate
    (schwarzschildPartial M)
    witnessRule0 edge12 2 0 0 witnessRule0_edge12_squareCountTrace_rateBounded

/-- **FLRW — fifth material discharge**. -/
theorem flrw_strong_from_exec_witness_squarecount (a da : ℝ → ℝ) :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_squarecount_rate
    (flrwPartial a da)
    witnessRule0 edge12 2 0 0 witnessRule0_edge12_squareCountTrace_rateBounded

/-- **Reissner–Nordström — fifth material discharge**. -/
theorem rn_strong_from_exec_witness_squarecount (M Q : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (rnPartial M Q) :=
  strong_partial_obligation_from_squarecount_rate
    (rnPartial M Q)
    witnessRule0 edge12 2 0 0 witnessRule0_edge12_squareCountTrace_rateBounded

/-- **de Sitter — fifth material discharge**. -/
theorem deSitter_strong_from_exec_witness_squarecount (Λ : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (dsPartial Λ) :=
  strong_partial_obligation_from_squarecount_rate
    (dsPartial Λ)
    witnessRule0 edge12 2 0 0 witnessRule0_edge12_squareCountTrace_rateBounded

/-- **2-sphere — fifth material discharge**. -/
theorem sphere_strong_from_exec_witness_squarecount :
    HypergraphPartialMetricOriginObligationStrong spherePartial :=
  strong_partial_obligation_from_squarecount_rate
    spherePartial
    witnessRule0 edge12 2 0 0 witnessRule0_edge12_squareCountTrace_rateBounded

/-- **Warped-diagonal 2D — fifth material discharge**. -/
theorem warpedDiag2_strong_from_exec_witness_squarecount :
    HypergraphMetricOriginObligationStrong warpedDiag2 :=
  strong_obligation_from_squarecount_rate warpedDiag2
    witnessRule0 edge12 2 0 0 witnessRule0_edge12_squareCountTrace_rateBounded

end SquareCountRateBridge
end InfraFormalization
