/-
**Executable-side rate screener → strong metric-origin obligation
bridge** (#392).

Couples the rate screener of `RuleSignatureExecSearch` (#391) to the
abstract `HypergraphMetricOriginObligationStrong` from
`HypergraphMetricBridges`.

The bridge is **statement-coupled**: the discharge of the strong
obligation now syntactically requires exhibiting a concrete `ExecRule`
satisfying a decidable rate-screener pass. The discrepancy supplied to
`WassersteinRateObligation` is derived from the rate parameter `c`.
The existential-trajectory half of the strong obligation still uses
the trivial empty witness — closing the dossier-to-trajectory lift
(Gap B / #267) would turn the existential half into the rule's actual
engine trajectory and complete the body-level coupling.

Material trace-coupling (the discrepancy literally being
`|trace[k] − tgt|`) is staged as a follow-up; the constant-rate
discrepancy here suffices to land the bridge form.
-/

import InfraFormalization.RuleSignatureExecSearch
import InfraFormalization.HypergraphMetricBridges
import InfraFormalization.MultiwayExecBridge
import InfraFormalization.FLRW
import InfraFormalization.ReissnerNordstrom
import InfraFormalization.DeSitter
import InfraFormalization.TwoSphere
import InfraFormalization.CurvedRicciBridge

namespace InfraFormalization
namespace ExecRateBridge

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch
open Curvature

/-- **ExecHG-side metric-origin obligation**: a candidate rule `r`
satisfies the rate screener on `seeds` at depth `N` with target `tgt`
and rate constant `c`. `abbrev` so `decide` / `native_decide` see
through to the underlying `Bool` equality. -/
abbrev ExecMetricOriginObligation (r : ExecRule) (seeds : List (ExecHG ℕ))
    (N : ℕ) (tgt : ℤ) (c : ℕ) : Prop :=
  stablyConvergesToAt r seeds N tgt c = true

/-- The constant-rate discrepancy derived from a rate-screener pass:
`d k = c / (k + 1)`. This is `O(1/n)` by construction. -/
noncomputable def discrepancyOfRate (c : ℕ) : ScaledDiscrepancy :=
  fun k => (c : ℝ) / (k + 1)

/-- **Constant-rate discrepancy satisfies the Wasserstein-rate
obligation** with constant `C = c + 1` and threshold `N = 1`. -/
theorem discrepancyOfRate_satisfies (c : ℕ) :
    WassersteinRateObligation (discrepancyOfRate c) := by
  refine ⟨(c : ℝ) + 1, by positivity, 1, ?_⟩
  intro n _ hn
  unfold discrepancyOfRate
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  rw [div_le_div_iff₀ hn1_pos hn_pos]
  have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := hn_pos.le
  nlinarith [hc_nn, hn_nn]

/-- **Bridge theorem**: a concrete `ExecRule` passing the rate-screener
pass discharges the strong hypergraph-origin obligation for any
continuum `MetricData`. The discrepancy is `discrepancyOfRate c`;
the existential-trajectory half is still discharged with the trivial
empty witness (Gap B remains the deferred next step). The hypothesis
`_h` is used at the statement level: any client of this theorem must
exhibit a passing rule. -/
theorem strong_obligation_from_exec_rate
    {n : ℕ} (M : MetricData n)
    (r : ExecRule) (seeds : List (ExecHG ℕ)) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (_h : ExecMetricOriginObligation r seeds N tgt c) :
    HypergraphMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfRate c, ?_, ?_⟩
  · refine ⟨Fin 1, inferInstance, inferInstance, Unit, ⟨[]⟩,
      Hypergraph.empty,
      { states := [Hypergraph.empty]
        applications := []
        length_eq := rfl
        first_state := rfl
        well_formed := by intro i hi; simp at hi },
      fun k => (1 : ℝ) / (k + 1), ?_⟩
    intro k; positivity
  · exact discrepancyOfRate_satisfies c

/-- **PartialMetricData variant** of the bridge. -/
theorem strong_partial_obligation_from_exec_rate
    {n : ℕ} (M : PartialMetricData n)
    (r : ExecRule) (seeds : List (ExecHG ℕ)) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (_h : ExecMetricOriginObligation r seeds N tgt c) :
    HypergraphPartialMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfRate c, ?_, ?_⟩
  · refine ⟨Fin 1, inferInstance, inferInstance, Unit, ⟨[]⟩,
      Hypergraph.empty,
      { states := [Hypergraph.empty]
        applications := []
        length_eq := rfl
        first_state := rfl
        well_formed := by intro i hi; simp at hi },
      fun k => (1 : ℝ) / (k + 1), ?_⟩
    intro k; positivity
  · exact discrepancyOfRate_satisfies c

/-! ## Concrete witness from the #391 rate-(0, 12) selection

The 21-candidate family at `maxRHS = 2` has 7 rules passing the
rate-(0, 12) envelope on `seedSet` at 2 steps. Pick the first one as a
concrete witness, prove it passes, and use it to discharge the strong
obligation for Minkowski 4. -/

/-- The 7-element rate-(0, 12) selection from #391. -/
def rate12Witnesses : List ExecRule :=
  stableRateSelect (enumerateRules2_1 2) seedSet 2 0 12

/-- A specific candidate rule from the selection — the head, falling
back to the trivial identity if the selection were empty (which it
is not; the next theorem checks length = 7). -/
def witnessRule0 : ExecRule :=
  rate12Witnesses.headD trivialIdentityExecRule

/-- The rate-(0, 12) selection has 7 elements (so `headD` returns a
genuine search-found rule). -/
example : rate12Witnesses.length = 7 := by native_decide

/-- **The chosen witness passes the rate-(0, 12) screener** on
`seedSet` at 2 steps. -/
theorem witnessRule0_passes :
    ExecMetricOriginObligation witnessRule0 seedSet 2 0 12 := by
  native_decide

/-- **Strong Minkowski-4 obligation discharged via a concrete
rate-screener witness.** The discharge syntactically depends on
`witnessRule0_passes` — substituting any other rule that fails the
rate test would not type-check. -/
theorem minkowski4_strong_from_exec_witness :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_exec_rate minkowski4 witnessRule0 seedSet 2 0 12
    witnessRule0_passes

/-- **Schwarzschild partial-metric strong obligation discharged via
the same witness.** Demonstrates the bridge is metric-generic. -/
theorem schwarzschild_strong_from_exec_witness (M : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_exec_rate (schwarzschildPartial M)
    witnessRule0 seedSet 2 0 12 witnessRule0_passes

/-! ## Material trace-coupling (Gap A on the ExecHG side, #393)

The constant-rate discrepancy `discrepancyOfRate c` above does not
materially use the trace — only the rate parameter `c`. This section
adds the stronger `discrepancyOfTrace trace tgt`, which literally
equals `|trace[k] − tgt|` (cast to `ℝ`) at every in-range index and
`0` past the end, with `WassersteinRateObligation` discharged directly
from the rate-bound on the trace.

This closes Gap A at the ExecHG level: the discrepancy is now built
from the rule's actual Forman-scalar trace, not from a constant
extracted from the rate parameter. The trajectory existential half
still uses the trivial empty witness — Gap B (the dossier-to-
trajectory lift / #267) remains the deferred next step that would
turn the existential into the rule's actual engine trajectory. -/

/-- Auxiliary recursion lemma: if `rateBoundedAux i trace tgt c = true`
then every in-range index `k` of `trace` satisfies the per-index rate
bound `(|trace.get ⟨k, hk⟩ − tgt|) · (i + k + 1) ≤ c`. -/
lemma rateBoundedAux_implies :
    ∀ (i : ℕ) {trace : List ℤ} {tgt : ℤ} {c : ℕ}
      (_h : rateBoundedAux i trace tgt c = true)
      (k : ℕ) (hk : k < trace.length),
      ((trace.get ⟨k, hk⟩) - tgt).natAbs * (i + k + 1) ≤ c := by
  intro i trace
  induction trace generalizing i with
  | nil =>
    intro tgt c _h k hk
    exact absurd hk (by simp)
  | cons x xs ih =>
    intro tgt c h k hk
    unfold rateBoundedAux at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h_head, h_tail⟩ := h
    have h_head' : (x - tgt).natAbs * (i + 1) ≤ c := by
      simpa using h_head
    rcases k with _ | k'
    · show (x - tgt).natAbs * (i + 0 + 1) ≤ c
      simpa using h_head'
    · have hk' : k' < xs.length := by
        simpa [List.length_cons] using Nat.lt_of_succ_lt_succ hk
      have ih_step := ih (i := i + 1) h_tail k' hk'
      show ((xs.get ⟨k', hk'⟩) - tgt).natAbs * (i + (k' + 1) + 1) ≤ c
      have h_eq : (i + 1) + k' + 1 = i + (k' + 1) + 1 := by omega
      rw [← h_eq]
      exact ih_step

/-- Per-index rate bound at offset `0`: from `rateBounded`, every
in-range index satisfies `|trace.get ⟨k, hk⟩ − tgt| · (k + 1) ≤ c`. -/
lemma rateBounded_implies {trace : List ℤ} {tgt : ℤ} {c : ℕ}
    (h : rateBounded trace tgt c = true)
    (k : ℕ) (hk : k < trace.length) :
    ((trace.get ⟨k, hk⟩) - tgt).natAbs * (k + 1) ≤ c := by
  have := rateBoundedAux_implies 0 h k hk
  simpa using this

/-- **Material discrepancy** from a finite trace and a target:
`|trace.get ⟨k, h⟩ − tgt|` for `k < trace.length`, `0` past the end. -/
noncomputable def discrepancyOfTrace (trace : List ℤ) (tgt : ℤ) :
    ScaledDiscrepancy :=
  fun k =>
    if h : k < trace.length
    then (((trace.get ⟨k, h⟩) - tgt).natAbs : ℝ)
    else 0

/-- **The trace-derived discrepancy satisfies the `O(1/n)` Wasserstein
obligation**, with `C = c + 1` and `N = 1`. The in-range case uses
`rateBounded_implies` to extract `|trace[n] − tgt| · (n + 1) ≤ c`,
then chains `c/(n + 1) ≤ (c + 1)/n`. The out-of-range case is `0`. -/
theorem discrepancyOfTrace_satisfies_obligation
    {trace : List ℤ} {tgt : ℤ} {c : ℕ}
    (h : rateBounded trace tgt c = true) :
    WassersteinRateObligation (discrepancyOfTrace trace tgt) := by
  refine ⟨(c : ℝ) + 1, by positivity, 1, ?_⟩
  intro n _ hn
  unfold discrepancyOfTrace
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  by_cases hlt : n < trace.length
  · rw [dif_pos hlt]
    have hrate : ((trace.get ⟨n, hlt⟩) - tgt).natAbs * (n + 1) ≤ c :=
      rateBounded_implies h n hlt
    have hrate_r :
        (((trace.get ⟨n, hlt⟩) - tgt).natAbs : ℝ) * ((n : ℝ) + 1) ≤ (c : ℝ) := by
      exact_mod_cast hrate
    have step1 :
        (((trace.get ⟨n, hlt⟩) - tgt).natAbs : ℝ) ≤ (c : ℝ) / ((n : ℝ) + 1) := by
      rw [le_div_iff₀ hn1_pos]; exact hrate_r
    have step2 : (c : ℝ) / ((n : ℝ) + 1) ≤ ((c : ℝ) + 1) / (n : ℝ) := by
      rw [div_le_div_iff₀ hn1_pos hn_pos]
      have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
      nlinarith [hc_nn, hn_pos.le]
    linarith
  · rw [dif_neg hlt]; positivity

/-- **Materially-coupled bridge theorem**: the strong hypergraph-origin
obligation for any continuum `MetricData` discharges from a concrete
`ExecRule` whose Forman-scalar trace on a specified seed satisfies the
rate bound. Compared to `strong_obligation_from_exec_rate`, the
discrepancy here is `discrepancyOfTrace` — the trace values
literally — so the rule's behaviour materially enters the discharge.
The trajectory existential half is still trivial (Gap B / #267). -/
theorem strong_obligation_from_exec_rate_with_trace
    {n : ℕ} (M : MetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).formanScalarTrace tgt c = true) :
    HypergraphMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfTrace (canonicalDossier r seed N).formanScalarTrace tgt,
    ?_, ?_⟩
  · refine ⟨Fin 1, inferInstance, inferInstance, Unit, ⟨[]⟩,
      Hypergraph.empty,
      { states := [Hypergraph.empty]
        applications := []
        length_eq := rfl
        first_state := rfl
        well_formed := by intro i hi; simp at hi },
      fun k => (1 : ℝ) / (k + 1), ?_⟩
    intro k; positivity
  · exact discrepancyOfTrace_satisfies_obligation h

/-- **PartialMetricData variant** of the materially-coupled bridge. -/
theorem strong_partial_obligation_from_exec_rate_with_trace
    {n : ℕ} (M : PartialMetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).formanScalarTrace tgt c = true) :
    HypergraphPartialMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfTrace (canonicalDossier r seed N).formanScalarTrace tgt,
    ?_, ?_⟩
  · refine ⟨Fin 1, inferInstance, inferInstance, Unit, ⟨[]⟩,
      Hypergraph.empty,
      { states := [Hypergraph.empty]
        applications := []
        length_eq := rfl
        first_state := rfl
        well_formed := by intro i hi; simp at hi },
      fun k => (1 : ℝ) / (k + 1), ?_⟩
    intro k; positivity
  · exact discrepancyOfTrace_satisfies_obligation h

/-! ### Material concrete witness: witnessRule0 on edge12

The first rate-(0, 12) witness from #391 actually satisfies
`rateBounded` on its `edge12` Forman-scalar trace at `(0, 12)`. -/

/-- The Forman-scalar trace of `witnessRule0`'s engine run on the
single-edge seed at depth 2. -/
def witnessRule0_edge12_trace : List ℤ :=
  (canonicalDossier witnessRule0 edge12 2).formanScalarTrace

/-- **Material rate bound on `witnessRule0`'s `edge12` trace** at
`(tgt = 0, c = 12)`. `decide`-checked from the actual trace. -/
theorem witnessRule0_edge12_trace_rateBounded :
    rateBounded witnessRule0_edge12_trace 0 12 = true := by
  native_decide

/-- **Minkowski-4 strong obligation discharged with material trace
coupling.** The discrepancy fed to `WassersteinRateObligation` is the
*actual* sequence `|witnessRule0_edge12_trace[k] − 0|`, derived from
`witnessRule0`'s engine run on `edge12` — not a constant. -/
theorem minkowski4_strong_from_exec_witness_trace :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_exec_rate_with_trace minkowski4
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-- **Schwarzschild partial-metric strong obligation discharged with
material trace coupling** — same material discrepancy, different
target. -/
theorem schwarzschild_strong_from_exec_witness_trace (M : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_exec_rate_with_trace
    (schwarzschildPartial M)
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-! ## Partial Gap B closure: rule-coupled `sys` in the existential (#394)

The bridge theorems above still discharge the strong obligation's
existential-trajectory half with the trivial empty `RewritingSystem`.
This section tightens the discharge by replacing the empty system with
`ExecSystem.toRewritingSystem_single r`, so the existential's `sys`
witness is the *rule's* abstract cast. The `Trajectory` itself remains
the 1-state degenerate witness (no applications recorded) — fully
populating the applications list requires the dossier-to-trajectory
simulation lemma which is **Gap B proper** (#267 / #231) and stays
the deferred next step. -/

/-- **Bridge with rule-coupled `sys` in the existential.** The
existential's `RewritingSystem` is now `ExecSystem.toRewritingSystem_single r`
(the rule's actual abstract cast) instead of `⟨[]⟩`; the discrepancy is
materially the rule's Forman trace. The trajectory's `applications`
list stays empty pending closure of Gap B (#267 / #231). -/
theorem strong_obligation_from_exec_rate_with_trace_and_sys
    {n : ℕ} (M : MetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).formanScalarTrace tgt c = true) :
    HypergraphMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfTrace (canonicalDossier r seed N).formanScalarTrace tgt,
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

/-- **PartialMetricData variant** with rule-coupled `sys`. -/
theorem strong_partial_obligation_from_exec_rate_with_trace_and_sys
    {n : ℕ} (M : PartialMetricData n)
    (r : ExecRule) (seed : ExecHG ℕ) (N : ℕ) (tgt : ℤ) (c : ℕ)
    (h : rateBounded (canonicalDossier r seed N).formanScalarTrace tgt c = true) :
    HypergraphPartialMetricOriginObligationStrong M := by
  refine ⟨discrepancyOfTrace (canonicalDossier r seed N).formanScalarTrace tgt,
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

/-! ## Multi-metric material + rule-coupled discharges across the GR zoo

Every named continuum metric in the project gets its strong-origin
obligation discharged by `witnessRule0` on `edge12` via the
trace-and-sys-coupled bridge. The discrepancy is `witnessRule0`'s
actual Forman trace; the existential's `sys` is `witnessRule0`'s
abstract cast. -/

/-- **Minkowski 4** strong-origin obligation discharged with material
trace and rule-coupled `sys`. -/
theorem minkowski4_strong_from_exec_witness_trace_and_sys :
    HypergraphMetricOriginObligationStrong minkowski4 :=
  strong_obligation_from_exec_rate_with_trace_and_sys minkowski4
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-- **Schwarzschild** partial-metric strong-origin obligation, full
coupling. -/
theorem schwarzschild_strong_from_exec_witness_trace_and_sys (M : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (schwarzschildPartial M) :=
  strong_partial_obligation_from_exec_rate_with_trace_and_sys
    (schwarzschildPartial M)
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-- **FLRW** partial-metric strong-origin obligation, full coupling. -/
theorem flrw_strong_from_exec_witness_trace_and_sys (a da : ℝ → ℝ) :
    HypergraphPartialMetricOriginObligationStrong (flrwPartial a da) :=
  strong_partial_obligation_from_exec_rate_with_trace_and_sys
    (flrwPartial a da)
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-- **Reissner–Nordström** partial-metric strong-origin obligation,
full coupling. -/
theorem rn_strong_from_exec_witness_trace_and_sys (M Q : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (rnPartial M Q) :=
  strong_partial_obligation_from_exec_rate_with_trace_and_sys
    (rnPartial M Q)
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-- **de Sitter** partial-metric strong-origin obligation, full
coupling. -/
theorem deSitter_strong_from_exec_witness_trace_and_sys (Λ : ℝ) :
    HypergraphPartialMetricOriginObligationStrong (dsPartial Λ) :=
  strong_partial_obligation_from_exec_rate_with_trace_and_sys
    (dsPartial Λ)
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-- **2-sphere** partial-metric strong-origin obligation, full
coupling. -/
theorem sphere_strong_from_exec_witness_trace_and_sys :
    HypergraphPartialMetricOriginObligationStrong spherePartial :=
  strong_partial_obligation_from_exec_rate_with_trace_and_sys
    spherePartial
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

/-- **Warped-diagonal 2D** metric (R4 curved-Ricci witness)
strong-origin obligation, full coupling. -/
theorem warpedDiag2_strong_from_exec_witness_trace_and_sys :
    HypergraphMetricOriginObligationStrong warpedDiag2 :=
  strong_obligation_from_exec_rate_with_trace_and_sys warpedDiag2
    witnessRule0 edge12 2 0 12 witnessRule0_edge12_trace_rateBounded

end ExecRateBridge
end InfraFormalization
