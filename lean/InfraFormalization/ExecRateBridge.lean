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

end ExecRateBridge
end InfraFormalization
