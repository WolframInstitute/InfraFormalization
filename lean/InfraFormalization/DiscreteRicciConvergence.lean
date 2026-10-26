/-
Finite-trace bounds and limits of Forman-scalar traces.

`FiniteFitEnvelope trace tgt c` states `|trace[k] − tgt| · (k + 1) ≤ c` for
every entry of a finite trace; it is the property that `rateBounded` checks.
`TrueLimitConverges s tgt` states that the sequence `s` tends to `tgt`.
`formanLimitTrace r seed n` is the Forman scalar of the state after `n` steps
of `singleWayEvolve`.

The Forman trace of `witnessRule0` on `edge12` over 2 steps is `[4, 4, 4]`,
which satisfies `rateBounded _ 0 12`. If the trace is 4 at every depth, it does
not tend to 0 (`witnessRule0_edge12_does_not_true_limit_converge_to_zero`).
Whether the trace is 4 at every depth is not proved.
-/

import InfraFormalization.RuleSignatureExecSearch
import Mathlib.Topology.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace InfraFormalization
namespace DiscreteRicciConvergence

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open RuleSignatureExecCorpus
open RuleSignatureExecSearch

/-- `|trace[k] − tgt| · (k + 1) ≤ c` for every entry k of the finite trace. -/
def FiniteFitEnvelope (trace : List ℤ) (tgt : ℤ) (c : ℕ) : Prop :=
  ∀ k (hk : k < trace.length),
    (Int.natAbs (trace.get ⟨k, hk⟩ - tgt)) * (k + 1) ≤ c

/-- The sequence `extendedTrace`, cast to ℝ, tends to `tgt`. -/
def TrueLimitConverges (extendedTrace : ℕ → ℤ) (tgt : ℤ) : Prop :=
  Filter.Tendsto (fun n => ((extendedTrace n) : ℝ)) Filter.atTop (nhds ((tgt : ℝ)))

/-- The Forman scalar of the state after `n` steps of `singleWayEvolve` of
the one-rule system `[r]` from `seed`. -/
def formanLimitTrace (r : ExecRule) (seed : ExecHG ℕ) : ℕ → ℤ :=
  fun n => execFormanScalar (singleWayEvolve ⟨[r]⟩ seed n)

/-- The Forman trace of `witnessRule0` on `edge12` is 4 at every depth.
Used as a hypothesis; not proved. -/
def witnessRule0_edge12_isFormanConstant : Prop :=
  ∀ n : ℕ, formanLimitTrace witnessRule0 edge12 n = 4

/-- The constant sequence 4 does not tend to 0. -/
theorem constant_4_not_tendsto_zero :
    ¬ Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
  intro h
  have h4 : Filter.Tendsto (fun _ : ℕ => (4 : ℝ)) Filter.atTop (nhds (4 : ℝ)) :=
    tendsto_const_nhds
  have : (4 : ℝ) = (0 : ℝ) := tendsto_nhds_unique h4 h
  norm_num at this

/-- If the Forman trace of `witnessRule0` on `edge12` is 4 at every depth,
it does not tend to 0. -/
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
  have : ((0 : ℤ) : ℝ) = (0 : ℝ) := by norm_num
  rw [this] at htends
  exact htends

end DiscreteRicciConvergence
end InfraFormalization
