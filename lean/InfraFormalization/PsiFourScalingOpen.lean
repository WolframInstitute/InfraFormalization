/-
Two Props about rescaled sums of squares of `discretePsiFour`.

`discretePsiFour sys H n` is the list of pairs (change in causal-graph
Knill value from step k to k+1, number of events at step k) for
k < n, computed with `causalDAGOfFireAll` and `tracedFireAllEvolve`.
The evolution is `fireAllStep`, which applies every match of every rule
found in the state, including matches that share edges. It is not a
Wolfram model update when matches overlap. `integratedModSq` is the sum
of `re² + im²` over the list. The name Ψ₄ is a label; the library
defines no Weyl tensor or waveform.

  * `DiscretePsiFourScalingHolds sys H`: some `α : ℕ → ℝ` and `L : ℝ`
    make `α n * integratedModSq (discretePsiFour sys H n)` tend to `L`.
    It holds for every `sys` and `H` with `α = 0`
    (`zeroScalingHoldsTrivially`), so it is VACUOUS.
  * `DiscretePsiFourScalingNonTrivial sys H`: the same with `L ≠ 0`.
    No instance is proved in the library.
-/

import InfraFormalization.DiscretePsiFour

namespace InfraFormalization
namespace PsiFourScalingOpen

open MultiwayExec
open RuleSignatureExecMetrics
open CausalEventTrace
open DiscoveredRules
open BBHInitialData
open DiscretePsiFour

/-! ## The scaling Prop -/

/-- `DiscretePsiFourScalingHolds sys H`: there exist `α : ℕ → ℝ` and
`L : ℝ` such that
`α n * integratedModSq (discretePsiFour sys H n)` tends to `L`. -/
def DiscretePsiFourScalingHolds (sys : ExecSystem) (H : ExecHG ℕ) : Prop :=
  ∃ α : ℕ → ℝ, ∃ L : ℝ,
    Filter.Tendsto (fun n => α n * ((integratedModSq (discretePsiFour sys H n)) : ℝ))
      Filter.atTop (nhds L)

/-! ## The zero choice -/

/-- `zeroScalingHoldsTrivially`: `DiscretePsiFourScalingHolds sys H`
holds for every `sys` and `H`, with `α = 0` and `L = 0`. -/
theorem zeroScalingHoldsTrivially (sys : ExecSystem) (H : ExecHG ℕ) :
    DiscretePsiFourScalingHolds sys H := by
  refine ⟨fun _ => 0, 0, ?_⟩
  simp only [zero_mul]
  exact tendsto_const_nhds

/-! ## The form with a nonzero limit -/

/-- `DiscretePsiFourScalingNonTrivial sys H`: there exist
`α : ℕ → ℝ` and `L ≠ 0` such that
`α n * integratedModSq (discretePsiFour sys H n)` tends to `L`. -/
def DiscretePsiFourScalingNonTrivial (sys : ExecSystem) (H : ExecHG ℕ) : Prop :=
  ∃ α : ℕ → ℝ, ∃ L : ℝ, L ≠ 0 ∧
    Filter.Tendsto (fun n => α n * ((integratedModSq (discretePsiFour sys H n)) : ℝ))
      Filter.atTop (nhds L)

/-! ## Summary

  * `DiscretePsiFourScalingHolds`: holds for every `sys` and `H`
    (`zeroScalingHoldsTrivially`, PROVED). It is VACUOUS.
  * `DiscretePsiFourScalingNonTrivial`: no theorem in the library
    proves or refutes it for any instance. For any `sys` and `H` whose
    value `integratedModSq (discretePsiFour sys H n)` is nonzero for all
    large `n`, the choice `α(n) = 1 / value` and `L = 1` satisfies it;
    no Lean statement records this.

Neither Prop refers to a continuum limit or to a waveform.
-/

end PsiFourScalingOpen
end InfraFormalization
