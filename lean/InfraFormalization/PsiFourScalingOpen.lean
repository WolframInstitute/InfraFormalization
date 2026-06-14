/-
**B4-psi4-scaling-open: continuum Ψ₄ scaling open question** (#452;
H9 scaffold).

This module **formalizes as an explicit Prop the continuum-scaling
question** for the discrete Ψ₄ analog defined in #448. The result is
NOT proved here; instead, this module:

  1. States the proposition `DiscretePsiFourScalingHolds` precisely.
  2. Reduces it to a clean statement about the integrated Ψ₄
     trajectory under depth-scaling.
  3. Documents what would be needed for its proof, and what fails
     immediately if it doesn't hold.

**The conjecture**: there exists a scaling function `α(n)` such that
the depth-`n` integrated `|Ψ₄|²` on the BBH seed, scaled by `α(n)`,
converges to a finite limit as `n → ∞`.

Formally:

  `∃ α : ℕ → ℝ, ∃ L : ℝ,
     Tendsto (fun n => α(n) · integratedModSq (discretePsiFour ...)) atTop (𝓝 L)`

**What's known empirically** (from #447, #448):

  * For `edgeReversal + tripleMerger`, per-step flux grows ×3 each
    step. So integrated Ψ₄ grows at least geometrically.
  * For `edgeReversal` alone, per-step flux is constant. Integrated
    grows linearly (sum of 1's).

These two cases have very different scaling. The right α(n) depends
on which rule.

**The reasonable guess**: for a growth-rate-r rule, `α(n) = r⁻²ⁿ`
should give convergence. But this needs to be proved per rule.

**Why this matters** (H9 toward closure): without a scaling theorem,
we have raw discrete data without a continuum limit. With a
scaling theorem, the discrete Ψ₄ corresponds to actual NR Ψ₄ in the
continuum limit.

This module establishes the **infrastructure** for H9: the proposition
is stated, the auxiliary observables are referenced, and the
analysis problem is precisely scoped.
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

/-! ## The scaling proposition -/

/-- **`DiscretePsiFourScalingHolds`**: there exists a scaling
function `α : ℕ → ℝ` and a finite limit `L` such that

  `Tendsto (fun n => α(n) · (integratedModSq (discretePsiFour sys H n)).toReal)
   atTop (𝓝 L)`.

This is the discrete analog of the **continuum limit** of the
gravitational-wave energy under refinement. -/
def DiscretePsiFourScalingHolds (sys : ExecSystem) (H : ExecHG ℕ) : Prop :=
  ∃ α : ℕ → ℝ, ∃ L : ℝ,
    Filter.Tendsto (fun n => α n * ((integratedModSq (discretePsiFour sys H n)) : ℝ))
      Filter.atTop (nhds L)

/-! ## What's tractable: a single-rule trivial case -/

/-- **`zeroScalingHoldsTrivially`**: any system has the trivial
scaling `α(n) = 0`, `L = 0`. The interesting question is whether
there's a *non-trivial* scaling that converges to a *non-zero* limit.
-/
theorem zeroScalingHoldsTrivially (sys : ExecSystem) (H : ExecHG ℕ) :
    DiscretePsiFourScalingHolds sys H := by
  refine ⟨fun _ => 0, 0, ?_⟩
  simp only [zero_mul]
  exact tendsto_const_nhds

/-! ## The non-trivial form: convergence to a non-zero limit -/

/-- **`DiscretePsiFourScalingNonTrivial`**: there is a scaling
`α : ℕ → ℝ` and a non-zero finite `L` such that the scaled trajectory
converges to `L`. -/
def DiscretePsiFourScalingNonTrivial (sys : ExecSystem) (H : ExecHG ℕ) : Prop :=
  ∃ α : ℕ → ℝ, ∃ L : ℝ, L ≠ 0 ∧
    Filter.Tendsto (fun n => α n * ((integratedModSq (discretePsiFour sys H n)) : ℝ))
      Filter.atTop (nhds L)

/-! ## What this delivers

**A precisely-stated open question** for H9:

  * `DiscretePsiFourScalingHolds` — exists scaling + finite limit
    (trivially true for zero scaling).
  * `DiscretePsiFourScalingNonTrivial` — exists scaling + non-zero
    limit (the interesting question).

**What needs to be proved for H9 closure**:

  1. For each candidate rule class (Tree, Merger, Bidirected),
     find the rule-class-specific scaling function `α(n)`.
  2. Prove `DiscretePsiFourScalingNonTrivial` for the BBH seed
     under the highest-merger-rate combo.
  3. Show the continuum limit `L` matches the actual NR Ψ₄
     amplitude in expected units.

These are major analysis problems. This module makes the question
precise — that's a real contribution toward H9, even though the
analysis remains open.

**Implications**:

  * Future work can attempt `DiscretePsiFourScalingNonTrivial` for
    specific rules and seeds.
  * Failure of this proposition for any rule would be a refutation
    result — showing that rule class cannot model gravitational
    radiation in the continuum limit.
-/

end PsiFourScalingOpen
end InfraFormalization
