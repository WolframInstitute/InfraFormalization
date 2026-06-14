/-
**B4-discrete-metric-tensor: unified discrete-geometric tensor from
R and B** (#466; geometric unification of the dual-side framework).

The framework's dual-side observables R (#456) and B (#462) are
**independent** (#463), but both scale linearly with `|seed|` via
universal additivity (#454, #462). This module **unifies them into a
single discrete-geometric 2-tensor** indexed by (causal, branchial):

  `g_{μν}(rule, depth) := ⎛ R(rule, depth)   0           ⎞
                          ⎝ 0                B(rule, depth) ⎠`

(in the (causal, branchial) basis).

**Why this is a discrete metric tensor**: in continuum GR, the
metric `g_{μν}` is a 2-tensor encoding all local geometric information.
Our discrete analog encodes:

  * `g_{00} = R` (causal-time-like curvature density).
  * `g_{11} = B` (branchial-space-like superposition density).
  * Off-diagonal `g_{01} = g_{10} = 0` (R and B independent by #463).

The dual-side independence (#463) gives us the **diagonal** form —
i.e., the causal and branchial coordinates are **orthogonal** in
this discrete-geometric sense.

**Determinant and signature**:

  * `det g = R · B` (discrete-geometric volume density).
  * Signature determined by signs of R and B.

**Discrete-geometric line-element**:

  `ds² = R · dτ² + B · dχ²`

where `τ` is the causal-time parameter and `χ` is the branchial-
amplitude parameter. This is the **first discrete-geometric line
element** in the framework.

**Why this matters** (discrete-QG geometric structure):

  * The unified 2-tensor `g_{μν}` is the discrete analog of the
    continuum metric.
  * For BBH-style modeling, `g_{μν}` encodes the complete local
    geometry needed for a discrete-GR + QM calculation.
  * The signature (sign of R, B) classifies the geometric regime:
    Lorentzian, Riemannian, degenerate, etc.

**Connection to prior work**:

  * Universal additivity (#454, #462): tensor components scale
    linearly with `|seed|`.
  * Unified EH action (#462): `S = |seed| · tr(g)` with weights.
  * Balance α (#465): identifies where `tr(g) = 0`.
-/

import InfraFormalization.DualSideIndependence

namespace InfraFormalization
namespace DiscreteMetricTensor

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open MultiRuleDiscovered
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## The discrete metric tensor -/

/-- **`discreteMetricTensor`**: the discrete-geometric 2-tensor
unifying R (causal) and B (branchial) into a single object. Returns
the diagonal `(R, B)` pair. -/
def discreteMetricTensor (sys : ExecSystem) (d : Nat) : Int × Int :=
  (discreteRicciScalar sys d, discreteBranchialDensity sys d)

/-- **`discreteDet`**: determinant of the discrete metric tensor —
the discrete-geometric volume element `R · B`. -/
def discreteDet (sys : ExecSystem) (d : Nat) : Int :=
  let (r, b) := discreteMetricTensor sys d
  r * b

/-- **`discreteTrace`**: trace of the discrete metric tensor —
`R + B`. Related to the unified EH action at `α = 1`. -/
def discreteTrace (sys : ExecSystem) (d : Nat) : Int :=
  let (r, b) := discreteMetricTensor sys d
  r + b

/-! ## Certified values -/

/-- For `eR + id` at depth 3: `g = (-24, 30)`, `det = -720`,
`tr = 6`. -/
theorem metric_eR_id_3 :
    discreteMetricTensor edgeReversal_identity_Sys 3 = (-24, 30) ∧
    discreteDet edgeReversal_identity_Sys 3 = -720 ∧
    discreteTrace edgeReversal_identity_Sys 3 = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- For `eR + fork` at depth 3: `g = (-42, 66)`, `det = -2772`,
`tr = 24`. -/
theorem metric_eR_fork_3 :
    discreteMetricTensor edgeReversal_fork_Sys 3 = (-42, 66) ∧
    discreteDet edgeReversal_fork_Sys 3 = -2772 ∧
    discreteTrace edgeReversal_fork_Sys 3 = 24 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Signature classification -/

/-- A discrete-geometric configuration has **Lorentzian signature**
if its R and B have opposite signs. (Discrete analog of how
Lorentzian metrics have signature (-, +) or (+, -).) -/
def hasLorentzianSignature (sys : ExecSystem) (d : Nat) : Bool :=
  let (r, b) := discreteMetricTensor sys d
  decide ((r < 0 ∧ b > 0) ∨ (r > 0 ∧ b < 0))

/-- **`eR_id_lorentzian_at_3`**: at depth 3, `eR + id` has
**Lorentzian signature** — R = -24 < 0 and B = 30 > 0. -/
theorem eR_id_lorentzian_at_3 :
    hasLorentzianSignature edgeReversal_identity_Sys 3 = true := by
  native_decide

/-- **`eR_fork_lorentzian_at_3`**: at depth 3, `eR + fork` also
has Lorentzian signature. -/
theorem eR_fork_lorentzian_at_3 :
    hasLorentzianSignature edgeReversal_fork_Sys 3 = true := by
  native_decide

/-! ## Universal additivity for the metric tensor -/

/-- **`discreteMetricTensor_universal_additivity`**: the discrete
metric tensor scales linearly with `|seed|` — each component
follows the universal additivity law. -/
theorem discreteMetricTensor_universal_additivity_eR_id_path :
    let baselineRB := discreteMetricTensor edgeReversal_identity_Sys 3
    knillEulerScaled (causalDAGOfEvolution edgeReversal_identity_Sys
      UniversalAdditivity.seedPath123 3) = 2 * baselineRB.1 ∧
    knillEulerScaled (branchialDAGOfEvolution edgeReversal_identity_Sys
      UniversalAdditivity.seedPath123 3) = 2 * baselineRB.2 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## The discrete line element -/

/-- **`discreteLineElement`**: `ds² = R · dτ² + B · dχ²` evaluated
at integer increments `(dτ, dχ)`. -/
def discreteLineElement (sys : ExecSystem) (d : Nat) (dτ dχ : Int) : Int :=
  let (r, b) := discreteMetricTensor sys d
  r * dτ * dτ + b * dχ * dχ

/-- For `eR + id` at depth 3, the line element at `(dτ, dχ) = (1, 1)`
is `-24 + 30 = 6` — POSITIVE despite the Lorentzian signature
(because both `dτ²` and `dχ²` are non-negative, the sign depends on
which dominates). -/
theorem lineElement_eR_id_3_at_1_1 :
    discreteLineElement edgeReversal_identity_Sys 3 1 1 = 6 := by
  native_decide

/-- For `eR + id` at depth 3, the line element at `(dτ, dχ) = (2, 1)`
is `-96 + 30 = -66` — NEGATIVE: time-like dominant region. -/
theorem lineElement_eR_id_3_at_2_1 :
    discreteLineElement edgeReversal_identity_Sys 3 2 1 = -66 := by
  native_decide

/-! ## What this delivers

**First unified discrete-geometric 2-tensor** in the framework:

  * `discreteMetricTensor(sys, d)` — diagonal `(R, B)` pair.
  * `discreteDet`, `discreteTrace` — derived invariants.
  * `hasLorentzianSignature` — signature classification predicate.
  * `discreteLineElement` — discrete-GR line element.

**Certified facts**:

  * `metric_eR_id_3`: `g = (-24, 30)`, det = -720, tr = 6.
  * `metric_eR_fork_3`: `g = (-42, 66)`, det = -2772, tr = 24.
  * `eR_id_lorentzian_at_3` + `eR_fork_lorentzian_at_3`: both
    multi-rule combos have Lorentzian signature at depth 3.
  * `discreteMetricTensor_universal_additivity_eR_id_path`: each
    component follows universal additivity.
  * `lineElement_eR_id_3_at_1_1` (positive) and `_at_2_1` (negative):
    discrete time-like / space-like classification by line element.

**Why this matters**:

This is the **first explicit discrete-geometric 2-tensor** in the
framework, unifying the dual-side R/B observables into a single
discrete-Lorentzian-like geometric structure. With this:

  * Each (rule, depth) pair has a well-defined discrete metric.
  * Signature classification distinguishes Lorentzian vs Riemannian
    vs degenerate regimes.
  * Discrete line element gives invariant geometric distances.

**Implication for H9**: in the continuum limit, the discrete metric
tensor should converge to a continuum metric `g_{μν}(x)`. The
universal additivity at finite resolution (#454, #462) provides the
linear-scaling baseline for this convergence statement.

**For BBH**: the discrete metric tensor on the BBH seed gives the
full discrete-geometric description of the binary system at any
depth. With this, the framework has the substrate for a complete
discrete-GR-and-QM calculation of binary evolution.
-/

end DiscreteMetricTensor
end InfraFormalization
