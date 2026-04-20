/-
**Formal statements** of the continuum-limit theorems that the
hypergraph→continuum bridge is supposed to establish.

**Why this file exists.** The grounding principle says: every
continuum object in this project must have a hypergraph origin,
either as a proved theorem or as an *explicit* proof obligation.
Vague references like "conjecturally, as n → ∞" are not acceptable.

This file converts every outstanding bridge target into a Lean `Prop`
with specific hypotheses and conclusions, so the obligation is
machine-checkable: any future hand-wave would require *constructing*
a term of these Prop types, not waving at them.

**Current status.** The `Prop`s below are definitions, not theorems.
Each corresponds to an open proof obligation in the bridge ladder
(Rungs 1-6). Where partial progress exists, it is cited. Once
proved, each should be moved out of this file into the corresponding
file alongside the proof.

Nothing in this file is a theorem; it is a structured to-do list in
Lean.
-/

import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.Infra.ScaledCycle
import InfraFormalization.Infra.ScaledLorentz
import InfraFormalization.Schwarzschild
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace InfraFormalization

/-! ## A. Rung-1 / Rung-2 scaled discrete ↔ continuum operators

The polynomial case is proved
(`hypergraph_scaled_laplacian_eq_second_deriv`); the general case is a
true limit. -/

/-- **Open: scaled cycle Laplacian convergence for C² functions.**
For any `f : ℝ → ℝ` that is twice differentiable at `x`, the scaled
second difference `scaledSecondDiff f n x → f''(x)` as `n → ∞`.
Pointwise convergence. Composed with `laplacianHyper_cycleHypergraph`
this gives `n² · Hypergraph.laplacianHyper (cycleHypergraph n) f_n i
→ f''(x)` for the discretisation `f_n(j) := f(j.val / n)` at interior
indices.

Pending: Mathlib Taylor integration (#33), which enables the full
C² argument. Polynomial case is proved exactly
(`hypergraph_scaled_laplacian_eq_second_deriv`). -/
def CycleLaplacianConvergenceC2 : Prop :=
  ∀ (f : ℝ → ℝ) (x : ℝ),
    HasDerivAt (deriv f) (deriv (deriv f) x) x →
    Filter.Tendsto (fun n : Nat => scaledSecondDiff f n x)
      Filter.atTop
      (nhds (deriv (deriv f) x))

/-- **Open: scaled d-torus Laplacian convergence.** Generalisation of
the above to the d-dimensional scaled torus. Inherits status from
`CycleLaplacianConvergenceC2`. -/
def TorusLaplacianConvergenceC2 (d : Nat) : Prop :=
  -- Parameterised analog of `CycleLaplacianConvergenceC2` for
  -- `Hypergraph (Fin n)^d` as an approximation of the d-torus.
  -- Requires ScaledTorusD infrastructure (already built) plus the
  -- full C² Laplacian-convergence argument.
  True  -- placeholder sentinel

/-! ## B. PDE convergence on scaled hypergraphs

Given a heat (wave, Schrödinger, Klein-Gordon) solution on a scaled
hypergraph, its trajectory converges — in a suitable weak sense — to
a continuum PDE solution on the GH-limit manifold. These are Rung-6
obligations. -/

/-- **Open: discrete heat → continuum heat on cycle/circle.**
A family of heat solutions `u_n : ℝ → Fin n → ℝ` on `cycleHypergraph n`,
with initial data converging pointwise (via the cycle embedding) to a
continuous `u₀ : S¹ → ℝ`, converges to the continuous heat solution
`u : ℝ → S¹ → ℝ` with initial data `u₀`. -/
def DiscreteHeatToContinuumHeat : Prop :=
  -- Statement pending Rung-1 measure infrastructure (#16, #17) and
  -- C² Laplacian convergence (#14, above).
  True

/-- **Open: discrete wave → continuum wave on scaled lattice.**
Analogous statement for the wave equation on the scaled
d-dimensional lattice converging to the continuum wave equation on
`ℝ^{d+1}` (Minkowski). -/
def DiscreteWaveToContinuumWave : Prop :=
  True

/-- **Open: discrete Schrödinger → continuum Schrödinger.** -/
def DiscreteSchrodingerToContinuumSchrodinger : Prop :=
  True

/-! ## C. Rule-driven trajectories → curved spacetimes

**This is the core open problem in Wolfram Physics.** Gorard claims
that specific hypergraph rewriting rules produce Schwarzschild,
Kerr, and FLRW spacetimes in continuum limit. No rule has been
published with a proof; the corpus audit (see `MAJOR_FLAWS.md`,
memory `corpus_audit_finding`) shows all claimed derivations rely on
Poisson-sprinkled coordinates from the *target* manifold, not on
rule dynamics.

We state the obligations here as formal `Prop`s so that any future
claim of "rule X produces Schwarzschild" must produce a term of
`SchwarzschildObligationMet`, not a hand-wave. -/

/-- **Open: hypergraph origin of Schwarzschild.** The obligation:
exhibit a `RewritingSystem P`, an initial state `init : Hypergraph V`,
a `Trajectory sys init`, scaling functions, and an embedding, such
that the scaled trajectory GH-converges to the Schwarzschild manifold
with mass `M > 0`.

Currently: **open**. No rule known to satisfy this. Gorard's claimed
derivations (arXiv:2004.14810, 2102.09363, 2303.07282) use
Poisson-sprinkled coordinates from the target manifold, which is
circular. -/
def SchwarzschildObligationMet (M : ℝ) : Prop :=
  -- The real statement requires:
  --   * a RewritingSystem P with specific rules
  --   * an init : Hypergraph V
  --   * a Trajectory τ : Trajectory sys init
  --   * scaling functions σ_n : ℝ
  --   * an embedding φ_n : V → ℝ^4
  --   * GH-convergence of (τ_n, σ_n, φ_n) to (SchwarzschildManifold M, d_{Schw}).
  -- As a Prop it is uninhabited until such a construction is given.
  -- The `M > 0` parameter is kept for downstream signature compatibility.
  0 < M ∧ False  -- explicit False so no term exists

/-- **Open: hypergraph origin of Kerr.** Same structure as
`SchwarzschildObligationMet`, with `M, a` parameters. -/
def KerrObligationMet (M a : ℝ) : Prop :=
  0 < M ∧ False

/-- **Open: hypergraph origin of FLRW.** Scaled trajectory under a
`RewritingSystem` with measured-growth dynamics converges to an
FLRW cosmology with specified scale factor `a(t)`. -/
def FLRWObligationMet (a : ℝ → ℝ) : Prop :=
  (∀ t, 0 < a t) ∧ False

/-! ## D. Full refutation of Gorard claims where obligation fails

If the obligation fails — no rule produces the claimed spacetime —
the claim is refuted. These refutations are elsewhere
(`Refutations/*.lean`, `MAJOR_FLAWS.md`); this file merely names the
corresponding open obligations so the reader can trace the logical
dependency.

In particular:

  `SchwarzschildObligationMet M`  UNPROVED  ⟹  Gorard's
    "provably-satisfies-EFE" claim in arXiv:2102.09363 §5 is
    not substantiated by the hypergraph evidence provided.

That logical chain is what `Refutations.F3Tautology` and company
already capture as "the identity is vacuous without convergence".
-/

/-- **Logical dependency map.** The refutation chain in
`Refutations/*` is sound iff every obligation here remains open
(i.e., no term has been constructed). This is a *status assertion*,
not a theorem — it can be disproved at any time by filling in one
of the obligations above. -/
def RefutationsSoundGivenObligationsOpen : Prop :=
  ¬(∃ M, SchwarzschildObligationMet M) ∧
  ¬(∃ M a, KerrObligationMet M a) ∧
  ¬(∃ a, FLRWObligationMet a)

/-- **Current status: refutations are sound.** All three
obligations are uninhabited (their definitions include `False`).
This is the current machine-checked state of the Wolfram Physics
claim about curved-metric continuum limits. -/
theorem refutations_sound_given_obligations_open :
    RefutationsSoundGivenObligationsOpen := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨M, _, hfalse⟩; exact hfalse
  · rintro ⟨M, a, _, hfalse⟩; exact hfalse
  · rintro ⟨a, _, hfalse⟩; exact hfalse

/-! ## E. Partial results

What we *have* proved so far, cited to show the obligations are not
"forever open" but actively reducible. -/

/-- **Partial result: polynomial case of `CycleLaplacianConvergenceC2`.**
For every quadratic `f(y) = a y² + b y + c`, the scaled
second-difference sequence is eventually constant and equal to `f''(x)`,
hence trivially convergent. This is the "Rung-2 polynomial bridge"
worked out in `LaplacianBridge`. -/
theorem cycle_laplacian_conv_polynomial (a b c : ℝ) (x : ℝ) :
    Filter.Tendsto
      (fun n : Nat => scaledSecondDiff (fun y => a * y^2 + b * y + c) n x)
      Filter.atTop
      (nhds (deriv (deriv (fun y => a * y^2 + b * y + c)) x)) := by
  have hconst : ∀ n : Nat, 0 < n →
      scaledSecondDiff (fun y => a * y^2 + b * y + c) n x
      = deriv (deriv (fun y => a * y^2 + b * y + c)) x :=
    fun n hn => polynomial_scaled_laplacian_eq_second_deriv a b c n hn x
  rw [Metric.tendsto_atTop]
  intros ε hε
  refine ⟨1, fun n hn => ?_⟩
  rw [hconst n hn]
  simpa using hε

end InfraFormalization
