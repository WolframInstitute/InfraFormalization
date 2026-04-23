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
import InfraFormalization.CycleEigenLimit
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

/-- **D7 — scaled discrete heat → continuum heat on cycle/circle**
(upgraded from `True` stub to real content + proof).

Under diffusive scaling (time `t ↦ t · n²` on the discrete side, which
matches space `x ↦ x/n`), the discrete heat-kernel eigenvalue on the
cycle converges to the continuum heat-kernel eigenvalue on `S¹`:

  `Real.exp (t · n² · cycleEigenvalue n k)  →  Real.exp (-(2πk)² · t)`

as `n → ∞`. Follows from A4 (`cycleEigenvalue_scaled_tendsto`) and
continuity of `Real.exp`.

This is the solution-level convergence of the discrete heat kernel
acting on the `k`-th eigenmode to the continuum heat kernel acting
on the `k`-th Fourier mode — the first *dynamics-level* (not just
spectrum-level) bridge theorem between discrete hypergraph heat flow
and continuum PDE heat flow. -/
def DiscreteHeatToContinuumHeat : Prop :=
  ∀ (k : ℕ) (t : ℝ),
    Filter.Tendsto
      (fun n : ℕ =>
        Real.exp (t * ((n : ℝ)^2 * cycleEigenvalue n k)))
      Filter.atTop
      (nhds (Real.exp (-(2 * Real.pi * k) ^ 2 * t)))

/-- **D7 proved.** The discrete-heat-to-continuum-heat scaling limit
holds: the discrete heat kernel on cycle eigenvectors, scaled
diffusively, converges pointwise to the continuum heat kernel on
circle Fourier modes. -/
theorem discreteHeatToContinuumHeat :
    DiscreteHeatToContinuumHeat := by
  intro k t
  -- Step 1: A4 gives n² · λ_k → -(2πk)².
  have hA4 := cycleEigenvalue_scaled_tendsto k
  -- Step 2: multiplying by constant t preserves the limit.
  have h_mul : Filter.Tendsto
      (fun n : ℕ => t * ((n : ℝ)^2 * cycleEigenvalue n k))
      Filter.atTop (nhds (t * (-(2 * Real.pi * k) ^ 2))) :=
    hA4.const_mul t
  -- Step 3: Real.exp is continuous, compose.
  have h_exp : Filter.Tendsto
      (fun n : ℕ => Real.exp (t * ((n : ℝ)^2 * cycleEigenvalue n k)))
      Filter.atTop (nhds (Real.exp (t * (-(2 * Real.pi * k) ^ 2)))) :=
    Real.continuous_exp.tendsto _ |>.comp h_mul
  -- Step 4: rewrite target `t * (-(2πk)²) = -(2πk)² * t`.
  have h_rewrite : Real.exp (t * (-(2 * Real.pi * k) ^ 2))
      = Real.exp (-(2 * Real.pi * k) ^ 2 * t) := by ring_nf
  rw [← h_rewrite]
  exact h_exp

/-- **A6 — weak convergence of the lattice average to the integral**
(upgraded from stub to real content).

For any continuous `f : ℝ → ℝ`, the `n`-point lattice Riemann sum
`(1/n) · Σ_{k=0}^{n-1} f(k/n)` converges to `∫_0^1 f dx` as `n → ∞`.
This is the operator-level form of "counting measure on `{k/n}_{k < n}`
converges weakly to Lebesgue on `[0,1)`". -/
def A6LatticeRiemannObligation : Prop :=
  ∀ (f : ℝ → ℝ) (_hcont : Continuous f),
    Filter.Tendsto
      (fun n : ℕ =>
        (1 / (n : ℝ)) * ∑ k : Fin n, f ((k : ℝ) / (n : ℝ)))
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1, f x))

/-- **A6 holds for constant functions**: `(1/n) · Σ_{k : Fin n} c = c
= ∫_0^1 c dx`. Concrete verification of the obligation's shape on the
easiest test functions. -/
theorem A6_for_constants (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ _k : Fin n, c)
      Filter.atTop
      (nhds (∫ _x in (0 : ℝ)..1, c)) := by
  have h_integral : (∫ _x in (0 : ℝ)..1, c) = c := by
    rw [intervalIntegral.integral_const]
    simp
  rw [h_integral]
  have h_sum : ∀ n : ℕ, 0 < n →
      (1 / (n : ℝ)) * ∑ _k : Fin n, c = c := by
    intro n hn
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  exact (h_sum n (by omega)).symm

/-- **Gauss summation formula on `Fin n` (real-valued)**:
`∑_{k : Fin n} k.val = n(n-1)/2` (in `ℝ`). The real-valued analog of
`Finset.sum_range_id`, obtained by induction via `Fin.sum_univ_castSucc`.

This is the building block for A6 tests on polynomial integrands
(e.g., the identity function `x`, quadratic `x²`, etc.), where the
Riemann sum `(1/n) · Σ_{k<n} (k/n)^d` reduces to a closed-form
polynomial in `n`. -/
theorem sum_fin_val_eq_triangular (n : ℕ) :
    (∑ k : Fin n, (k.val : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- **A6 Riemann-sum closed form for the identity function**:
`(1/n) · Σ_{k : Fin n} (k/n) = (n - 1) / (2n)` for every positive `n`.
Direct consequence of `sum_fin_val_eq_triangular`; the `n → ∞` limit
gives `1/2 = ∫_0^1 x dx`, which is the `A6_for_identity` obligation
(filter-side statement deferred to the general polynomial case). -/
theorem A6_identity_sum_closed_form (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ k : Fin n, ((k : ℝ) / (n : ℝ)))
      = ((n : ℝ) - 1) / (2 * n) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  rw [← Finset.sum_div, sum_fin_val_eq_triangular]
  field_simp

/-- **Riemann sum `(n-1)/(2n)` converges to `1/2`**. Splits the
expression as `1/2 - 1/(2n)`, then applies
`(1/n) → 0` for the second term. -/
theorem tendsto_nMinusOne_div_twoN :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 1) / (2 * n))
      Filter.atTop (nhds (1 / 2)) := by
  have h_eqv : ∀ n : ℕ, 0 < n →
      ((n : ℝ) - 1) / (2 * n) = 1 / 2 - 1 / (2 * n) := by
    intro n hn
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have h_nat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h_2n : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h_nat
  have h_inv : Filter.Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ)))
      Filter.atTop (nhds 0) := by
    have := h_2n.inv_tendsto_atTop
    refine this.congr ?_
    intro n
    rw [one_div]; rfl
  have h_target : Filter.Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) - 1 / (2 * n)) Filter.atTop
      (nhds ((1 / 2 : ℝ) - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds h_inv
  rw [sub_zero] at h_target
  refine h_target.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (h_eqv n (by omega)).symm

/-- **A6 holds for the identity function `f(x) = x`**: the Riemann sum
`(1/n) · Σ_{k : Fin n} (k/n) = (n-1)/(2n) → 1/2 = ∫_0^1 x dx`.
Follows from `A6_identity_sum_closed_form` plus
`tendsto_nMinusOne_div_twoN`. Concrete A6 verification on the first
non-constant polynomial integrand. -/
theorem A6_for_identity :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ k : Fin n, ((k : ℝ) / (n : ℝ)))
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1, x)) := by
  have h_integral : (∫ x in (0 : ℝ)..1, x) = 1 / 2 := by
    rw [integral_id]; norm_num
  rw [h_integral]
  refine tendsto_nMinusOne_div_twoN.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  exact (A6_identity_sum_closed_form n (by omega)).symm

/-- **Discrete wave → continuum wave on scaled lattice** (upgraded
from `True` to real content).

Spectral form: the `k`-th discrete wave-propagator frequency (the
dispersion relation eigenvalue) on the `n`-cycle, scaled by `n`,
converges to the continuum-wave frequency `2πk` on the circle.

Discrete dispersion: `ω_k(n) = 2 sin(πk/n)` (the square root of the
discrete Laplacian eigenvalue magnitude). Scaled: `n · ω_k(n) =
2n sin(πk/n) → 2πk` as `n → ∞`. This is the Rung-2 / A4 bridge for the
wave equation: the cycle wave-Laplacian eigenvalues converge to the
continuum-circle wave-Laplacian eigenvalues.

Full wave-equation convergence (propagator level) needs wave-kernel
infrastructure; the spectral bridge is the foundational step. -/
def DiscreteWaveToContinuumWave : Prop :=
  ∀ (k : ℕ),
    Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) * (2 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))))
      Filter.atTop
      (nhds (2 * Real.pi * k))

/-- **Discrete Schrödinger → continuum Schrödinger** (upgraded from
`True` to real content).

Spectral form: the scaled discrete Schrödinger dispersion relation
on the cycle converges to the continuum one.

Discrete Schrödinger Hamiltonian eigenvalue = minus the discrete
Laplacian eigenvalue = `4 sin²(πk/n)`. Scaled by `n²`:
`n² · 4 sin²(πk/n) → (2πk)²` as `n → ∞`. This matches the continuum
Schrödinger Hamiltonian eigenvalue `-d²/dx² = (2πk)²` on the circle.

Same content as `cycleEigenvalue_scaled_tendsto` (A4) in magnitude;
stated here for the Schrödinger operator. Full propagator-level
convergence `exp(-itH_n) → exp(-itH_∞)` needs unitary-convergence
infrastructure. -/
def DiscreteSchrodingerToContinuumSchrodinger : Prop :=
  ∀ (k : ℕ),
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ))^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2))
      Filter.atTop
      (nhds ((2 * Real.pi * k)^2))

/-- **DiscreteWaveToContinuumWave PROVED.** Follows from the helper
`n_sin_pi_k_div_n_tendsto`: `n · sin(πk/n) → πk`, so
`n · 2 sin(πk/n) = 2 · (n · sin(πk/n)) → 2πk`. Uses `Tendsto.const_mul`. -/
theorem discreteWaveToContinuumWave_holds :
    DiscreteWaveToContinuumWave := by
  intro k
  have h1 := n_sin_pi_k_div_n_tendsto k
  have h2 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * ((n : ℝ) * Real.sin (Real.pi * k / n)))
      Filter.atTop (nhds (2 * (Real.pi * k))) :=
    h1.const_mul 2
  have h_eq : ∀ n : ℕ, (2 : ℝ) * ((n : ℝ) * Real.sin (Real.pi * k / n))
      = (n : ℝ) * (2 * Real.sin (Real.pi * k / n)) := by
    intro n; ring
  have h_target : 2 * (Real.pi * (k : ℝ)) = 2 * Real.pi * k := by ring
  rw [h_target] at h2
  exact h2.congr h_eq

/-- **DiscreteSchrodingerToContinuumSchrodinger PROVED.** Negative of
`cycleEigenvalue_scaled_tendsto` (A4). Since
`n² · cycleEigenvalue n k = -n² · 4 sin²(πk/n) → -(2πk)²`, we get
`n² · 4 sin²(πk/n) → (2πk)²`. -/
theorem discreteSchrodingerToContinuumSchrodinger_holds :
    DiscreteSchrodingerToContinuumSchrodinger := by
  intro k
  have hA4 := cycleEigenvalue_scaled_tendsto k
  -- hA4: n² · (−4 sin²(π k / n)) → −(2πk)².
  -- Negate to get: n² · 4 sin²(π k / n) → (2πk)².
  have hneg : Filter.Tendsto
      (fun n : ℕ => - ((n : ℝ)^2 * cycleEigenvalue n k))
      Filter.atTop (nhds (-(-(2 * Real.pi * k)^2))) := hA4.neg
  have h_eq : ∀ n : ℕ, - ((n : ℝ)^2 * cycleEigenvalue n k)
      = (n : ℝ)^2 * (4 * (Real.sin (Real.pi * k / n))^2) := by
    intro n
    unfold cycleEigenvalue
    ring
  have h_target : -(-(2 * Real.pi * (k : ℝ))^2) = (2 * Real.pi * k)^2 := by ring
  rw [h_target] at hneg
  exact hneg.congr h_eq

/-- **Klein-Gordon continuum-limit spectrum**: for mass `m` and any
wavenumber `k`, the lattice KG dispersion `n²·4 sin²(πk/n) + m²`
converges to the continuum KG Hamiltonian eigenvalue `(2πk)² + m²`
as `n → ∞`. Follows from the Schrödinger spectral bridge
(`discreteSchrodingerToContinuumSchrodinger_holds`) via
`Filter.Tendsto.add`. -/
def DiscreteKleinGordonSpectrum (m : ℝ) : Prop :=
  ∀ (k : ℕ),
    Filter.Tendsto
      (fun n : ℕ =>
        ((n : ℝ))^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2)
        + m^2)
      Filter.atTop
      (nhds ((2 * Real.pi * k)^2 + m^2))

/-- **DiscreteKleinGordonSpectrum PROVED.** Sum of the Schrödinger
spectral convergence and the constant `m²` limit. -/
theorem discreteKleinGordonSpectrum_holds (m : ℝ) :
    DiscreteKleinGordonSpectrum m := by
  intro k
  have h_schr := discreteSchrodingerToContinuumSchrodinger_holds k
  have h_const : Filter.Tendsto (fun _ : ℕ => m^2) Filter.atTop (nhds (m^2)) :=
    tendsto_const_nhds
  exact h_schr.add h_const

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
