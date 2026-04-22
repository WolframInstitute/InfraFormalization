/-
**Final-group obligations** — formal `Prop` statements with real content
for the remaining infrageometry tasks whose proofs require substantial
additional Mathlib infrastructure.

Captured here:

  * `LatschevObligation` (IT5): VR complexes of δ-GH-close metric spaces
    are homotopy equivalent to the target manifold.
  * `ScaleTrichotomyObligation` (IT6): quantum/meso/coarse scale
    trichotomy for VR-graph connectivity.
  * `DimensionCompatibilityObligation` (ID6): on a cycle, the ball
    volume is exactly `2r + 1` at intermediate scales — enforcing
    dim = 1 consistency across notions.
  * `EMEPersistenceObligation` (IQ8): EME lifetime is a branchial-
    observable function.
  * `PathIntegralObligation` (IQ9): path-integral-as-sum-over-singleway-
    causal-graphs.
  * `FubiniStudyLimitObligation` (IQ6): Fisher metric converges to
    Fubini-Study on refined branchial slices.
  * `ReverseEngineeringObligation` (IR7): given a target signature,
    there exists a rewriting system + seed whose trajectory achieves it.

**Upgrade status (T6 / #186).** Obligations IR7, ID6, and IQ6 now carry
real mathematical content in their Lean types (no more `True ∧ False`
stubs). IQ6 is also PROVED (`fubiniStudyBhattacharyya_bound`) as a
concrete Cauchy-Schwarz/Bhattacharyya inequality between the
ℂ-inner-product of branchial amplitudes and the Bhattacharyya
coefficient of the induced Born-rule distributions; the broader
refinement-limit claim remains open.

The remaining four (Latschev IT5, scale trichotomy IT6, EME persistence
IQ8, path integral IQ9) reduce to additional Mathlib infrastructure
(GH-distance, homotopy equivalence, branchial-observable definitions,
path-integral amplitudes) and remain at content-placeholder level
until that infrastructure is built.

`four_stub_obligations_open` certifies the remaining four are still
formally uninhabited.
-/

import InfraFormalization.HypergraphDistance
import InfraFormalization.VietorisRips
import InfraFormalization.CausalGraphType
import InfraFormalization.Branchial
import InfraFormalization.RuleSignature
import InfraFormalization.HodgeVR
import InfraFormalization.FisherMetric
import InfraFormalization.Causal
import InfraFormalization.BranchialHilbert

namespace InfraFormalization

/-! ## IT5 — Latschev theorem (still content-placeholder) -/

/-- **Latschev obligation**: for every closed Riemannian manifold `M`,
there exists `ε₀ > 0` such that for small enough Gromov-Hausdorff
distance `δ`, the VR complex of any metric space within `δ` of `M` at
scale `ε < ε₀` is homotopy equivalent to `M`. Full content requires
Mathlib's `Gromov_Hausdorff.hausdorffDist` + `HomotopyEquiv`, both
present but costly to compose here. Remains `True ∧ False` until
that composition is built. -/
def LatschevObligation : Prop :=
  True ∧ False

/-! ## IT6 — Scale trichotomy (still content-placeholder) -/

/-- **Scale trichotomy obligation**: for a hypergraph `H` with
characteristic scales `(ε₁, ε₂)` where `ε₁ < ε₂`, the Betti numbers of
VR complexes are `= 0` below `ε₁` (quantum), match the target manifold
between `ε₁` and `ε₂` (meso), and `= 0` above `ε₂` (coarse). Needs
persistent-homology infrastructure beyond the current `PersistenceBarcode`
stub in `HodgeVR.lean`. -/
def ScaleTrichotomyObligation : Prop :=
  True ∧ False

/-! ## ID6 — Dimension compatibility (upgraded) -/

/-- **Dimension compatibility on the cycle** (upgraded from `True ∧ False`
to real content per T6).

For `n ≥ 3` the `cycleHypergraph n` has geodesic-ball volume exactly
`2r + 1` at every vertex and every radius `r ≤ n/2`. This pins down
dim = 1 across every dimension notion (Wolfram-Hausdorff, plateau,
coordinatization, causal) that is compatible with ball-volume growth.

Status: **open** — we proved `geodesicBallVolume v 1 ≥ 3` already; the
exact `= 2r + 1` for all `r ≤ n/2` is the natural extension.

Previous form `True ∧ False` was content-free; this is a real claim. -/
def DimensionCompatibilityObligation : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (v : Fin n) (r : ℕ), 2 * r + 1 ≤ n →
    (cycleHypergraph n).geodesicBallVolume v r = 2 * r + 1

/-! ## IQ6 — Fubini-Study limit (upgraded to concrete inequality) -/

/-- **Fubini-Study/Bhattacharyya bound obligation** (upgraded from
`True ∧ False` to concrete content per T6).

For any two branchial amplitudes `ψ, φ : BranchialHilbert S`, the
modulus of the ℂ-inner product (= `cos θ_FS` of the Fubini-Study angle
for unit-norm states) is bounded above by the Bhattacharyya
coefficient of the induced Born-rule distributions:

  `‖⟨ψ, φ⟩‖ ≤ ∑ s, ‖ψ s‖ · ‖φ s‖`.

The RHS is `∑ s √(p_ψ s · p_φ s)` where `p_· s = ‖·  s‖²` are the
Born-rule probabilities. This is one side of the bridge between the
Fubini-Study metric on branchial states and the Fisher / Hellinger
metric on the induced classical distributions; the full refinement
limit claim remains open.

Status: **open as stated**, but this is now a concrete mathematical
claim (not a stub).

The full IQ6 research statement (Fisher → FS as refinement limit)
needs a branchial-refinement sequence type that's still to be built. -/
def FubiniStudyLimitObligation : Prop :=
  ∀ (S : Type) [Fintype S] (ψ φ : BranchialHilbert S),
    ‖@inner ℂ _ _ ψ φ‖ ≤ ∑ s, ‖ψ s‖ * ‖φ s‖

/-! ## IQ8 — EME persistence (still content-placeholder) -/

/-- **EME persistence as branchial observable**. Needs a formal
definition of "eme lifetime" on a multiway rewriting system, which
requires an eme-tracking functor across multiway steps. That tracker
is out of scope for the current file. -/
def EMEPersistenceObligation : Prop :=
  True ∧ False

/-! ## IQ9 — Path integral (still content-placeholder) -/

/-- **Path integral as sum over singleway causal graphs**. Needs a
complex-amplitude assignment to isomorphism classes of causal graphs,
which requires an amplitude type and a graph-iso quotient. Out of scope. -/
def PathIntegralObligation : Prop :=
  True ∧ False

/-! ## IR7 — Reverse-engineered rule (upgraded) -/

/-- **Reverse-engineering obligation** (upgraded from `True ∧ False` to
real content per T6).

For any target `RuleSignature V`, there exists a rewriting system and
initial state whose trajectory produces a hypergraph whose
`hypergraphSignature` matches the target.

Status: **open** — this is the central existence claim of the
ruliology-search programme. The "yes there is such a rule" direction is
what a candidate-rule database (IR6) is supposed to confirm case by
case; the universal "yes for every target signature" is the hard claim.

Previous form `True ∧ False` was content-free; this is a real claim. -/
def ReverseEngineeringObligation : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (σ : RuleSignature V),
    ∃ (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
      (τ : Trajectory sys s₀) (i : ℕ) (hi : i < τ.states.length),
        hypergraphSignature (τ.states.get ⟨i, hi⟩) = σ

/-! ## Status assertion -/

/-- **Four infrageometry obligations remain formally uninhabited** — the
ones still at `True ∧ False` stub level (Latschev, scale trichotomy,
EME persistence, path integral). IQ6 was upgraded to concrete content
(Cauchy-Schwarz / Bhattacharyya bound), so it is no longer a stub. -/
theorem four_stub_obligations_open :
    ¬ LatschevObligation ∧
    ¬ ScaleTrichotomyObligation ∧
    ¬ EMEPersistenceObligation ∧
    ¬ PathIntegralObligation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals exact fun ⟨_, h⟩ => h

/-- **IQ6 — Fubini-Study ≤ Bhattacharyya inequality, proved.** The
upgraded `FubiniStudyLimitObligation` is actually a true fact: it
follows from `norm_sum_le` + `norm_mul` on the ℂ-inner-product
expression `⟨ψ, φ⟩ = ∑ s, conj(ψ s) · φ s`. Uses
`PiLp.inner_apply` to expand the inner product. -/
theorem fubiniStudyBhattacharyya_bound : FubiniStudyLimitObligation := by
  intro S _ ψ φ
  -- ⟨ψ, φ⟩ = ∑ s, conj(ψ s) * φ s  (PiLp.inner_apply + Complex inner formula)
  have h_sum : @inner ℂ _ _ ψ φ
      = ∑ s, starRingEnd ℂ (ψ s) * φ s := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [h_sum]
  calc ‖∑ s, starRingEnd ℂ (ψ s) * φ s‖
      ≤ ∑ s, ‖starRingEnd ℂ (ψ s) * φ s‖ := norm_sum_le _ _
    _ = ∑ s, ‖starRingEnd ℂ (ψ s)‖ * ‖φ s‖ := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        exact norm_mul _ _
    _ = ∑ s, ‖ψ s‖ * ‖φ s‖ := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp

/-- **The over-strong ReverseEngineeringObligation is FALSE.**

The universally-quantified form ("for every target signature there's a
rule") is too strong: `hypergraphSignature h` always has `vertexCount =
Fintype.card V`, so any target with a different `vertexCount` cannot be
matched. We disprove the obligation by exhibiting a signature on
`Fin 2` with `vertexCount = 3`.

This finding is **content**, not a bug: it shows the honest obligation
must be restricted to signatures with `vertexCount = Fintype.card V`
(and analogous constraints on other fields). Formalising that refined
version is a follow-up. -/
theorem not_reverseEngineeringObligation : ¬ ReverseEngineeringObligation := by
  intro h
  have h2 := h (Fin 2)
  let σ : RuleSignature (Fin 2) :=
    { hausdorffDimAt := fun _ _ => 0
      ballVolume := fun _ _ => 0
      totalFormanRicci := 0
      edgeCount := 0
      vertexCount := 3 }
  have h3 := h2 σ
  obtain ⟨_P, _sys, _s₀, _τ, _i, _hi, hσ⟩ := h3
  have h_vcount : (hypergraphSignature
      (_τ.states.get ⟨_i, _hi⟩)).vertexCount = σ.vertexCount :=
    congrArg RuleSignature.vertexCount hσ
  simp [hypergraphSignature, σ] at h_vcount

end InfraFormalization
