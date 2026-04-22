/-
**Branchial Hilbert space** (task R3 / #178 partial).

For a finite `Fintype` `S` (interpreted as a branchial slice), the
ℂ-valued functions `S → ℂ` form a finite-dimensional complex Hilbert
space. Via Mathlib's `EuclideanSpace ℂ S`, this is automatic.

This file:

  * Defines `BranchialHilbert S := EuclideanSpace ℂ S` (type alias).
  * Confirms the Hilbert-space instance is inherited.
  * Defines a branchial adjacency operator at the function level
    (`branchialAdj`) given a `Finset.Adj`-style predicate, built as
    a ℂ-linear map so additivity and ℂ-linearity are automatic.

**Connection to hypergraphs.** Given a rewriting system `sys` and a
seed `s₀` such that the `n`-th branchial slice is finite (via
`branchialSliceFinite_of_successors_finite` from `BranchialFinite.lean`,
I1 / #84), one can pick a `Fintype` representative of the slice and
instantiate `BranchialHilbert` on it. The connection is not automated
here — it requires extracting a Fintype from `Set.Finite`, which is
straightforward via `Set.Finite.toFinset`.

**Status.** Partial R3: the Hilbert-space framework is in place and the
adjacency operator is stated as a ℂ-linear map; self-adjointness (for
symmetric `adj`) and the full unitary branchial evolution (Schrödinger
on branchial slices) remain follow-ups.
-/

import InfraFormalization.BranchialFinite
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace InfraFormalization

/-- **Branchial Hilbert space** on a finite index type `S`. Alias for
`EuclideanSpace ℂ S` — Mathlib's canonical finite-dim `ℓ²`. -/
abbrev BranchialHilbert (S : Type*) [Fintype S] : Type _ :=
  EuclideanSpace ℂ S

noncomputable instance (S : Type*) [Fintype S] :
    NormedAddCommGroup (BranchialHilbert S) := inferInstance

noncomputable instance (S : Type*) [Fintype S] :
    InnerProductSpace ℂ (BranchialHilbert S) := inferInstance

noncomputable instance (S : Type*) [Fintype S] :
    CompleteSpace (BranchialHilbert S) := inferInstance

/-- **Branchial adjacency operator** as a ℂ-linear map on
`BranchialHilbert S`, given an adjacency predicate `adj : S → S → Prop`.
At each vertex `v`, the image is the sum of `ψ`'s values over all
`u` with `adj v u`, i.e. the graph-adjacency action.

Defined via `WithLp.toLp` / `WithLp.ofLp` so the Pi-level linear
structure carries through cleanly; the map is ℂ-linear automatically. -/
noncomputable def branchialAdjLM {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] :
    BranchialHilbert S →ₗ[ℂ] BranchialHilbert S where
  toFun ψ :=
    WithLp.toLp 2
      (fun v => ∑ u ∈ Finset.univ.filter (fun u => adj v u),
        (WithLp.ofLp ψ : S → ℂ) u)
  map_add' ψ φ := by
    refine PiLp.ext (fun v => ?_)
    simp only [WithLp.ofLp_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ψ := by
    refine PiLp.ext (fun v => ?_)
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]

/-- **Branchial adjacency operator** (plain function form). The
`LinearMap` version is `branchialAdjLM`; use that when ℂ-linearity
is needed. -/
noncomputable def branchialAdj {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] (ψ : BranchialHilbert S) :
    BranchialHilbert S :=
  branchialAdjLM adj ψ

/-- **Branchial adjacency is additive** (follows from the `LinearMap`
structure). -/
theorem branchialAdj_add {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj]
    (ψ φ : BranchialHilbert S) :
    branchialAdj adj (ψ + φ) = branchialAdj adj ψ + branchialAdj adj φ :=
  (branchialAdjLM adj).map_add ψ φ

/-- **Branchial adjacency commutes with scalar multiplication** (follows
from the `LinearMap` structure). -/
theorem branchialAdj_smul {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] (c : ℂ) (ψ : BranchialHilbert S) :
    branchialAdj adj (c • ψ) = c • branchialAdj adj ψ :=
  (branchialAdjLM adj).map_smul c ψ

/-- **Self-adjointness of `branchialAdjLM` for symmetric `adj`.** The
graph-style adjacency operator is Hermitian whenever the underlying
adjacency predicate is symmetric — this is the finite-dimensional
spectral-theorem prerequisite for a real spectrum. -/
theorem branchialAdjLM_inner {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] (hsymm : ∀ a b, adj a b → adj b a)
    (ψ φ : BranchialHilbert S) :
    @inner ℂ _ _ (branchialAdjLM adj ψ) φ = @inner ℂ _ _ ψ (branchialAdjLM adj φ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, branchialAdjLM, LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp, map_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
  by_cases h : adj u v
  · simp [h, hsymm _ _ h]
  · have h' : ¬ adj v u := fun h' => h (hsymm _ _ h')
    simp [h, h']

/-! ### Branchial amplitudes and the Born-rule probability

In the Wolfram-model QM bridge, a **branchial amplitude** is exactly a
wavefunction in `BranchialHilbert S`, and the induced **probability
distribution** on states is `|ψ|²` — the Born rule. We record those
definitions and the basic sanity facts (non-negativity, normalisation
under unit norm). -/

/-- **Branchial amplitude** = wavefunction in `BranchialHilbert S`. An
alias recording the physical interpretation (I3 / #86). -/
abbrev BranchialAmplitude (S : Type*) [Fintype S] : Type _ := BranchialHilbert S

/-- **Born-rule probability distribution** induced by an amplitude:
`bornProbability ψ s = |ψ s|²`. This is the induced mass assigned to
state `s` when observing the branchial amplitude. -/
noncomputable def bornProbability {S : Type*} [Fintype S]
    (ψ : BranchialAmplitude S) (s : S) : ℝ :=
  Complex.normSq (ψ s)

/-- **Born-rule is non-negative at every state**. -/
theorem bornProbability_nonneg {S : Type*} [Fintype S]
    (ψ : BranchialAmplitude S) (s : S) :
    0 ≤ bornProbability ψ s :=
  Complex.normSq_nonneg _

/-- **Born-rule is normalised to `‖ψ‖²`**. In particular, if `‖ψ‖ = 1`
then the Born probabilities sum to `1` and define a genuine probability
distribution on `S`. -/
theorem sum_bornProbability {S : Type*} [Fintype S]
    (ψ : BranchialAmplitude S) :
    ∑ s, bornProbability ψ s = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  unfold bornProbability
  rw [Real.sq_sqrt]
  · simp only [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _)]
  · exact Finset.sum_nonneg (fun s _ => sq_nonneg _)

/-- **Uniform branchial weight** on a finite slice (I2 / #85). Every
element carries weight `1 / |S|`; summed over `S` this gives `1`,
i.e. a bona-fide discrete probability distribution. -/
noncomputable def branchialUniformWeight (S : Type*) [Fintype S]
    (_s : S) : ℝ :=
  (Fintype.card S : ℝ)⁻¹

/-- **Uniform branchial weight is non-negative**. -/
theorem branchialUniformWeight_nonneg (S : Type*) [Fintype S] (s : S) :
    0 ≤ branchialUniformWeight S s := by
  unfold branchialUniformWeight
  positivity

/-- **Uniform branchial weights sum to 1** when the slice is nonempty. -/
theorem sum_branchialUniformWeight (S : Type*) [Fintype S] [Nonempty S] :
    ∑ s : S, branchialUniformWeight S s = 1 := by
  unfold branchialUniformWeight
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  field_simp

/-! ### Expectation values (I7 / #90) -/

/-- **Expectation value** of a ℂ-linear operator `A` in the state `ψ`:
`⟨A⟩_ψ := ⟨ψ, A ψ⟩`. For a Hermitian `A` this is a real number; for
any `A` it is ℂ-linear in the right slot, conjugate-linear in the
left, making it a bona-fide quantum-mechanical matrix element. -/
noncomputable def expectationValue {S : Type*} [Fintype S]
    (A : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S)
    (ψ : BranchialHilbert S) : ℂ :=
  @inner ℂ _ _ ψ (A ψ)

/-- **Expectation value is real for Hermitian (self-adjoint) operators**.
If `A` satisfies `⟨A φ, ψ⟩ = ⟨φ, A ψ⟩` for all `φ, ψ`, then
`⟨A⟩_ψ = ⟨ψ, A ψ⟩` is a real number — one of the core observations of
quantum mechanics. -/
theorem expectationValue_re_of_symm {S : Type*} [Fintype S]
    (A : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S)
    (hsa : ∀ φ ψ : BranchialHilbert S, @inner ℂ _ _ (A φ) ψ = @inner ℂ _ _ φ (A ψ))
    (ψ : BranchialHilbert S) :
    starRingEnd ℂ (expectationValue A ψ) = expectationValue A ψ := by
  unfold expectationValue
  rw [inner_conj_symm]
  exact hsa ψ ψ

/-- **Born rule via expectation value.** For a Hermitian operator `A`
with eigenvector `ψ` of eigenvalue `a : ℝ`, the expectation value is
`a · ‖ψ‖²`. So unit-norm eigenvectors realize the eigenvalue as the
definite measurement outcome. -/
theorem expectationValue_eigenvector {S : Type*} [Fintype S]
    (A : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S)
    (ψ : BranchialHilbert S) (a : ℂ)
    (heigen : A ψ = a • ψ) :
    expectationValue A ψ = a * (@inner ℂ _ _ ψ ψ) := by
  unfold expectationValue
  rw [heigen, inner_smul_right]

/-! ### Observables (I6 / #89) -/

/-- **Quantum observable on a branchial Hilbert space** (I6 / #89).
A ℂ-linear self-adjoint operator `A : BranchialHilbert S →ₗ[ℂ]
BranchialHilbert S` — satisfying `⟨A φ, ψ⟩ = ⟨φ, A ψ⟩` for all
`φ, ψ`. The real-valued expectation values (via
`expectationValue_re_of_symm`) are the measurement outcomes. -/
structure BranchialObservable (S : Type*) [Fintype S] where
  /-- The underlying ℂ-linear operator. -/
  op : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S
  /-- Self-adjointness (Hermitianness). -/
  isSymm : ∀ φ ψ : BranchialHilbert S,
    @inner ℂ _ _ (op φ) ψ = @inner ℂ _ _ φ (op ψ)

/-- **The adjacency operator is a branchial observable** for symmetric
adjacency `adj`. Concrete instance connecting the Wolfram-model graph
structure to the observable interpretation. -/
noncomputable def branchialAdjObservable {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] (hsymm : ∀ a b, adj a b → adj b a) :
    BranchialObservable S where
  op := branchialAdjLM adj
  isSymm := branchialAdjLM_inner adj hsymm

/-- **Expectation values of observables are real**. -/
theorem BranchialObservable.expectationValue_real {S : Type*} [Fintype S]
    (A : BranchialObservable S) (ψ : BranchialHilbert S) :
    starRingEnd ℂ (expectationValue A.op ψ) = expectationValue A.op ψ :=
  expectationValue_re_of_symm A.op A.isSymm ψ

/-! ### Connection to the concrete branchial slice

Given the finite-successor hypothesis on a rewriting system, every
branchial slice at depth `n` is finite
(`branchialSliceFinite_of_successors_finite`). We turn that `Set.Finite`
witness into a Fintype so `BranchialHilbert` can be instantiated on
the concrete slice `↑(BranchialSlice sys s₀ n)`. -/

/-- Fintype on a finite branchial slice, extracted from the
`Set.Finite` witness. -/
@[reducible]
noncomputable def branchialSliceFintype {P V : Type*} [DecidableEq V]
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) :
    Fintype ↑(BranchialSlice sys s₀ n) :=
  h.fintype

/-- **Branchial Hilbert space on a concrete finite slice.** With the
finite-successor hypothesis supplied, `BranchialSlice sys s₀ n` is a
finite set, so ℓ²(slice) = `EuclideanSpace ℂ ↑(BranchialSlice sys s₀ n)`
is automatic. -/
noncomputable abbrev branchialSliceHilbert {P V : Type*} [DecidableEq V]
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) : Type _ :=
  @BranchialHilbert ↑(BranchialSlice sys s₀ n) (branchialSliceFintype sys s₀ n h)

end InfraFormalization
