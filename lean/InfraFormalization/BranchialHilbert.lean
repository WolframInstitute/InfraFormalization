/-
The space `EuclideanSpace ℂ S` on a finite type `S`, with an adjacency operator and
expectation values.

The module defines `BranchialHilbert S := EuclideanSpace ℂ S`, the ℂ-linear adjacency
operator `branchialAdjLM` of a decidable relation, `bornProbability ψ s = |ψ s|²`, the
uniform weight `1 / |S|`, expectation values `⟨ψ, A ψ⟩`, and self-adjoint operators
(`BranchialObservable`). It proves that the adjacency operator of a symmetric relation is
self-adjoint, that `∑ s, |ψ s|² = ‖ψ‖²`, that the uniform weights sum to 1, and that
expectation values of self-adjoint operators equal their conjugates. It also instantiates
the space on a branchial slice that is given as finite.
-/

import InfraFormalization.BranchialFinite
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace InfraFormalization

/-- `EuclideanSpace ℂ S`, the space `ℓ²(S)` for a finite type `S`. -/
abbrev BranchialHilbert (S : Type*) [Fintype S] : Type _ :=
  EuclideanSpace ℂ S

noncomputable instance (S : Type*) [Fintype S] :
    NormedAddCommGroup (BranchialHilbert S) := inferInstance

noncomputable instance (S : Type*) [Fintype S] :
    InnerProductSpace ℂ (BranchialHilbert S) := inferInstance

noncomputable instance (S : Type*) [Fintype S] :
    CompleteSpace (BranchialHilbert S) := inferInstance

/-- The adjacency operator of `adj : S → S → Prop` as a ℂ-linear map:
`(A ψ)(v) = ∑_{u : adj v u} ψ(u)`. -/
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

/-- The function underlying `branchialAdjLM adj`. -/
noncomputable def branchialAdj {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] (ψ : BranchialHilbert S) :
    BranchialHilbert S :=
  branchialAdjLM adj ψ

/-- `branchialAdj adj` is additive. -/
theorem branchialAdj_add {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj]
    (ψ φ : BranchialHilbert S) :
    branchialAdj adj (ψ + φ) = branchialAdj adj ψ + branchialAdj adj φ :=
  (branchialAdjLM adj).map_add ψ φ

/-- `branchialAdj adj` commutes with multiplication by a complex scalar. -/
theorem branchialAdj_smul {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] (c : ℂ) (ψ : BranchialHilbert S) :
    branchialAdj adj (c • ψ) = c • branchialAdj adj ψ :=
  (branchialAdjLM adj).map_smul c ψ

/-- For a symmetric relation `adj`, `⟨A ψ, φ⟩ = ⟨ψ, A φ⟩` with `A = branchialAdjLM adj`. -/
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

/-! ### Amplitudes and squared moduli -/

/-- A second name for `BranchialHilbert S`. -/
abbrev BranchialAmplitude (S : Type*) [Fintype S] : Type _ := BranchialHilbert S

/-- `bornProbability ψ s = |ψ s|²`. -/
noncomputable def bornProbability {S : Type*} [Fintype S]
    (ψ : BranchialAmplitude S) (s : S) : ℝ :=
  Complex.normSq (ψ s)

/-- `bornProbability ψ s ≥ 0`. -/
theorem bornProbability_nonneg {S : Type*} [Fintype S]
    (ψ : BranchialAmplitude S) (s : S) :
    0 ≤ bornProbability ψ s :=
  Complex.normSq_nonneg _

/-- `∑ s, bornProbability ψ s = ‖ψ‖²`. -/
theorem sum_bornProbability {S : Type*} [Fintype S]
    (ψ : BranchialAmplitude S) :
    ∑ s, bornProbability ψ s = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  unfold bornProbability
  rw [Real.sq_sqrt]
  · simp only [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _)]
  · exact Finset.sum_nonneg (fun s _ => sq_nonneg _)

/-- The constant weight `1 / |S|` on a finite type `S`. -/
noncomputable def branchialUniformWeight (S : Type*) [Fintype S]
    (_s : S) : ℝ :=
  (Fintype.card S : ℝ)⁻¹

/-- `branchialUniformWeight S s ≥ 0`. -/
theorem branchialUniformWeight_nonneg (S : Type*) [Fintype S] (s : S) :
    0 ≤ branchialUniformWeight S s := by
  unfold branchialUniformWeight
  positivity

/-- For nonempty `S`, the uniform weights sum to 1. -/
theorem sum_branchialUniformWeight (S : Type*) [Fintype S] [Nonempty S] :
    ∑ s : S, branchialUniformWeight S s = 1 := by
  unfold branchialUniformWeight
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  field_simp

/-! ### Expectation values -/

/-- The expectation value `⟨A⟩_ψ := ⟨ψ, A ψ⟩` of a ℂ-linear operator `A`. -/
noncomputable def expectationValue {S : Type*} [Fintype S]
    (A : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S)
    (ψ : BranchialHilbert S) : ℂ :=
  @inner ℂ _ _ ψ (A ψ)

/-- If `⟨A φ, ψ⟩ = ⟨φ, A ψ⟩` for all `φ, ψ`, then `⟨A⟩_ψ` equals its complex conjugate. -/
theorem expectationValue_re_of_symm {S : Type*} [Fintype S]
    (A : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S)
    (hsa : ∀ φ ψ : BranchialHilbert S, @inner ℂ _ _ (A φ) ψ = @inner ℂ _ _ φ (A ψ))
    (ψ : BranchialHilbert S) :
    starRingEnd ℂ (expectationValue A ψ) = expectationValue A ψ := by
  unfold expectationValue
  rw [inner_conj_symm]
  exact hsa ψ ψ

/-- If `A ψ = a • ψ` for `a : ℂ`, then `⟨A⟩_ψ = a · ⟨ψ, ψ⟩`. -/
theorem expectationValue_eigenvector {S : Type*} [Fintype S]
    (A : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S)
    (ψ : BranchialHilbert S) (a : ℂ)
    (heigen : A ψ = a • ψ) :
    expectationValue A ψ = a * (@inner ℂ _ _ ψ ψ) := by
  unfold expectationValue
  rw [heigen, inner_smul_right]

/-! ### Self-adjoint operators -/

/-- A ℂ-linear operator on `BranchialHilbert S` with `⟨A φ, ψ⟩ = ⟨φ, A ψ⟩` for all `φ, ψ`. -/
structure BranchialObservable (S : Type*) [Fintype S] where
  /-- The underlying ℂ-linear operator. -/
  op : BranchialHilbert S →ₗ[ℂ] BranchialHilbert S
  /-- Self-adjointness. -/
  isSymm : ∀ φ ψ : BranchialHilbert S,
    @inner ℂ _ _ (op φ) ψ = @inner ℂ _ _ φ (op ψ)

/-- The adjacency operator of a symmetric relation as a `BranchialObservable`. -/
noncomputable def branchialAdjObservable {S : Type*} [Fintype S] [DecidableEq S]
    (adj : S → S → Prop) [DecidableRel adj] (hsymm : ∀ a b, adj a b → adj b a) :
    BranchialObservable S where
  op := branchialAdjLM adj
  isSymm := branchialAdjLM_inner adj hsymm

/-- The expectation value of a `BranchialObservable` equals its complex conjugate. -/
theorem BranchialObservable.expectationValue_real {S : Type*} [Fintype S]
    (A : BranchialObservable S) (ψ : BranchialHilbert S) :
    starRingEnd ℂ (expectationValue A.op ψ) = expectationValue A.op ψ :=
  expectationValue_re_of_symm A.op A.isSymm ψ

/-! ### Branchial slices -/

/-- The `Fintype` instance on `BranchialSlice sys s₀ n` obtained from a finiteness proof. -/
@[reducible]
noncomputable def branchialSliceFintype {P V : Type*} [DecidableEq V]
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) :
    Fintype ↑(BranchialSlice sys s₀ n) :=
  h.fintype

/-- `BranchialHilbert` on the slice `BranchialSlice sys s₀ n`, given a proof that the slice
is finite. -/
noncomputable abbrev branchialSliceHilbert {P V : Type*} [DecidableEq V]
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) : Type _ :=
  @BranchialHilbert ↑(BranchialSlice sys s₀ n) (branchialSliceFintype sys s₀ n h)

end InfraFormalization
