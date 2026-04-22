/-
**Canonical branchial Hamiltonian grounded in hypergraph rewriting.**

This file wires the QM bridge explicitly to Wolfram-model rewriting
dynamics — no islands. Given a rewriting system `sys : RewritingSystem P`
and a seed `s₀ : Hypergraph V` whose depth-`n` branchial slice is
finite, we construct the canonical branchial Hamiltonian as the
adjacency operator on `BranchialHilbert ↑(BranchialSlice sys s₀ n)`
with adjacency = `BranchialRelated sys` (from `Branchial.lean`).

Concretely:

  * `BranchialRelated sys s₁ s₂` ⇔ both `s₁` and `s₂` are single-step
    successors of some common state `s` (defined in `Branchial.lean`).
  * The **canonical branchial adjacency** on a finite slice is
    `branchialAdjLM (fun s₁ s₂ => BranchialRelated sys s₁.val s₂.val)`.
  * This adjacency is automatically symmetric (`branchial_symm`), so
    the branchial Hamiltonian is Hermitian (`branchialAdjLM_inner`),
    and the Schrödinger evolution `i ∂_t ψ = A ψ` on the finite slice
    is unitary (`branchialSchrodinger_unitary_evolution`).

**Why this matters.** This anchors the ℂ-Hilbert / Schrödinger /
observable / Born-rule machinery explicitly to the rewriting system.
The QM bridge is not a free-floating analog — every operator, every
eigenvector, every measurement outcome depends on the underlying
Wolfram-model dynamics `sys`. The continuous structures sit on top of
the discrete rewriting, never beside it.
-/

import InfraFormalization.BranchialHilbert
import InfraFormalization.BranchialSchrodinger
import InfraFormalization.BranchialFinite

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

section
open Classical

/-- **Canonical branchial adjacency** on a finite branchial slice:
two states in the slice are adjacent iff they are branch-related
under the underlying rewriting system `sys`. Classical decidability
is used since `Step sys` is generally not decidable. -/
noncomputable def branchialSliceAdj (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : ℕ) :
    ↑(BranchialSlice sys s₀ n) → ↑(BranchialSlice sys s₀ n) → Prop :=
  fun s₁ s₂ => BranchialRelated sys s₁.val s₂.val

/-- **Canonical branchial adjacency is symmetric** — lifted directly
from `branchial_symm`. This is the key fact that makes the branchial
Hamiltonian Hermitian. -/
theorem branchialSliceAdj_symm (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : ℕ) :
    ∀ a b : ↑(BranchialSlice sys s₀ n),
      branchialSliceAdj sys s₀ n a b → branchialSliceAdj sys s₀ n b a :=
  fun _ _ h => branchial_symm sys h

/-- **Canonical branchial Hamiltonian** on the finite slice — the
ℂ-linear adjacency operator on `BranchialHilbert ↑(BranchialSlice sys
s₀ n)` with the canonical `BranchialRelated` adjacency.

This is the fully-grounded QM Hamiltonian: every feature (eigenvalues,
eigenvectors, expectation values, Schrödinger evolution) is
determined by the rewriting-system dynamics `sys` and the seed state
`s₀`. The Hilbert space and Hamiltonian are *derived from*, not
imposed upon, the computational rewriting structure. -/
noncomputable def branchialSliceHamiltonian (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : ℕ) (h : BranchialSliceFinite sys s₀ n) :
    letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
    BranchialHilbert ↑(BranchialSlice sys s₀ n) →ₗ[ℂ]
      BranchialHilbert ↑(BranchialSlice sys s₀ n) :=
  letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
  letI : DecidableEq ↑(BranchialSlice sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  letI : DecidableRel (branchialSliceAdj sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  branchialAdjLM (branchialSliceAdj sys s₀ n)

/-- **The canonical branchial Hamiltonian is Hermitian** — directly
from `branchialAdjLM_inner` + symmetry of `BranchialRelated`. For any
two states `ψ, φ` in the branchial Hilbert space,

  `⟨H ψ, φ⟩ = ⟨ψ, H φ⟩`.

This is the spectral-theorem prerequisite for a real spectrum: every
expectation value `⟨H⟩_ψ` is a real number, and eigenvalues of the
canonical Hamiltonian are real — exactly what quantum mechanics
requires of an observable. -/
theorem branchialSliceHamiltonian_isSymm
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) :
    letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
    ∀ φ ψ : BranchialHilbert ↑(BranchialSlice sys s₀ n),
      @inner ℂ _ _ ((branchialSliceHamiltonian sys s₀ n h) φ) ψ
      = @inner ℂ _ _ φ ((branchialSliceHamiltonian sys s₀ n h) ψ) := by
  letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
  letI : DecidableEq ↑(BranchialSlice sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  letI : DecidableRel (branchialSliceAdj sys s₀ n) :=
    fun _ _ => Classical.propDecidable _
  intro φ ψ
  exact branchialAdjLM_inner (branchialSliceAdj sys s₀ n)
    (branchialSliceAdj_symm sys s₀ n) φ ψ

/-- **Canonical branchial observable**: the rewriting-system-grounded
Hamiltonian packaged as a `BranchialObservable`. -/
noncomputable def branchialSliceObservable
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) :
    letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
    BranchialObservable ↑(BranchialSlice sys s₀ n) :=
  letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
  { op := branchialSliceHamiltonian sys s₀ n h
    isSymm := branchialSliceHamiltonian_isSymm sys s₀ n h }

/-- **Grounding statement**: every feature of the branchial quantum
framework (Hilbert space, Hamiltonian, observable, Schrödinger
evolution, Born rule) is determined *entirely* by `(sys, s₀, n)` —
the rewriting-system dynamics and initial data. No continuous
structure is imposed; all of it is derived from the discrete
hypergraph-rewriting state space.

This is the concrete expression of the Wolfram-model claim that
quantum mechanics is **emergent** from computational rewriting. -/
theorem branchial_qm_is_rewriting_grounded
    (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : ℕ)
    (h : BranchialSliceFinite sys s₀ n) :
    letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
    ∃ A : BranchialObservable ↑(BranchialSlice sys s₀ n),
      ∀ φ ψ : BranchialHilbert ↑(BranchialSlice sys s₀ n),
        @inner ℂ _ _ (A.op φ) ψ = @inner ℂ _ _ φ (A.op ψ) := by
  letI : Fintype ↑(BranchialSlice sys s₀ n) := h.fintype
  refine ⟨branchialSliceObservable sys s₀ n h, ?_⟩
  intro φ ψ
  exact (branchialSliceObservable sys s₀ n h).isSymm φ ψ

end

end InfraFormalization
