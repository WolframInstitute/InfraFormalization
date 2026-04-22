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

end InfraFormalization
