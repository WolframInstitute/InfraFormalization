/-
**Branchial-slice finiteness** (Group IQ / I1; task #84).

For a finite rewriting system acting on a finite initial hypergraph,
every branchial slice at depth `n` is a finite set of states. This
is the foundation for the QM bridge: a finite branchial slice
supports a `Finset`-indexed ℓ² Hilbert space, which is the
finite-dim precursor to the continuum QM Hilbert space.

**This file** provides the structural finiteness argument at the
`Set.Finite` level, conditional on the reasonable assumption that
each state has finitely many successors. The explicit `Fintype`
instance requires enumerating `Application r s` constructors and
is deferred to a follow-up (IG + BranchialFintypeInstance).
-/

import InfraFormalization.Branchial
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **Successors set** of a state `s` under a rewriting system. -/
def successors (sys : RewritingSystem P) (s : Hypergraph V) :
    Set (Hypergraph V) :=
  { s' | Step sys s s' }

/-- **Predicate: a branchial slice is finite.** -/
def BranchialSliceFinite (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (n : Nat) : Prop :=
  (BranchialSlice sys s₀ n).Finite

/-- **Finiteness at depth 0** — the slice is `{s₀}`. -/
theorem branchialSliceFinite_zero (sys : RewritingSystem P)
    (s₀ : Hypergraph V) :
    BranchialSliceFinite sys s₀ 0 := by
  unfold BranchialSliceFinite
  rw [branchialSlice_zero]
  exact Set.finite_singleton _

/-- **Inductive step**: if every state has finitely many successors
(a very mild assumption — always true for finite `V` and finite rule
sets), the branchial slice at depth `n + 1` is finite provided the
slice at depth `n` is. -/
theorem branchialSliceFinite_succ (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : Nat)
    (h_prev : BranchialSliceFinite sys s₀ n)
    (h_succ_finite : ∀ s : Hypergraph V, (successors sys s).Finite) :
    BranchialSliceFinite sys s₀ (n + 1) := by
  unfold BranchialSliceFinite at *
  let Sub : Type _ := {s : Hypergraph V // s ∈ BranchialSlice sys s₀ n}
  have hSub_fin : Finite Sub := h_prev.to_subtype
  let bigU : Set (Hypergraph V) := Set.iUnion (fun s : Sub => successors sys s.val)
  have hsub : BranchialSlice sys s₀ (n + 1) ⊆ bigU := by
    intro s' hs'
    rw [branchialSlice_succ] at hs'
    obtain ⟨s, hs_in, hstep⟩ := hs'
    exact Set.mem_iUnion.mpr ⟨⟨s, hs_in⟩, hstep⟩
  have hU_fin : bigU.Finite :=
    Set.finite_iUnion (fun s : Sub => h_succ_finite s.val)
  exact hU_fin.subset hsub

/-- **Main statement (conditional finiteness).** Under the
"finite-successors-everywhere" hypothesis, every branchial slice
is finite. -/
theorem branchialSliceFinite_of_successors_finite
    (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (h_succ : ∀ s : Hypergraph V, (successors sys s).Finite) (n : Nat) :
    BranchialSliceFinite sys s₀ n := by
  induction n with
  | zero => exact branchialSliceFinite_zero sys s₀
  | succ k ih => exact branchialSliceFinite_succ sys s₀ k ih h_succ

end InfraFormalization
