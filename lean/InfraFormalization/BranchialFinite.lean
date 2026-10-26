/-
Finiteness of branchial slices.

This module proves that if every state has finitely many one-step
successors, then every branchial slice `BranchialSlice sys s₀ n` is a finite
set.
-/

import InfraFormalization.Branchial
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- The set of states reachable from `s` in one step. -/
def successors (sys : RewritingSystem P) (s : Hypergraph V) :
    Set (Hypergraph V) :=
  { s' | Step sys s s' }

/-- The branchial slice at depth `n` is a finite set. -/
def BranchialSliceFinite (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (n : Nat) : Prop :=
  (BranchialSlice sys s₀ n).Finite

/-- The slice at depth 0 is finite. -/
theorem branchialSliceFinite_zero (sys : RewritingSystem P)
    (s₀ : Hypergraph V) :
    BranchialSliceFinite sys s₀ 0 := by
  unfold BranchialSliceFinite
  rw [branchialSlice_zero]
  exact Set.finite_singleton _

/-- If every state has finitely many successors and the slice at depth `n`
is finite, then the slice at depth `n + 1` is finite. -/
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

/-- If every state has finitely many successors, every branchial slice is
finite. -/
theorem branchialSliceFinite_of_successors_finite
    (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (h_succ : ∀ s : Hypergraph V, (successors sys s).Finite) (n : Nat) :
    BranchialSliceFinite sys s₀ n := by
  induction n with
  | zero => exact branchialSliceFinite_zero sys s₀
  | succ k ih => exact branchialSliceFinite_succ sys s₀ k ih h_succ

end InfraFormalization
