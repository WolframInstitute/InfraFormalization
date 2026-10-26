/-
Branchial relation and slices.

In G1 the branchial graph of a multiway system joins states that share
an immediate predecessor. This module defines that relation for the
abstract `Step` relation, proves it symmetric, defines exact `n`-step
reachability `NStep`, and defines the depth-`n` slice as the set of
states reachable in exactly `n` steps.
-/

import InfraFormalization.Multiway

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- Two states are branch-related when both are one-step successors of
some state `s`. -/
def BranchialRelated (sys : RewritingSystem P) (s₁ s₂ : Hypergraph V) : Prop :=
  ∃ s : Hypergraph V, Step sys s s₁ ∧ Step sys s s₂

/-- Branchial relatedness is symmetric. -/
theorem branchial_symm (sys : RewritingSystem P) :
    ∀ {s₁ s₂ : Hypergraph V},
      BranchialRelated sys s₁ s₂ → BranchialRelated sys s₂ s₁ := by
  rintro s₁ s₂ ⟨s, h₁, h₂⟩
  exact ⟨s, h₂, h₁⟩

/-- A state is branch-related to itself provided it has any
predecessor under the system. -/
theorem branchial_refl_of_has_predecessor (sys : RewritingSystem P)
    {s : Hypergraph V} (h : ∃ s₀, Step sys s₀ s) :
    BranchialRelated sys s s := by
  obtain ⟨s₀, hs₀⟩ := h
  exact ⟨s₀, hs₀, hs₀⟩

/-- `NStep sys n a b` holds when `b` is reachable from `a` in exactly `n`
steps of `Step sys`. -/
inductive NStep (sys : RewritingSystem P) :
    Nat → Hypergraph V → Hypergraph V → Prop
  | zero (s : Hypergraph V) : NStep sys 0 s s
  | succ {n : Nat} {a b c : Hypergraph V} :
      NStep sys n a b → Step sys b c → NStep sys (n + 1) a c

/-- Zero-step reachability is equality. -/
theorem nStep_zero_iff (sys : RewritingSystem P) (a b : Hypergraph V) :
    NStep sys 0 a b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact NStep.zero _

/-- One-step reachability is `Step`. -/
theorem nStep_one_iff (sys : RewritingSystem P) (a b : Hypergraph V) :
    NStep sys 1 a b ↔ Step sys a b := by
  constructor
  · intro h
    cases h with
    | succ h₀ hstep =>
      have : a = _ := (nStep_zero_iff sys _ _).mp h₀
      subst this
      exact hstep
  · intro h
    exact NStep.succ (NStep.zero _) h

/-- Any `NStep` implies `MultiStep` (reflexive-transitive closure). -/
theorem nStep_implies_multiStep (sys : RewritingSystem P)
    {n : Nat} {a b : Hypergraph V} (h : NStep sys n a b) :
    MultiStep sys a b := by
  induction h with
  | zero s => exact Relation.ReflTransGen.refl
  | succ _ hstep ih => exact Relation.ReflTransGen.tail ih hstep

/-- The depth-`n` slice: the set of states reachable from `s₀` in
exactly `n` steps. -/
def BranchialSlice (sys : RewritingSystem P) (s₀ : Hypergraph V) (n : Nat) :
    Set (Hypergraph V) :=
  { s | NStep sys n s₀ s }

/-- The depth-0 slice is the singleton `{s₀}`. -/
theorem branchialSlice_zero (sys : RewritingSystem P) (s₀ : Hypergraph V) :
    BranchialSlice sys s₀ 0 = {s₀} := by
  ext s
  simp only [BranchialSlice, Set.mem_setOf_eq, nStep_zero_iff, Set.mem_singleton_iff]
  exact eq_comm

/-- A state in the depth-`(n+1)` slice is a step-successor of some
state in the depth-`n` slice. -/
theorem branchialSlice_succ (sys : RewritingSystem P)
    (s₀ : Hypergraph V) (n : Nat) (s : Hypergraph V) :
    s ∈ BranchialSlice sys s₀ (n + 1) ↔
      ∃ s', s' ∈ BranchialSlice sys s₀ n ∧ Step sys s' s := by
  unfold BranchialSlice
  constructor
  · intro h
    cases h with
    | succ h₀ hstep =>
      exact ⟨_, h₀, hstep⟩
  · rintro ⟨s', h', hstep⟩
    exact NStep.succ h' hstep

end InfraFormalization
