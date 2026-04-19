/-
Branchial structure — states sharing a common single-step predecessor.

Gorard (arXiv:2004.14810 and companion) posits a branchial graph at
each "slice" of the multiway evolution graph: vertices are hypergraph
states on the slice, edges connect states sharing an immediate
predecessor. This graph is the staging ground for the branchial-space
"quantum" picture (amplitudes, interference, branchial observables),
which is the eventual bridge to QM in the Wolfram program.

This file gives the bare, axiom-clean skeleton: the relation,
its symmetry, and an iterated-step reachability predicate. It is
deliberately lightweight — the interesting work happens downstream
when branchial slices are endowed with measures, when amplitudes are
assigned, and when convergence to quantum-mechanical Hilbert-space
structure is proved.
-/

import InfraFormalization.Multiway

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **Branchial relation.** Two hypergraph states are *branch-related*
(at the same multiway depth) if they share a common immediate
predecessor: both are single-step successors of some state `s`. -/
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

/-- **Iterated single-step reachability.** `NStep sys n a b` holds if
`b` is reachable from `a` in exactly `n` single-step firings. -/
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

/-- **Branchial slice at depth `n`.** The set of states reachable from
`s₀` in exactly `n` steps. This is the vertex set of the branchial
graph at depth `n`. -/
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

/-- **Placeholder type-level interface for branchial structure.** A
`BranchialStructure V` packages a slice-type and a slice-of-function;
downstream code wanting to abstract the branchial-graph picture can
depend on this interface without committing to a specific
construction. Kept for compatibility with earlier scaffolding. -/
structure BranchialStructure (V : Type*) where
  Slice : Type*
  sliceOf : Hypergraph V → Slice

end InfraFormalization
