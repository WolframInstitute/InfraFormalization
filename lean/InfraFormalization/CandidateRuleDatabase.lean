/-
Candidate rewriting systems and two screens.

This module defines `CandidateRule P`, a rewriting system with a name and a
note, and the predicates `NotConservative`, `NonEmpty`, `PassesScreens` and
`AllConservative`. It proves that `AllConservative` is the negation of
`NotConservative`, that a trajectory of an all-conservative system never
reaches a signature with a different edge count, and that no trajectory
reaches a non-admissible signature.
-/

import InfraFormalization.RuleSignature
import InfraFormalization.StructuralRuleBounds

namespace InfraFormalization

/-- A rewriting system with a name and a note. -/
structure CandidateRule (P : Type*) where
  name : String
  sys  : RewritingSystem P
  note : String := ""

/-- Some rule of the system is not conservative. -/
def CandidateRule.NotConservative {P : Type*} (c : CandidateRule P) :
    Prop :=
  ∃ r ∈ c.sys.rules, ¬ r.IsConservative

/-- The system has at least one rule. -/
def CandidateRule.NonEmpty {P : Type*} (c : CandidateRule P) : Prop :=
  c.sys.rules ≠ []

/-- `NonEmpty` and `NotConservative` both hold. -/
def CandidateRule.PassesScreens {P : Type*} (c : CandidateRule P) :
    Prop :=
  c.NonEmpty ∧ c.NotConservative

/-- Every rule of the system is conservative (`|LHS| = |RHS|`). -/
def CandidateRule.AllConservative {P : Type*} (c : CandidateRule P) : Prop :=
  ∀ r ∈ c.sys.rules, r.IsConservative

/-- `AllConservative` holds if and only if `NotConservative` fails. -/
theorem CandidateRule.allConservative_iff_not_notConservative
    {P : Type*} (c : CandidateRule P) :
    c.AllConservative ↔ ¬ c.NotConservative := by
  unfold CandidateRule.AllConservative CandidateRule.NotConservative
  constructor
  · intro hall h_exists
    obtain ⟨r, hr_mem, hr_notcons⟩ := h_exists
    exact hr_notcons (hall r hr_mem)
  · intro hnot r hr_mem
    by_contra h_notcons
    exact hnot ⟨r, hr_mem, h_notcons⟩

/-- Let `c` satisfy `AllConservative`, and let `τ` be a step-consistent
trajectory from `init` whose applications use rules of `c.sys`. If the edge
count of `σ` differs from that of `init`, then no state of `τ` has the edge
count of `σ`. -/
theorem CandidateRule.allConservative_edgeCount_screen
    {P : Type*} (c : CandidateRule P) (hcons : c.AllConservative)
    {V : Type*} [Fintype V] [DecidableEq V] {init : Hypergraph V}
    (τ : Trajectory c.sys init) (hstep : τ.StepConsistent)
    (happ_in_rules : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1 ∈ c.sys.rules)
    (σ : RuleSignature V)
    (hmis : σ.edgeCount ≠ (hypergraphSignature init).edgeCount)
    (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount ≠ σ.edgeCount := by
  have hcons_all : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative :=
    fun i hi => hcons _ (happ_in_rules i hi)
  exact RuleSignature.edgeCount_mismatch_unreachable_of_conservative
    τ hstep hcons_all σ hmis i hi

/-- If `σ` is not admissible, no state of any trajectory `τ` has signature
`σ`. The candidate argument `_c` is not used, and `τ` is over an arbitrary
system `sys`. This is `RuleSignature.not_admissible_unreachable`. -/
theorem CandidateRule.notAdmissible_unreachable
    {P : Type*} (_c : CandidateRule P)
    {V : Type*} [Fintype V] [DecidableEq V] {init : Hypergraph V}
    {sys : RewritingSystem P}
    (τ : Trajectory sys init)
    (σ : RuleSignature V) (hnotadmis : ¬ σ.Admissible)
    (i : Nat) (hi : i < τ.states.length) :
    hypergraphSignature (τ.states.get ⟨i, hi⟩) ≠ σ :=
  RuleSignature.not_admissible_unreachable σ hnotadmis _

end InfraFormalization
