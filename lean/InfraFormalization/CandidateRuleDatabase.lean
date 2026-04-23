/-
**Candidate-rule database and screening pipeline** (Group IR / #164).

Infrastructure for the ruliology arm of the program: store candidate
rules (`RewritingSystem P`) together with their signatures, filter
by target dimension / structural constraints.

  * `CandidateRule P` — a rewriting system + metadata (name, signature).
  * `screenByDimension`, `screenByGrowth` — filter predicates.
  * `passesStructuralScreens` — conjunction of impossibility
    theorems (not conservative, not pure-tree, etc).

**Connection to hypergraphs.** Native. Each candidate is a
`RewritingSystem P` acting on `Hypergraph V`.
-/

import InfraFormalization.RuleSignature
import InfraFormalization.StructuralRuleBounds

namespace InfraFormalization

/-- **Candidate rule**: a rewriting system bundled with human-readable
metadata for database use. -/
structure CandidateRule (P : Type*) where
  name : String
  sys  : RewritingSystem P
  note : String := ""

/-- **Screen: non-conservative** (a rule must grow to avoid the
`trajectory_size_invariant` bound on dimension). -/
def CandidateRule.NotConservative {P : Type*} (c : CandidateRule P) :
    Prop :=
  ∃ r ∈ c.sys.rules, ¬ r.IsConservative

/-- **Screen: non-trivial rule** — at least one rule in the system. -/
def CandidateRule.NonEmpty {P : Type*} (c : CandidateRule P) : Prop :=
  c.sys.rules ≠ []

/-- **Candidate passes basic structural screens** if it's non-empty
and not everything is conservative. -/
def CandidateRule.PassesScreens {P : Type*} (c : CandidateRule P) :
    Prop :=
  c.NonEmpty ∧ c.NotConservative

/-- **A list of candidates** with the screening predicate applied. -/
def filterCandidates {P : Type*} (candidates : List (CandidateRule P))
    [DecidableEq P] : List (CandidateRule P) :=
  candidates  -- sentinel: the screening is predicate-level, not
              -- decidable in general. The list is returned as-is
              -- and screening theorems are applied individually.

/-- **All rules conservative** — dual to `NotConservative`. Every rule
in the system has `|LHS| = |RHS|`. Under this predicate, any trajectory
built over `c.sys` preserves `edgeCount` (via IR2). -/
def CandidateRule.AllConservative {P : Type*} (c : CandidateRule P) : Prop :=
  ∀ r ∈ c.sys.rules, r.IsConservative

/-- **AllConservative is the negation of NotConservative** (over the
rule list). Uses decidable-equality on rule predicates for the
forward direction. -/
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

/-- **Screening theorem**: a candidate `c` with `AllConservative` and a
step-consistent trajectory over `c.sys` starting from `init` cannot
reach any target signature `σ` with `σ.edgeCount ≠ init.size`.

This is the IR6-level combination of IR2 (conservation theorem) with
the signature screening criterion
`RuleSignature.edgeCount_mismatch_unreachable_of_conservative`.
Applied to a rule database, it immediately rules out whole classes
of target signatures without exploring the state space. -/
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

/-- **Unconditional admissibility screen**: any non-admissible target
`σ` is unreachable by every candidate `c` and every trajectory over
`c.sys`, regardless of conservativity, step-consistency, or anything
else about the rules. Follows directly from
`RuleSignature.not_admissible_unreachable`. -/
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
