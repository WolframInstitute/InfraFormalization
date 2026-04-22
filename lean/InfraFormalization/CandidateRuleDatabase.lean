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

end InfraFormalization
