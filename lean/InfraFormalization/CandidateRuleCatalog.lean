import InfraFormalization.Rule

/-!
Rules from the Wolfram-model literature, with their conservation status.

The module defines five rules as `Rule P` values over `Fin k`, each with a `LiteratureSource`
record, and proves for each whether `|LHS| = |RHS|`. The rules are the rule of G3 (line 6202),
which is conservative, the edge-doubling, edge-append and triple-expansion rules, which are not,
and the one-edge identity rule, which is. No theorem in this module concerns the causal graph or
the dimension of any rule.
-/

namespace InfraFormalization
namespace CandidateCatalog

/-- A citation record for a rule. -/
structure LiteratureSource where
  author : String
  year : Nat
  identifier : String  -- arXiv ID, paper title, WPP rule number, etc.
  note : String

/-- Six pattern vertices, used for the rule of G3 (`x, y, z, w, v` bound, `u` fresh). -/
abbrev P6 : Type := Fin 6

/-- Three pattern vertices, used for `{{x, y}} → {{x, y}, {y, z}}`. -/
abbrev P3 : Type := Fin 3

/-- Four pattern vertices, used for the triple-expansion rule. -/
abbrev P4 : Type := Fin 4

/-- Two pattern vertices, used for the edge-doubling and identity rules. -/
abbrev P2 : Type := Fin 2

/-- The two-vertex hyperedge `[a, b]`. -/
def edge {P : Type} (a b : P) : Hyperedge P :=
  ⟨[a, b], by simp⟩

/-- The hypergraph whose edge multiset is the list `es`. -/
def mkHypergraph {P : Type} (es : List (Hyperedge P)) : Hypergraph P :=
  ⟨(es : Multiset _)⟩

/-! ## Rules -/

/-- The rule `{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` of G3 (line 6202), with
fresh vertex `u`. The left-hand side is a path with four edges. Pattern vertices:
`x=0, y=1, z=2, w=3, v=4, u=5`. -/
def gorardNamedRule : Rule P6 :=
  { lhs := mkHypergraph [edge 0 1, edge 1 2, edge 2 3, edge 3 4],
    rhs := mkHypergraph [edge 1 5, edge 5 4, edge 3 0, edge 0 5] }

/-- Citation record for `gorardNamedRule` (G3). -/
def gorardNamedRule_source : LiteratureSource :=
  { author := "JGORARD"
    year := 2021
    identifier := "arXiv:2102.09363"
    note := "\"provably satisfies EFE in the continuum limit\" (abstract, line 51)" }

/-- `gorardNamedRule` is conservative: `|LHS| = |RHS| = 4`. -/
theorem gorardNamedRule_isConservative :
    Rule.IsConservative gorardNamedRule := by
  unfold Rule.IsConservative gorardNamedRule Rule.lhsSize Rule.rhsSize
  rfl

/-- `{{x,y}} → {{x,y},{x,y}}`. `|LHS| = 1`, `|RHS| = 2`. -/
def edgeDoublingRule : Rule P2 :=
  { lhs := mkHypergraph [edge 0 1]
    rhs := mkHypergraph [edge 0 1, edge 0 1] }

def edgeDoublingRule_source : LiteratureSource :=
  { author := "WPP enumeration"
    year := 2020
    identifier := "WPP/early"
    note := "edge duplication; non-conservative" }

theorem edgeDoublingRule_not_conservative :
    ¬ Rule.IsConservative edgeDoublingRule := by
  unfold Rule.IsConservative edgeDoublingRule Rule.lhsSize Rule.rhsSize
  decide

/-- `{{x,y}} → {{x,y},{y,z}}` with fresh vertex `z`. `|LHS| = 1`, `|RHS| = 2`. -/
def edgeAppendRule : Rule P3 :=
  { lhs := mkHypergraph [edge 0 1]
    rhs := mkHypergraph [edge 0 1, edge 1 2] }

def edgeAppendRule_source : LiteratureSource :=
  { author := "WPP enumeration"
    year := 2020
    identifier := "WPP/early"
    note := "linear extension; non-conservative; tree-like causal graph" }

theorem edgeAppendRule_not_conservative :
    ¬ Rule.IsConservative edgeAppendRule := by
  unfold Rule.IsConservative edgeAppendRule Rule.lhsSize Rule.rhsSize
  decide

/-- `{{x,y}} → {{x,y},{y,z},{z,w}}` with fresh vertices `z`, `w`. `|LHS| = 1`, `|RHS| = 3`. -/
def tripleExpansionRule : Rule P4 :=
  { lhs := mkHypergraph [edge 0 1]
    rhs := mkHypergraph [edge 0 1, edge 1 2, edge 2 3] }

def tripleExpansionRule_source : LiteratureSource :=
  { author := "WPP enumeration"
    year := 2020
    identifier := "WPP/early"
    note := "triple expansion; non-conservative; tree causal structure" }

theorem tripleExpansionRule_not_conservative :
    ¬ Rule.IsConservative tripleExpansionRule := by
  unfold Rule.IsConservative tripleExpansionRule Rule.lhsSize Rule.rhsSize
  decide

/-- `{{x,y}} → {{x,y}}`. `|LHS| = |RHS| = 1`. -/
def trivialIdentityRule : Rule P2 :=
  { lhs := mkHypergraph [edge 0 1]
    rhs := mkHypergraph [edge 0 1] }

def trivialIdentityRule_source : LiteratureSource :=
  { author := "control"
    year := 2026
    identifier := "n/a"
    note := "degenerate identity; conservative; causal graph is empty" }

theorem trivialIdentityRule_isConservative :
    Rule.IsConservative trivialIdentityRule := by
  unfold Rule.IsConservative trivialIdentityRule Rule.lhsSize Rule.rhsSize
  rfl

/-! ## Summary -/

/-- The number 5, the count of rules defined in this module. -/
def catalogSize : Nat := 5

/-- `gorardNamedRule` and `trivialIdentityRule` are conservative. -/
theorem catalog_conservative_rules :
    Rule.IsConservative gorardNamedRule
    ∧ Rule.IsConservative trivialIdentityRule :=
  ⟨gorardNamedRule_isConservative, trivialIdentityRule_isConservative⟩

/-- `edgeDoublingRule`, `edgeAppendRule` and `tripleExpansionRule` are not conservative. -/
theorem catalog_non_conservative_rules :
    ¬ Rule.IsConservative edgeDoublingRule
    ∧ ¬ Rule.IsConservative edgeAppendRule
    ∧ ¬ Rule.IsConservative tripleExpansionRule :=
  ⟨edgeDoublingRule_not_conservative,
   edgeAppendRule_not_conservative,
   tripleExpansionRule_not_conservative⟩

end CandidateCatalog
end InfraFormalization
