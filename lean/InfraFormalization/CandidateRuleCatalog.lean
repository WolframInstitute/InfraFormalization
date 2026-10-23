import InfraFormalization.Rule
import InfraFormalization.RuleWitnesses

/-!
**Candidate rule catalog from the literature** (H1 / #74).

Concrete rewriting rules that have been proposed in the Wolfram-physics
literature as candidates for having GR-like continuum limits. Each rule
is given here as an explicit `Rule P` (with a concrete pattern-vertex
type `P`), a `LiteratureSource` citation, and its conservation status.

**Purpose**. This catalog is the input stream for the IR6 screening
pipeline (`CandidateRuleDatabase.lean`) — every candidate below has its
conservation status classified here so that the edge-count
conservation theorems of `Conservation.lean` apply to it. Closing H1 gives H2/H3 a concrete list of rules to
run signature screens against.

**Disclaimer**. Inclusion here is *not* an endorsement of the rule's
dimensional claims. No theorem in this file or its importers bounds
the dimension of any catalogued rule's causal graph.

**Sources catalogued**.
  * `gorardNamedRule`: arXiv:2102.09363 line 6202. JGORARD's "provably
    EFE-satisfying" rule. |LHS|=|RHS|=4, so the rule is conservative
    (`gorardNamedRule_isConservative`). Measured cone-growth exponents
    are in `results/phase1_selfaudit/README.md`. A proof of any bound
    on its causal-graph growth is OPEN (`STATUS_OF_GORARD_CLAIMS.md`).
  * `edgeDoublingRule`: trivial WPP "rule 0" — doubles each edge. Non-
    conservative; produces exponential edge growth.
  * `edgeAppendRule`: `{{x,y}} → {{x,y},{y,z}}` — simple linear-
    extension rule from early WPP enumerations; non-conservative.
  * `tripleExpansionRule`: `{{x,y}} → {{x,y},{y,z},{z,w}}` — triple
    expansion; non-conservative, produces tree-like causal structure.
  * `trivialIdentityRule`: `{{x,y}} → {{x,y}}` — the degenerate
    identity (conservative); useful as a control in IR6 screens.

**Not catalogued here (out of scope for this tier)**:
  * Full Wolfram Physics Project enumeration (thousands of rules;
    infeasible as Lean `def` list without external data).
  * Causal-set-adjacent rules (they're by construction defined by a
    causal order on an unstructured set, not by a hypergraph-rewriting
    LHS→RHS; no Rule P representation).
  * Random-geometric-graph rules (stochastic; need measure-theoretic
    representation outside Rule P).
  * CDT-style (triangulation-based; uses simplicial 2-3 and 4-6 moves,
    requires a different carrier type).
-/

namespace InfraFormalization
namespace CandidateCatalog

/-- Literature source annotation (purely documentary). -/
structure LiteratureSource where
  author : String
  year : Nat
  identifier : String  -- arXiv ID, paper title, WPP rule number, etc.
  note : String

/-- **Pattern-vertex type with 6 slots**: enough for JGORARD's named rule
`{x, y, z, w, v, u}` (5 bound + 1 fresh). -/
abbrev P6 : Type := Fin 6

/-- **Pattern-vertex type with 3 slots**: enough for simple rules
like `{{x, y}} → {{x, y}, {y, z}}`. -/
abbrev P3 : Type := Fin 3

/-- **Pattern-vertex type with 4 slots**: triple-expansion rule. -/
abbrev P4 : Type := Fin 4

/-- **Pattern-vertex type with 2 slots**: edge-doubling. -/
abbrev P2 : Type := Fin 2

/-- Helper: build a 2-ary hyperedge from two pattern vertices. -/
def edge {P : Type} (a b : P) : Hyperedge P :=
  ⟨[a, b], by simp⟩

/-- Helper: build a hypergraph from a list of 2-ary hyperedges. -/
def mkHypergraph {P : Type} (es : List (Hyperedge P)) : Hypergraph P :=
  ⟨(es : Multiset _)⟩

/-! ## Catalogued rules -/

/-- **JGORARD's named rule** (arXiv:2102.09363 line 6202):
`{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}`.
The LHS is a path of length 4; the RHS rewires into a different
path of length 4 with one fresh vertex `u`.

Pattern-vertex encoding (`Fin 6`): `x=0, y=1, z=2, w=3, v=4, u=5`.

**Conservation status**: conservative (|LHS| = |RHS| = 4). -/
def gorardNamedRule : Rule P6 :=
  { lhs := mkHypergraph [edge 0 1, edge 1 2, edge 2 3, edge 3 4],
    rhs := mkHypergraph [edge 1 5, edge 5 4, edge 3 0, edge 0 5] }

/-- Source citation for JGORARD's named rule. -/
def gorardNamedRule_source : LiteratureSource :=
  { author := "JGORARD"
    year := 2021
    identifier := "arXiv:2102.09363"
    note := "\"provably satisfies EFE in the continuum limit\" (abstract, line 51)" }

/-- **JGORARD's rule is conservative**: |LHS| = |RHS| = 4. -/
theorem gorardNamedRule_isConservative :
    Rule.IsConservative gorardNamedRule := by
  unfold Rule.IsConservative gorardNamedRule Rule.lhsSize Rule.rhsSize
  rfl

/-- **Edge-doubling rule**: `{{x,y}} → {{x,y},{x,y}}`. Trivial WPP
"rule 0"; produces a duplicated copy of every edge each step.

**Conservation status**: non-conservative (|LHS|=1, |RHS|=2). -/
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

/-- **Edge-append rule**: `{{x,y}} → {{x,y},{y,z}}`. Simple linear
path-extension rule from early Wolfram-model enumerations.

**Conservation status**: non-conservative (|LHS|=1, |RHS|=2). -/
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

/-- **Triple-expansion rule**: `{{x,y}} → {{x,y},{y,z},{z,w}}`. Produces
a chain extension of length 3 per application.

**Conservation status**: non-conservative (|LHS|=1, |RHS|=3). -/
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

/-- **Trivial identity rule**: `{{x,y}} → {{x,y}}`. Useful as a
control in screening experiments.

**Conservation status**: trivially conservative (|LHS| = |RHS| = 1). -/
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

/-! ## Catalog summary -/

/-- **Catalogued rules count** (sanity check). We catalogue 5 concrete
rules spanning the conservative / non-conservative spectrum. -/
def catalogSize : Nat := 5

/-- **Conservative catalogued rules**: `gorardNamedRule`,
`trivialIdentityRule`. Both have |LHS| = |RHS|. -/
theorem catalog_conservative_rules :
    Rule.IsConservative gorardNamedRule
    ∧ Rule.IsConservative trivialIdentityRule :=
  ⟨gorardNamedRule_isConservative, trivialIdentityRule_isConservative⟩

/-- **Non-conservative catalogued rules**: `edgeDoublingRule`,
`edgeAppendRule`, `tripleExpansionRule`. These can potentially
produce higher-dimensional causal graphs; whether any actually achieves
a 4D continuum limit is IR2 / H2 / H3 empirical work. -/
theorem catalog_non_conservative_rules :
    ¬ Rule.IsConservative edgeDoublingRule
    ∧ ¬ Rule.IsConservative edgeAppendRule
    ∧ ¬ Rule.IsConservative tripleExpansionRule :=
  ⟨edgeDoublingRule_not_conservative,
   edgeAppendRule_not_conservative,
   tripleExpansionRule_not_conservative⟩

end CandidateCatalog
end InfraFormalization
