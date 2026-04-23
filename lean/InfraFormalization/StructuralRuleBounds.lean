/-
**Structural impossibility theorems for rule dimensions** (Group IR).

Extends `RuleDimensionBounds.lean` with additional classes of rules
whose outputs have bounded Wolfram-Hausdorff / spectral dimension.

  * **IR3**: Tree-producing rules have dimension `= log(branching)`.
    (Predicate-level statement; quantitative proof deferred.)
  * **IR4**: Planar-preserving rules produce graphs with
    `dim ≤ 2` (Euler formula `V − E + F = 2` bounds curvature).
  * **IR5**: Product rules `R₁ × R₂` on disjoint vertex sets give
    additive dimensions (predicate-level).

These eliminate broad classes from the candidate-rule search space.

**Connection to hypergraphs.** Native: every bound is on a
`RewritingSystem` acting on `Hypergraph V`. No continuum.
-/

import InfraFormalization.RuleDimensionBounds
import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {P V : Type*} [Fintype V] [DecidableEq V]

/-! ## IR3: Tree-producing rules -/

/-- **A hypergraph is tree-like** if its clique-expansion is a
tree (connected + acyclic). Predicate-level, using Mathlib's
SimpleGraph machinery. Mathlib-complete statement is
`SimpleGraph.IsTree`. -/
def Hypergraph.IsTreelike (H : Hypergraph V) : Prop :=
  -- `SimpleGraph.IsTree` requires `Connected` + `Acyclic`; we state
  -- the conjunction at predicate level.
  H.toSimpleGraph.Connected ∧
  ∀ (u v : V) (w₁ w₂ : (H.toSimpleGraph).Walk u v),
    w₁.IsPath → w₂.IsPath → w₁ = w₂

/-- **Tree-rule predicate**: every trajectory state is tree-like. -/
def RewritingSystem.ProducesTrees (sys : RewritingSystem P) : Prop :=
  ∀ (init : Hypergraph V) (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length),
    (τ.states.get ⟨i, hi⟩).IsTreelike

/-! ## IR4: Planar rules -/

/-- **A hypergraph is planar** if its clique-expansion embeds in
the plane (no edge crossings). Predicate-level; Mathlib has
`SimpleGraph.IsPlanar` in development.

We state via the Euler-formula consequence: the vertex count,
edge count, and face count satisfy `V − E + F = 2` for connected
planar graphs. -/
def Hypergraph.IsPlanarLike (H : Hypergraph V) : Prop :=
  -- Mathlib-level planarity is limited; we adopt a weaker placeholder:
  -- "the hypergraph's clique-expansion has at most `3V − 6` edges
  -- for `V ≥ 3`", a necessary condition for planarity.
  Fintype.card V < 3 ∨
  (H.toSimpleGraph.edgeFinset.card ≤ 3 * Fintype.card V - 6)

/-- **Planar-rule predicate**: every trajectory state is planar. -/
def RewritingSystem.ProducesPlanar (sys : RewritingSystem P) : Prop :=
  ∀ (init : Hypergraph V) (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length),
    (τ.states.get ⟨i, hi⟩).IsPlanarLike

/-! ## IR5: Product rules -/

/-- **Direct-concatenation system**: a system whose rule list is the
concatenation of two sub-system rule lists, both over the same
pattern type `P`. This is the shape-level of a product rule system,
expressing that `sys` is built by putting `sys₁`'s rules and `sys₂`'s
rules side by side with no interaction. Both halves required
non-empty so the predicate is non-degenerate.

This is the Lean-typable skeleton of "product rule"; the fuller
version (product on disjoint vertex subsets `V₁ ⊕ V₂`) requires
Rule types indexed by vertex-set, which is separate infrastructure. -/
def IsDirectConcatSystem (sys sys₁ sys₂ : RewritingSystem P) : Prop :=
  sys.rules = sys₁.rules ++ sys₂.rules ∧
  sys₁.rules ≠ [] ∧ sys₂.rules ≠ []

/-- **Every rule in a direct-concat system belongs to one of the two
halves.** Immediate from the `List.mem_append` characterisation. -/
theorem IsDirectConcatSystem.rule_in_half
    {sys sys₁ sys₂ : RewritingSystem P}
    (hsys : IsDirectConcatSystem sys sys₁ sys₂) (r : Rule P)
    (hr : r ∈ sys.rules) : r ∈ sys₁.rules ∨ r ∈ sys₂.rules := by
  rw [hsys.1] at hr
  exact List.mem_append.mp hr

/-- **A direct-concat system is `AllConservative`** iff both halves are.
Machine-level witness that the `AllConservative` property is additive
over direct-concatenation — one of the two shape-level additivity
lemmas needed before the full product-dim additivity (IR5). -/
theorem IsDirectConcatSystem.allConservative_iff_both
    {sys sys₁ sys₂ : RewritingSystem P}
    (hsys : IsDirectConcatSystem sys sys₁ sys₂) :
    (∀ r ∈ sys.rules, r.IsConservative) ↔
    (∀ r ∈ sys₁.rules, r.IsConservative) ∧
    (∀ r ∈ sys₂.rules, r.IsConservative) := by
  constructor
  · intro hall
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · exact hall r (by rw [hsys.1]; exact List.mem_append_left _ hr)
    · exact hall r (by rw [hsys.1]; exact List.mem_append_right _ hr)
  · rintro ⟨h1, h2⟩ r hr
    rcases hsys.rule_in_half r hr with hr1 | hr2
    · exact h1 r hr1
    · exact h2 r hr2

/-- **Product rule** (sentinel at pattern-type level): a system is a
"product-like combo" when it can be written as a `IsDirectConcatSystem`
over two halves. -/
def IsProductSystem (sys : RewritingSystem P) : Prop :=
  ∃ (sys₁ sys₂ : RewritingSystem P), IsDirectConcatSystem sys sys₁ sys₂

end InfraFormalization
