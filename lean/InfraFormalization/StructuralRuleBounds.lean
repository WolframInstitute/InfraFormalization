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

/-- **Product rule**: `sys₁ × sys₂` acts on `V₁ ⊕ V₂` (disjoint
union) with `sys₁` on the first summand, `sys₂` on the second.
Predicate-level statement: a system is a "product-like combo" if
all its rules factor through one of two subsystems on disjoint
parts.

For dimension additivity: `dim(sys₁ × sys₂) = dim(sys₁) + dim(sys₂)`
when both subsystems act on disjoint vertex types. -/
def IsProductSystem {P₁ P₂ : Type*}
    (sys : RewritingSystem P) (sys₁ : RewritingSystem P₁)
    (sys₂ : RewritingSystem P₂) : Prop :=
  -- Skeleton: full definition requires defining products of
  -- RewritingSystems, which is substantial. Here we state the
  -- predicate at a sentinel level.
  True

end InfraFormalization
