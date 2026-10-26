/-
Tree, planarity and concatenation predicates on rewriting systems.

This module defines tree-like hypergraphs (connected clique expansion with
unique paths), the edge-count condition `E ≤ 3V − 6` as a necessary
condition for planarity, the predicates that every trajectory state
satisfies one of these, and systems whose rule list is the concatenation of
two nonempty rule lists. It proves that every rule of a concatenated system
lies in one of the two parts and that a concatenated system has only
conservative rules if and only if both parts do. No theorem in this module
bounds a dimension.
-/

import InfraFormalization.RuleDimensionBounds
import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {P V : Type*} [Fintype V] [DecidableEq V]

/-! ## Trees -/

/-- The clique expansion of `H` is connected and any two paths with the
same endpoints are equal. -/
def Hypergraph.IsTreelike (H : Hypergraph V) : Prop :=
  -- Connectedness and uniqueness of paths, stated directly.
  H.toSimpleGraph.Connected ∧
  ∀ (u v : V) (w₁ w₂ : (H.toSimpleGraph).Walk u v),
    w₁.IsPath → w₂.IsPath → w₁ = w₂

/-- Every state of every trajectory of `sys` is tree-like. -/
def RewritingSystem.ProducesTrees (sys : RewritingSystem P) : Prop :=
  ∀ (init : Hypergraph V) (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length),
    (τ.states.get ⟨i, hi⟩).IsTreelike

/-! ## Planarity -/

/-- `V` has fewer than 3 elements, or the clique expansion of `H` has at
most `3 · |V| − 6` edges. This is a necessary condition for planarity, not
planarity. -/
def Hypergraph.IsPlanarLike (H : Hypergraph V) : Prop :=
  -- Edge bound E ≤ 3V − 6 for |V| ≥ 3.
  Fintype.card V < 3 ∨
  (H.toSimpleGraph.edgeFinset.card ≤ 3 * Fintype.card V - 6)

/-- Every state of every trajectory of `sys` satisfies `IsPlanarLike`. -/
def RewritingSystem.ProducesPlanar (sys : RewritingSystem P) : Prop :=
  ∀ (init : Hypergraph V) (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length),
    (τ.states.get ⟨i, hi⟩).IsPlanarLike

/-! ## Concatenated systems -/

/-- The rule list of `sys` is the concatenation of the rule lists of `sys₁`
and `sys₂`, and both are nonempty. -/
def IsDirectConcatSystem (sys sys₁ sys₂ : RewritingSystem P) : Prop :=
  sys.rules = sys₁.rules ++ sys₂.rules ∧
  sys₁.rules ≠ [] ∧ sys₂.rules ≠ []

/-- Every rule of a concatenated system is a rule of `sys₁` or of
`sys₂`. -/
theorem IsDirectConcatSystem.rule_in_half
    {sys sys₁ sys₂ : RewritingSystem P}
    (hsys : IsDirectConcatSystem sys sys₁ sys₂) (r : Rule P)
    (hr : r ∈ sys.rules) : r ∈ sys₁.rules ∨ r ∈ sys₂.rules := by
  rw [hsys.1] at hr
  exact List.mem_append.mp hr

/-- All rules of a concatenated system are conservative if and only if all
rules of `sys₁` and all rules of `sys₂` are conservative. -/
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

end InfraFormalization
