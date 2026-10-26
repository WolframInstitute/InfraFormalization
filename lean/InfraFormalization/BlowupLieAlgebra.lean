/-
Predicates on elementary blowups and Poisson brackets.

Elementary blowups are rules with a single-hyperedge left-hand side. This
module defines the predicate that the left-hand edge has one vertex, the type
`PoissonBracket V` of binary operations on functions `Hypergraph V → ℝ`, and
antisymmetry of such an operation. No Lie algebra or commutator is constructed.
-/

import InfraFormalization.ElementaryBlowup
import Mathlib.Data.Real.Basic

namespace InfraFormalization

variable {P : Type*}

/-- The single left-hand-side hyperedge of `B` has exactly one vertex. -/
def ElementaryBlowup.IsUnary (B : ElementaryBlowup P) : Prop :=
  (B.rule.lhs.edges.toList.head (by
    have : B.rule.lhs.edges.card = 1 := B.lhs_single
    intro h
    have : B.rule.lhs.edges.toList.length = 0 := by rw [h]; rfl
    rw [Multiset.length_toList] at this; omega)).verts.length = 1

/-! ## Binary operations on hypergraph functions -/

/-- The type of binary operations on functions `Hypergraph V → ℝ`. No
bilinearity, antisymmetry or Jacobi identity is imposed. -/
abbrev PoissonBracket (V : Type*) :=
  (Hypergraph V → ℝ) → (Hypergraph V → ℝ) → (Hypergraph V → ℝ)

/-- `br f g H = - br g f H` for all `f`, `g`, `H`. -/
def PoissonBracket.IsAntisymmetric {V : Type*}
    (br : PoissonBracket V) : Prop :=
  ∀ (f g : Hypergraph V → ℝ) (H : Hypergraph V),
    br f g H = - br g f H

end InfraFormalization
