/-
Elementary blowups.

An `ElementaryBlowup P` is a `Rule P` whose left-hand side has exactly one
hyperedge. The module defines its left-hand hyperedge, its applications to a
hypergraph, its right-hand edge count and the relation `Order B n` stating
that this count is `n`. It proves no theorems. No commutator, Lie bracket or
Poisson bracket is defined here.
-/

import InfraFormalization.Rule
import InfraFormalization.Application

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- A `Rule P` whose left-hand side has exactly one hyperedge. -/
structure ElementaryBlowup (P : Type*) where
  rule : Rule P
  lhs_single : rule.lhsSize = 1

/-- The single hyperedge of the left-hand side of `B`. -/
noncomputable def ElementaryBlowup.headEdge (B : ElementaryBlowup P) :
    Hyperedge P :=
  B.rule.lhs.edges.toList.head
    (by
      have : B.rule.lhs.edges.card = 1 := B.lhs_single
      intro h
      have hzero : B.rule.lhs.edges.toList.length = 0 := by
        rw [h]; rfl
      rw [Multiset.length_toList] at hzero
      omega)

/-- The type of applications of the rule of `B` to `H`. -/
def ElementaryBlowup.apply (B : ElementaryBlowup P) (H : Hypergraph V) :
    Type _ :=
  Application B.rule H

/-- The number of hyperedges on the right-hand side of the rule of `B`. -/
def ElementaryBlowup.rhsSize (B : ElementaryBlowup P) : Nat :=
  B.rule.rhsSize

/-- `Order B n` holds exactly when `B.rhsSize = n`. -/
inductive ElementaryBlowup.Order : ElementaryBlowup P → Nat → Prop
  | mk (B : ElementaryBlowup P) (n : Nat) (h : B.rhsSize = n) :
      ElementaryBlowup.Order B n

end InfraFormalization
