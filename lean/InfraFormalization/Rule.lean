/-
Rewriting rules for Wolfram-model hypergraph rewriting.

A rule is a pair of hypergraphs `lhs` and `rhs` on a pattern-vertex type
`P`. Pattern vertices that occur only in `rhs` are bound to new vertices
when the rule is applied; `Application.lean` records the binding and
`CausalHistory.RuleHistory` states the freshness condition.
-/

import InfraFormalization.Hypergraph

namespace InfraFormalization

open Hypergraph

/-- A rewriting rule with pattern-vertex type `P`. -/
structure Rule (P : Type*) where
  lhs : Hypergraph P
  rhs : Hypergraph P

namespace Rule

variable {P : Type*}

/-- The number of left-hand-side edges. -/
@[simp] def lhsSize (r : Rule P) : Nat := r.lhs.size

/-- The number of right-hand-side edges. -/
@[simp] def rhsSize (r : Rule P) : Nat := r.rhs.size

/-- A rule is conservative if its left-hand and right-hand sides have the
same number of edges. `Conservation.lean` proves that an application of a
conservative rule preserves the edge count. -/
def IsConservative (r : Rule P) : Prop := r.lhsSize = r.rhsSize

end Rule

end InfraFormalization
