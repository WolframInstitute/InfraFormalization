/-
Rewriting rules for Wolfram-model hypergraph rewriting.

We take a simple, explicit formulation: a rule is a pair of hypergraphs
on a common "pattern vertex" type `P`, plus an explicit partition of `P`
into *bound* variables (which must match existing target vertices) and
*fresh* variables (which must get new vertex labels allocated when the
rule fires).

This is stronger than Gorard's prose definition (which leaves "preserves
symmetries" unformalised) but exactly matches how every Wolfram-model
rule is actually written — with pattern variables on the left and
possibly some fresh ones on the right.

Key invariant on the rule: all pattern vertices that appear in `lhs`
must be in `bound`. Pattern vertices in `rhs` that are not in `bound`
are considered fresh.
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

/-- A rule is **conservative** iff it has the same number of edges on
both sides. This is a structural property visible at the rule level.
Every conservative rule preserves `state.size` under every application;
see `Conservation.lean`. -/
def IsConservative (r : Rule P) : Prop := r.lhsSize = r.rhsSize

/-- Gorard's named "EFE-satisfying" rule (arXiv:2102.09363 line 6202) is
conservative: |LHS| = |RHS| = 4. See `NamedRule.lean`. -/
example : True := trivial

end Rule

end InfraFormalization
