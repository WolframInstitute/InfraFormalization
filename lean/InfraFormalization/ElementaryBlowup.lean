/-
**Elementary blowups** (Group IB / #146).

An *elementary blowup* is a rewriting rule whose LHS consists of a
single hyperedge. Pavel Hájek's Srní talk (2026) identifies this
class as the minimal-model Lie-algebra generator:

  * Commutator `[B₁, B₂]` on isomorphism classes of hypergraphs
    has vanishing causal-branchial component.
  * Elementary blowups thus form a **Lie algebra**.
  * For unary edges, this specialises to the **insertion Lie
    algebra** of perturbative QFT.
  * Induces a **Poisson bracket** on formal hypergraph functions
    (Hamiltonian mechanics on the ruliad).

This file gives the definitions + basic properties; the
commutator-vanishing theorem, Lie-algebra structure, insertion
algebra, and Poisson bracket are IB2–IB5.

**Connection to hypergraphs.** Native. An elementary blowup is a
specific kind of `Rule P` applied to a `Hypergraph V` via
`Application`. No continuum objects.
-/

import InfraFormalization.Rule
import InfraFormalization.Application

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- **An elementary blowup** is a `Rule P` whose LHS has exactly one
hyperedge. -/
structure ElementaryBlowup (P : Type*) where
  rule : Rule P
  lhs_single : rule.lhsSize = 1

/-- **Extract the single hyperedge of an elementary-blowup LHS.** -/
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

/-- **An elementary blowup is in particular a rule**, so can be
applied wherever rules can be applied. -/
def ElementaryBlowup.apply (B : ElementaryBlowup P) (H : Hypergraph V) :
    Type _ :=
  Application B.rule H

/-- **The RHS hyperedge count of a blowup.** Free parameter. -/
def ElementaryBlowup.rhsSize (B : ElementaryBlowup P) : Nat :=
  B.rule.rhsSize

/-- **Classification**: the RHS size determines the "order" of the
blowup (number of outgoing edges produced by a single incoming edge). -/
inductive ElementaryBlowup.Order : ElementaryBlowup P → Nat → Prop
  | mk (B : ElementaryBlowup P) (n : Nat) (h : B.rhsSize = n) :
      ElementaryBlowup.Order B n

end InfraFormalization
