/-
Multiway systems.

Following G1 §2.2, an abstract rewriting system is a type with a binary relation. For a hypergraph
rewriting system, `Step sys s s'` holds if some rule `r` of the system has an application
`a : Application r s` with `a.result = s'`. This module defines `Step`, its reflexive-transitive
closure `MultiStep`, and confluence and local confluence of this relation.
-/

import InfraFormalization.Application
import Mathlib.Logic.Relation

namespace InfraFormalization

/-- A rewriting system: a list of rules with pattern-vertex type `P`. -/
structure RewritingSystem (P : Type*) where
  rules : List (Rule P)

variable {P V : Type*} [DecidableEq V]

/-- One-step rewriting relation induced by a system. -/
inductive Step (sys : RewritingSystem P) :
    Hypergraph V → Hypergraph V → Prop
  | apply (s : Hypergraph V) (r : Rule P) (_hr : r ∈ sys.rules)
      (a : Application r s) : Step sys s a.result

/-- Reflexive-transitive closure of `Step`. -/
def MultiStep (sys : RewritingSystem P) :
    Hypergraph V → Hypergraph V → Prop :=
  Relation.ReflTransGen (Step sys)

/-- Confluence (G1, Def 7): if `a` reaches `b` and `c` by `MultiStep`, then `b` and `c` reach a
common
`d`. -/
def Confluent (sys : RewritingSystem P) : Prop :=
  ∀ a b c : Hypergraph V,
    MultiStep sys a b → MultiStep sys a c →
    ∃ d, MultiStep sys b d ∧ MultiStep sys c d

/-- Local confluence (G1, Eq 9): if `a` reaches `b` and `c` in one `Step`, then `b` and `c` reach a
common `d` by `MultiStep`. -/
def LocallyConfluent (sys : RewritingSystem P) : Prop :=
  ∀ a b c : Hypergraph V,
    Step sys a b → Step sys a c →
    ∃ d, MultiStep sys b d ∧ MultiStep sys c d

end InfraFormalization
