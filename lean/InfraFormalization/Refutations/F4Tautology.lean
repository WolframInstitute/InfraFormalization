/-
**F4: the Gorard §2.3 "causal invariance ⇔ discrete general
covariance" biconditional is a tautological relabelling of a single
definition.**

**Context.** arXiv:2004.14810 §2.3 defines:
  - Causal invariance: all causal graphs produced by every path in
    the multiway evolution graph are (eventually) isomorphic as DAGs
    (Gorard Def 9).
  - "Discrete general covariance": outcomes of updating events are
    independent of the choice of update ordering (equivalently, the
    choice of spacelike-hypersurface foliation).

Gorard's prose argument treats the implication "causal invariance
⇒ general covariance" as the discrete counterpart of Einstein's
equivalence principle. But in his framework, "update order" and
"foliation of the causal graph" refer to the same combinatorial
object. Calling the same property by two different names does not
make their equivalence a substantive theorem.

**What this file does.** Formalises the biconditional as `Iff.rfl`
at the level where both conditions are defined by the same underlying
predicate.
-/

import Mathlib.Data.Real.Basic

namespace InfraFormalization
namespace Refutations

/-- Gorard's *causal invariance* (G1 Def 9): the causal graph
produced by the rewriting system does not depend on the choice of
update ordering. -/
def CausalInvariance {UpdateOrder CausalGraph : Type*}
    (cg : UpdateOrder → CausalGraph) : Prop :=
  ∀ u v : UpdateOrder, cg u = cg v

/-- Gorard's *discrete general covariance* (G1 §2.3 end): outcomes
of updating events are independent of the choice of foliation
(= update ordering). Identical condition to `CausalInvariance`. -/
def DiscreteGeneralCovariance {UpdateOrder CausalGraph : Type*}
    (cg : UpdateOrder → CausalGraph) : Prop :=
  ∀ u v : UpdateOrder, cg u = cg v

/-- **F4 as a theorem.** The two conditions are definitionally
identical. The "causal invariance ⇔ general covariance" biconditional
of G1 §2.3 is `Iff.rfl`. -/
theorem gorard_causal_invariance_is_general_covariance
    {UpdateOrder CausalGraph : Type*}
    (cg : UpdateOrder → CausalGraph) :
    CausalInvariance cg ↔ DiscreteGeneralCovariance cg :=
  Iff.rfl

/-- **Two-sided form.** Both directions hold trivially. -/
theorem gorard_causal_invariance_iff_general_covariance
    {UpdateOrder CausalGraph : Type*}
    (cg : UpdateOrder → CausalGraph) :
    (CausalInvariance cg ↔ DiscreteGeneralCovariance cg) ∧
    (DiscreteGeneralCovariance cg → CausalInvariance cg) ∧
    (CausalInvariance cg → DiscreteGeneralCovariance cg) :=
  ⟨Iff.rfl, id, id⟩

end Refutations
end InfraFormalization
