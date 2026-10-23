/-
**F4: the JGORARD §2.3 "causal invariance ⇔ discrete general
covariance" biconditional is a tautological relabelling of a single
definition.**

**Context.** arXiv:2004.14810 §2.3 defines:
  - Causal invariance: all causal graphs produced by every path in
    the multiway evolution graph are (eventually) isomorphic as DAGs
    (JGORARD Def 9).
  - "Discrete general covariance": outcomes of updating events are
    independent of the choice of update ordering (equivalently, the
    choice of spacelike-hypersurface foliation).

JGORARD's prose argument treats the implication "causal invariance
⇒ general covariance" as the discrete counterpart of Einstein's
equivalence principle. But in his framework, "update order" and
"foliation of the causal graph" refer to the same combinatorial
object. Calling the same property by two different names does not
make their equivalence a substantive theorem.

**What this file proves.** The file defines `CausalInvariance` and
`DiscreteGeneralCovariance` with the same body and proves them
equivalent by `Iff.rfl`. The paper text identifies the two
(`papers/gorard_2004.14810.txt` lines 1066-1075: causal invariance
"is a discretized version of the principle of general covariance").
That identification is a reading of the paper and is not a Lean
theorem.
-/

import Mathlib.Data.Real.Basic

namespace InfraFormalization
namespace Refutations

/-- JGORARD's *causal invariance* (G1 Def 9): the causal graph
produced by the rewriting system does not depend on the choice of
update ordering. -/
def CausalInvariance {UpdateOrder CausalGraph : Type*}
    (cg : UpdateOrder → CausalGraph) : Prop :=
  ∀ u v : UpdateOrder, cg u = cg v

/-- JGORARD's *discrete general covariance* (G1 §2.3 end): outcomes
of updating events are independent of the choice of foliation
(= update ordering). Identical condition to `CausalInvariance`. -/
def DiscreteGeneralCovariance {UpdateOrder CausalGraph : Type*}
    (cg : UpdateOrder → CausalGraph) : Prop :=
  ∀ u v : UpdateOrder, cg u = cg v

/-- `CausalInvariance cg` and `DiscreteGeneralCovariance cg` are
equivalent, by `Iff.rfl`: both are defined as `∀ u v, cg u = cg v`. -/
theorem causalInvariance_iff_discreteGeneralCovariance
    {UpdateOrder CausalGraph : Type*}
    (cg : UpdateOrder → CausalGraph) :
    CausalInvariance cg ↔ DiscreteGeneralCovariance cg :=
  Iff.rfl

end Refutations
end InfraFormalization
