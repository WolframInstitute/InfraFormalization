/-
Antichain sizes and a log-ratio on causal graphs.

This module defines the largest antichain size of a finite causal graph,
the largest slice size of a sequence of vertex sets, the ratio
`log |f n| / log n`, and the predicate that a chain of length `n` ends at a
vertex. It proves no theorems.
-/

import InfraFormalization.CausalGraphType
import InfraFormalization.CausalFoliation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-! ## Antichain-size growth -/

/-- The largest cardinality of an antichain of `G`, or 0 if there is none.
Decidability of the antichain predicate is classical. -/
noncomputable def maxAntichainSize : Nat :=
  haveI : DecidablePred G.IsAntichain := fun _ => Classical.propDecidable _
  (Finset.univ.powerset.filter G.IsAntichain).image Finset.card |>.max.getD 0

/-- The largest cardinality of `f n` for `n ≤ |V|`, or 0. -/
noncomputable def foliationMaxThickness (f : Nat → Finset V) : Nat :=
  ((Finset.range (Fintype.card V + 1)).image (fun n => (f n).card)).max.getD 0

/-! ## Chain-based dual: proper-time growth -/

/-- Some vertex `u` has a chain of length `n` from `u` to `v` in `G`. -/
def HasChainToDepth (v : V) (n : Nat) : Prop :=
  ∃ u : V, G.ChainOfLength n u v

end CausalGraph
end InfraFormalization
