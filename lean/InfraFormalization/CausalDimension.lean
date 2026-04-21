/-
**Causal-graph dimension** (Group ID / #143 ID5, Group H / #76 H2).

For a causal graph (from `CausalGraphType.lean`), the dimension
can be read off from the growth rate of maximal antichains: a
causal graph that looks locally like a Minkowski lattice in
`(d+1)` dimensions has antichain size growing as `n^d` (level `n`
has `~ n^d` events).

This gives an independent dimension notion to be cross-checked
against Wolfram-Hausdorff (`ID1`) and spectral (`ID7`)
dimensions — the compatibility theorem (`ID6`) states they should
all agree for physical rules.

**Connection to hypergraphs.** Causal graphs arise from
`Trajectory`s (native). Every `Causal.lean` predicate carries
over; this file extracts the growth-of-antichain dimension.
-/

import InfraFormalization.CausalGraphType
import InfraFormalization.CausalFoliation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-! ## Antichain-size growth -/

/-- **Maximal-antichain size**: the largest antichain in `G`. Uses
classical decidability for the antichain predicate. -/
noncomputable def maxAntichainSize : Nat :=
  haveI : DecidablePred G.IsAntichain := fun _ => Classical.propDecidable _
  (Finset.univ.powerset.filter G.IsAntichain).image Finset.card |>.max.getD 0

/-- **Foliation-thickness**: the maximum size of any foliation slice. -/
noncomputable def foliationMaxThickness (f : Nat → Finset V) : Nat :=
  ((Finset.range (Fintype.card V + 1)).image (fun n => (f n).card)).max.getD 0

/-- **Causal-graph dimension**: logarithmic growth rate of maximal
antichain size as a function of the causal-graph level. Bounded by
`log(maxAntichainSize) / log(depth)` for finite causal graphs;
formally stated at the predicate level here. -/
noncomputable def causalDimensionAt (f : Nat → Finset V) (n : Nat) : ℝ :=
  if n ≤ 1 then 0
  else
    Real.log ((f n).card : ℝ) / Real.log (n : ℝ)

/-! ## Chain-based dual: proper-time growth -/

/-- **Longest chain between depth `n` and depth 0**: a measure of
"proper time" in discrete units. -/
def HasChainToDepth (v : V) (n : Nat) : Prop :=
  ∃ u : V, G.ChainOfLength n u v

end CausalGraph
end InfraFormalization
