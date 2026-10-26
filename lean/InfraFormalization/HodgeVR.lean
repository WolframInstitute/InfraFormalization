/-
Graph Laplacian of the Vietoris–Rips graph of a hypergraph.

This module defines `vrHodge0 ε`, the graph Laplacian of `vietorisRipsGraph ε`, which is built from `Hypergraph.dist`, and proves that it vanishes on constant functions. No 1-form Laplacian is defined here.
-/

import InfraFormalization.VietorisRips

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `vrHodge0 ε f v = ∑_{u adjacent to v in vietorisRipsGraph ε} (f u − f v)`. -/
noncomputable def vrHodge0 (H : Hypergraph V) (ε : ℕ) (f : V → ℝ)
    (v : V) : ℝ :=
  haveI : DecidablePred (fun u => (H.vietorisRipsGraph ε).Adj v u) :=
    fun _ => Classical.propDecidable _
  ∑ u ∈ (Finset.univ : Finset V).filter
      (fun u => (H.vietorisRipsGraph ε).Adj v u),
    (f u - f v)

/-- `vrHodge0 ε` vanishes on constant functions. -/
theorem vrHodge0_const (H : Hypergraph V) (ε : ℕ) (c : ℝ) (v : V) :
    H.vrHodge0 ε (fun _ => c) v = 0 := by
  unfold vrHodge0
  apply Finset.sum_eq_zero
  intros u _
  ring


end Hypergraph
end InfraFormalization
