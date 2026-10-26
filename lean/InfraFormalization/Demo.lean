/-
Edge conservation, re-exported.

This module restates `Application.size_result_of_conservative` and
`size_preserved_by_applications` under shorter names.
-/

import InfraFormalization.Conservation

namespace InfraFormalization

/-- Applying a conservative rule leaves the number of hyperedges unchanged. -/
theorem edge_conservation {P V : Type*} [DecidableEq V]
    {r : Rule P} {H : Hypergraph V}
    (a : Application r H) (hcons : r.IsConservative) :
    a.result.size = H.size :=
  Application.size_result_of_conservative a hcons

/-- Along a chain of applications of a conservative rule starting at `H₀`,
every state has the same number of hyperedges as `H₀`. -/
theorem trajectory_preserves_size {P V : Type*} [DecidableEq V]
    {r : Rule P} (hcons : r.IsConservative)
    (H₀ : Hypergraph V)
    (as : List (Σ H : Hypergraph V, Application r H))
    (hfirst : ∀ (h : as ≠ []), (as.head h).1 = H₀)
    (hchain : ∀ i (hi : i + 1 < as.length),
      (as.get ⟨i + 1, hi⟩).1 = (as.get ⟨i, Nat.lt_of_succ_lt hi⟩).2.result) :
    ∀ i (hi : i < as.length), (as.get ⟨i, hi⟩).1.size = H₀.size :=
  size_preserved_by_applications hcons H₀ as hfirst hchain

end InfraFormalization
