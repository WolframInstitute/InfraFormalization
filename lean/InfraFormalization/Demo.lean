/-
Demo: the main theorem of the project compiles.

This file just references the proved theorem `Application.size_result_of_conservative`
and uses it in a trivial proof, so that building this file asserts the
theorem is available and has the expected signature.
-/

import InfraFormalization.Conservation

namespace InfraFormalization

/-- Re-export the verified edge-conservation theorem for easy access. -/
theorem edge_conservation {P V : Type*} [DecidableEq V]
    {r : Rule P} {H : Hypergraph V}
    (a : Application r H) (hcons : r.IsConservative) :
    a.result.size = H.size :=
  Application.size_result_of_conservative a hcons

/-- Re-export the trajectory-level corollary. -/
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
