/-
F7: edge-count conservation for the rule of G3.

G3 (`papers/gorard_2102.09363.txt` lines 50-52, rule at line 6202) uses
the rule `{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` and states
that it "provably satisfies the Einstein field equations in the continuum
limit". This file proves that every application, and every chain of
applications, of this rule (`CandidateCatalog.gorardNamedRule`) leaves the
edge count unchanged. It proves no bound on causal-graph growth or on any
dimension.
-/

import InfraFormalization.Conservation
import InfraFormalization.CandidateRuleCatalog

namespace InfraFormalization
namespace Refutations

open CandidateCatalog

variable {V : Type*} [DecidableEq V]

/-- One application of `gorardNamedRule` to any hypergraph `H` gives a
hypergraph with the same edge count as `H`. -/
theorem gorardNamedRule_application_preserves_size
    (H : Hypergraph V) (a : Application gorardNamedRule H) :
    a.result.size = H.size :=
  Application.size_result_of_conservative a gorardNamedRule_isConservative

/-- In a chain of applications of `gorardNamedRule` that starts at `H₀`,
where each application acts on the result of the previous one, every
hypergraph in the chain has the edge count of `H₀`. -/
theorem gorardNamedRule_applications_preserve_size
    (H₀ : Hypergraph V)
    (as : List (Σ H : Hypergraph V, Application gorardNamedRule H))
    (hfirst : ∀ (h : as ≠ []), (as.head h).1 = H₀)
    (hchain : ∀ i (hi : i + 1 < as.length),
      (as.get ⟨i + 1, hi⟩).1 = (as.get ⟨i, Nat.lt_of_succ_lt hi⟩).2.result) :
    ∀ i (hi : i < as.length), (as.get ⟨i, hi⟩).1.size = H₀.size :=
  size_preserved_by_applications gorardNamedRule_isConservative H₀ as hfirst hchain

end Refutations
end InfraFormalization
