import InfraFormalization.CausalGraphType
import InfraFormalization.Branchial

/-!
Multiway causal graphs.

The multiway causal graph of a Wolfram model combines the causal relation on rule-application events
with the branchial structure on states reached at each step. This module defines the structure
`MultiwayCausalGraph P V E` of a rewriting system, an initial hypergraph and a causal graph on an
event type `E`, the slice at step `n` (the states reached from `s₀` after `n` applications), and the
empty instance. The structure imposes no relation between the causal graph and the rewriting system.
-/

namespace InfraFormalization

variable {P V : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]

/-- A rewriting system `sys`, an initial hypergraph `s₀`, and a causal graph `causal` on an event
type
`E`. No field relates `causal` to `sys` or `s₀`. -/
structure MultiwayCausalGraph (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] where
  sys : RewritingSystem P
  s₀ : Hypergraph V
  causal : CausalGraph E

namespace MultiwayCausalGraph

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The set of hypergraphs reached from `s₀` after `n` rule applications (`BranchialSlice`). -/
def slice (M : MultiwayCausalGraph P V E) (n : ℕ) : Set (Hypergraph V) :=
  BranchialSlice M.sys M.s₀ n

/-- The instance with no rules, the empty initial hypergraph and no causal edges. -/
def empty (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] :
    MultiwayCausalGraph P V E where
  sys := ⟨[]⟩
  s₀ := Hypergraph.empty
  causal :=
    { causalEdge := fun _ _ => False
      irrefl := fun _ h => h
      transitively_reduced := fun _ _ h => False.elim h }

/-- `empty` has no causal edges. -/
@[simp] theorem empty_causalEdge (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] (u v : E) :
    (empty P V E).causal.causalEdge u v = False := rfl

/-- The initial hypergraph of `empty` is the empty hypergraph. -/
@[simp] theorem empty_s₀ (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] :
    (empty P V E).s₀ = (Hypergraph.empty : Hypergraph V) := rfl

end MultiwayCausalGraph

end InfraFormalization
