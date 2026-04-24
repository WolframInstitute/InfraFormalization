import InfraFormalization.CausalGraphType
import InfraFormalization.Branchial

/-!
**Multiway causal graph — combined causal + branchial structure** (J1 / #94).

The Wolfram-physics "multiway causal graph" combines two structures that
in single-way theories are taken separately:

* A *causal graph* of rule-application events, partially ordered by
  the direct-cause relation.
* A *branchial structure*: multiple parallel copies of the state
  tracked by rule-application branches that don't resolve to the same
  state.

This module packages the two into a single Lean structure. The causal
dimension lives on events (rule applications), the branchial dimension
lives on states at a given step. A "slice" is a branchial graph
(vertex set = states at step n, edges = pairs of states sharing a
common rule application); the causal graph threads through the slices
via the direct-cause partial order on events.

Concrete content:
* `MultiwayCausalGraph P V`: a record bundling a `RewritingSystem P`,
  an initial hypergraph `s₀ : Hypergraph V`, and a `CausalGraph` on
  rule-application events (indexed abstractly as `V`).
* `MultiwayCausalGraph.slice`: the branchial slice at step `n`.
* `MultiwayCausalGraph.causal`: projection to the underlying
  `CausalGraph`.
* `empty`: the trivial multiway-causal graph (empty rewriting, no
  events, empty causal graph).

This provides the combined carrier the Wolfram framework needs;
deeper structure (observer foliation across causal + branchial
dimensions, multiway-causal coherence) is follow-up work (J2+).
-/

namespace InfraFormalization

variable {P V : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]

/-- **Multiway causal graph**: the joint causal-plus-branchial
structure of a rewriting system running from an initial hypergraph.

* `sys` is the rewriting system (rules + signatures).
* `s₀` is the initial state hypergraph.
* `causal` is the direct-cause DAG on "events" — indexed abstractly
  by a carrier type `E` so the same structure can be used for multi-way
  enumerations (events = rule applications), single-way (events =
  update steps), or causal-set-style (events = pairs of incident
  hyperedges).

This matches the Wolfram-physics informal "multiway causal graph":
states live on slices indexed by step `n`; slices are connected by
rule applications (events); events carry the causal partial order. -/
structure MultiwayCausalGraph (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] where
  sys : RewritingSystem P
  s₀ : Hypergraph V
  causal : CausalGraph E

namespace MultiwayCausalGraph

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Branchial slice at step `n`** of a multiway-causal-graph: the
set of hypergraph states reached after `n` rule applications from `s₀`. -/
def slice (M : MultiwayCausalGraph P V E) (n : ℕ) : Set (Hypergraph V) :=
  BranchialSlice M.sys M.s₀ n

/-- **Empty multiway-causal graph** on any state carrier `V` and
event carrier `E`: no rules, no initial state edges, no events,
no causal relations. -/
def empty (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] :
    MultiwayCausalGraph P V E where
  sys := ⟨[]⟩
  s₀ := Hypergraph.empty
  causal :=
    { causalEdge := fun _ _ => False
      irrefl := fun _ h => h
      transitively_reduced := fun _ _ h => False.elim h }

/-- **The empty multiway-causal-graph has no causal edges.** -/
@[simp] theorem empty_causalEdge (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] (u v : E) :
    (empty P V E).causal.causalEdge u v = False := rfl

/-- **The empty multiway-causal-graph has the empty hypergraph as
initial state.** -/
@[simp] theorem empty_s₀ (P V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P] :
    (empty P V E).s₀ = (Hypergraph.empty : Hypergraph V) := rfl

end MultiwayCausalGraph

end InfraFormalization
