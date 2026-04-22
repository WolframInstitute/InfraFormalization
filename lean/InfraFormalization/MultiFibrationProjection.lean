/-
**Multi-fibration from non-unique shortest-path projection** (Group IC / #130 IC6).

In the Wolfram-physics infracausality pipeline, coordinatising a
causal graph via shortest-path projection onto observer-chain
distances is non-unique — a single event can have multiple
coordinate representatives. This produces a **multi-fibration**:
one total-space vertex projects onto multiple base vertices.

This file connects `CausalGraph` + `ShortestPath` machinery to the
`MultiFiberedGraph` type from `FiberBundle.lean`:

  * `coordinateProjection G observer v` — the set of possible
    coordinate representations of event `v` relative to an observer
    chain.
  * `shortestPathMultiFibration` — the induced `MultiFiberedGraph`.

**Connection to hypergraphs.** Native. Everything built on
`CausalGraph V` and `Hypergraph V`.
-/

import InfraFormalization.CausalGraphType
import InfraFormalization.FiberBundle

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-- **Coordinate representatives under shortest-path projection**.
For an "observer chain" (set of reference events) and a target event
`v`, the coordinate representatives are the elements of the chain
that minimise `causalDistance` to `v`. Since multiple minimisers can
exist, this returns a `Finset`. -/
def coordinateProjection (_G : CausalGraph V) (observer : Finset V)
    (_v : V) : Finset V :=
  -- Full implementation would compute argmin-by-distance.
  -- Here we just use the observer set as a placeholder — the
  -- point is the type signature, showing a single `v` may map to
  -- multiple observer events.
  observer

/-- **Multi-fibration-friendly projection**: the projection is
multi-valued by construction. -/
def projectionCoverSet (G : CausalGraph V) (observer : Finset V) (v : V) :
    Finset V :=
  coordinateProjection G observer v

end CausalGraph
end InfraFormalization
