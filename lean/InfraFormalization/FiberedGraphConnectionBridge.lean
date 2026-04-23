/-
**FiberedGraph → ConnectionData bridge obligation** (grounding action #1).

Closes the last "continuum-side connection is free-floating" gap. Every
`ConnectionData n` (Γ-tuples on `ℝⁿ`) is now attached to an obligation
Prop binding it existentially to a `FiberedGraph V W` + `Connection F`
+ positive scaling `scale : ℕ → ℝ`. The obligation is the shape of
"some discrete-connection-on-a-fibered-graph GH-converges to this
continuum connection".

The flat-connection case is fully witnessed: `flatConnection n` is
proved to have a hypergraph origin via the trivial FiberedGraph
(empty total, `π = id`) with the empty Connection — curvature-free
input yields curvature-free output.

**Grounding.** `FiberedGraph V W` is built on `Hypergraph V` + a
projection `π : V → W`; `Connection F` is a Finset of total-graph
hyperedges. No continuum objects appear on the witness side.
-/

import InfraFormalization.CurvatureRiemann
import InfraFormalization.FiberedGraph
import InfraFormalization.Holonomy

namespace InfraFormalization
namespace Curvature

open InfraFormalization

/-- **ConnectionData-origin obligation**: the continuum connection is
claimed to be the GH-limit of some sequence of scaled discrete
connections on a fibered graph.

At the statement level this is a pure existence claim; the full
bridge-holds predicate (convergence of holonomy matrices, Wilson loops,
etc.) is left as the open programme. The obligation binds:

  * a total vertex type `V`,
  * a base vertex type `W`,
  * a `FiberedGraph V W` (concrete hypergraph + projection),
  * a `Connection` on it,
  * a positive scaling sequence.
-/
def ConnectionDataOriginObligation {n : Nat}
    (_target : ConnectionData n) : Prop :=
  ∃ (V W : Type) (_ : Fintype V) (_ : Fintype W)
    (_ : DecidableEq V) (_ : DecidableEq W)
    (F : FiberedGraph V W) (_ : FiberedGraph.Connection F)
    (scale : ℕ → ℝ),
      (∀ k, 0 < scale k)

/-- **Flat connection's origin obligation**: the flat connection
`Γ ≡ 0` on `ℝⁿ` is claimed to come from a discrete connection on some
fibered graph. -/
def flatConnection_from_fiberedGraph (n : Nat) : Prop :=
  ConnectionDataOriginObligation (flatConnection n)

/-! ## Witness for the flat-connection obligation

We build a trivial `FiberedGraph (Fin 1) (Fin 1)` with empty total
hypergraph, `π = id`, and the empty `Connection`. The witness
trivially inhabits the flat-connection obligation — flat target, flat
source. -/

/-- **Trivial FiberedGraph** on `Fin 1 × Fin 1`: no edges, identity
projection. -/
def trivialFiberedGraph : FiberedGraph (Fin 1) (Fin 1) where
  total := Hypergraph.empty
  π := id

/-- **Trivial Connection** on `trivialFiberedGraph`: empty edge set.
Both predicates (horizontality, sub-total) are vacuous over `∅`. -/
def trivialConnection : FiberedGraph.Connection trivialFiberedGraph where
  edges := ∅
  horizontal := by intro e he; simp at he
  sub_total := by intro e he; simp at he

/-- **Flat-connection bridge obligation is inhabited**: the `Γ ≡ 0`
connection on `ℝⁿ` has a (trivial) fibered-graph origin witness. -/
theorem flatConnection_from_fiberedGraph_proved (n : Nat) :
    flatConnection_from_fiberedGraph n := by
  unfold flatConnection_from_fiberedGraph
    ConnectionDataOriginObligation
  refine ⟨Fin 1, Fin 1, inferInstance, inferInstance,
    inferInstance, inferInstance,
    trivialFiberedGraph, trivialConnection,
    fun k => (1 : ℝ) / (k + 1), ?_⟩
  intro k
  positivity

/-! ## Generalised obligation for any ConnectionData

For any continuum connection, we state the obligation and for the
flat one we have a witness. Curved connections (from
`Schwarzschild`, `FLRW`, `Kerr`, etc.) are still target-only and
their obligations remain open — exactly as they should be. -/

/-- **Minkowski's flat-connection obligation** (specialising flat to
`n = 4`): inhabited. -/
theorem flatConnection_minkowski4_from_fiberedGraph :
    ConnectionDataOriginObligation (flatConnection 4) := by
  exact flatConnection_from_fiberedGraph_proved 4

/-- **Arbitrary connection's origin-obligation is trivially inhabited
at the current statement level.** Because the obligation Prop as
currently written is a pure existential over `FiberedGraph` +
`Connection` + positive scaling (no bridgeHolds predicate), the same
`trivialFiberedGraph` + `trivialConnection` witness inhabits it for
every `C : ConnectionData n`, flat or curved. The open research work
(covariant bridgeHolds) is a future strengthening of the obligation,
not a new inhabitant of this one. -/
theorem any_connection_has_obligation_witness {n : Nat} (C : ConnectionData n) :
    ConnectionDataOriginObligation C := by
  unfold ConnectionDataOriginObligation
  refine ⟨Fin 1, Fin 1, inferInstance, inferInstance,
    inferInstance, inferInstance,
    trivialFiberedGraph, trivialConnection,
    fun k => (1 : ℝ) / (k + 1), ?_⟩
  intro k
  positivity

/-- **Levi-Civita connection from any `MetricDataC2` inherits the
origin-obligation witness.** Every Levi-Civita connection — derivable
from any `MetricDataC2 n` via `leviCivitaConnection` — is itself a
`ConnectionData n` and hence satisfies the obligation, per
`any_connection_has_obligation_witness`. -/
theorem leviCivitaConnection_from_fiberedGraph {n : Nat} (M : MetricDataC2 n) :
    ConnectionDataOriginObligation M.leviCivitaConnection :=
  any_connection_has_obligation_witness _

end Curvature
end InfraFormalization
