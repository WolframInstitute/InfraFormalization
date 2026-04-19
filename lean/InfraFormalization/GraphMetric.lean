/-
Graph metric on a hypergraph.

To connect hypergraph rewriting to continuum geometry we need a metric
on the vertex set. The standard choice is the *shortest-path graph
metric*: `d(u, v)` = minimum number of hyperedges one must traverse to
get from `u` to `v`, treating each hyperedge as connecting all of its
vertices.

We give a minimal interface here: walks, reachability, and a simple
scaled-hypergraph structure that is the hook for continuum-limit
theorems (parameterised by an edge length `ε : ℝ`).

For full-strength metric-space API we would integrate with Mathlib's
`PseudoMetricSpace` — that is a follow-up once the core theorems are
in place.
-/

import InfraFormalization.Hypergraph

namespace InfraFormalization

open Hypergraph

variable {V : Type*}

/-- A **walk** of length `n` in `H` from `u` to `v`: a sequence of
hyperedges `e₀, e₁, …, e_{n-1}` such that `u ∈ e₀`, `v ∈ e_{n-1}`, and
consecutive edges share a vertex. -/
structure Walk (H : Hypergraph V) (u v : V) (n : Nat) where
  edges : Fin n → Hyperedge V
  edges_mem : ∀ i, edges i ∈ H.edges
  start_mem : ∀ h : 0 < n, u ∈ (edges ⟨0, h⟩).verts
  end_mem : ∀ h : 0 < n, v ∈ (edges ⟨n - 1, by omega⟩).verts
  shared : ∀ i (hi : i + 1 < n),
    ∃ w : V, w ∈ (edges ⟨i, Nat.lt_of_succ_lt hi⟩).verts ∧
             w ∈ (edges ⟨i + 1, hi⟩).verts
  trivial_case : n = 0 → u = v

/-- `u` and `v` are reachable in `H` — some walk of finite length
connects them. -/
def Reachable (H : Hypergraph V) (u v : V) : Prop :=
  ∃ n, Nonempty (Walk H u v n)

/-- A **scaled hypergraph**: a hypergraph equipped with an edge length
`ε : ℝ`. A sequence `(H_n, ε_n)` with `ε_n → 0` is the natural
object whose metric limits one might study. -/
structure ScaledHypergraph (V : Type*) where
  graph : Hypergraph V
  ε : ℝ
  ε_pos : 0 < ε

end InfraFormalization
