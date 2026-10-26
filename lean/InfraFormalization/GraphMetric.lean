/-
Walks and reachability in a hypergraph.

This module defines `Walk H u v n`, a sequence of `n` hyperedges of `H` in which consecutive edges
share a vertex, the first contains `u` and the last contains `v`.
It defines `Reachable H u v` as the existence of a walk of some length, and `ScaledHypergraph`, a
hypergraph paired with a positive real edge length `ε`.
-/

import InfraFormalization.Hypergraph

namespace InfraFormalization

open Hypergraph

variable {V : Type*}

/-- A walk of length `n` in `H` from `u` to `v`: hyperedges `e₀, …, e_{n-1}` of `H` with `u ∈ e₀`,
`v ∈ e_{n-1}`, consecutive edges sharing a vertex, and `u = v` when `n = 0`. -/
structure Walk (H : Hypergraph V) (u v : V) (n : Nat) where
  edges : Fin n → Hyperedge V
  edges_mem : ∀ i, edges i ∈ H.edges
  start_mem : ∀ h : 0 < n, u ∈ (edges ⟨0, h⟩).verts
  end_mem : ∀ h : 0 < n, v ∈ (edges ⟨n - 1, by omega⟩).verts
  shared : ∀ i (hi : i + 1 < n),
    ∃ w : V, w ∈ (edges ⟨i, Nat.lt_of_succ_lt hi⟩).verts ∧
             w ∈ (edges ⟨i + 1, hi⟩).verts
  trivial_case : n = 0 → u = v

/-- There is a walk in `H` from `u` to `v` of some length `n`. -/
def Reachable (H : Hypergraph V) (u v : V) : Prop :=
  ∃ n, Nonempty (Walk H u v n)

/-- A hypergraph together with an edge length `ε : ℝ` and a proof that `0 < ε`. -/
structure ScaledHypergraph (V : Type*) where
  graph : Hypergraph V
  ε : ℝ
  ε_pos : 0 < ε

end InfraFormalization
