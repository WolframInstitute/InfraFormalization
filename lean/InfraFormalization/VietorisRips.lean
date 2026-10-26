/-
Vietoris-Rips complexes of hypergraphs.

This module defines, for a hypergraph `H` and a scale `ε : ℕ`, the
Vietoris-Rips edge relation `dist u v ≤ ε`, the simplex predicate (every
pair in a finset is within `ε`) and the 1-skeleton as a `SimpleGraph V`.
It proves that simplices are closed under subsets, that the empty set and
singletons are simplices, that simplices persist under increasing `ε`, and
that at `ε = 0` no two reachable vertices are adjacent.
-/

import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Hypergraph

/-- `u` and `v` are within hypergraph distance `ε`. -/
def VietorisRipsEdge (H : Hypergraph V) (ε : ℕ) (u v : V) : Prop :=
  H.dist u v ≤ ε

/-- Every pair of vertices in `S` is within hypergraph distance `ε`. -/
def VietorisRipsSimplex (H : Hypergraph V) (ε : ℕ) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, H.dist u v ≤ ε

/-- A subset of a Vietoris-Rips simplex is a Vietoris-Rips simplex. -/
theorem VietorisRipsSimplex.mono {H : Hypergraph V} {ε : ℕ}
    {S T : Finset V} (hS : H.VietorisRipsSimplex ε S) (hsub : T ⊆ S) :
    H.VietorisRipsSimplex ε T := by
  intros u hu v hv
  exact hS u (hsub hu) v (hsub hv)

/-- The empty set is a Vietoris-Rips simplex. -/
theorem VietorisRipsSimplex.empty (H : Hypergraph V) (ε : ℕ) :
    H.VietorisRipsSimplex ε ∅ := by
  intros u hu
  exact absurd hu (Finset.notMem_empty u)

/-- Every singleton is a Vietoris-Rips simplex. -/
theorem VietorisRipsSimplex.singleton (H : Hypergraph V) (ε : ℕ) (v : V) :
    H.VietorisRipsSimplex ε {v} := by
  intros u hu w hw
  rw [Finset.mem_singleton] at hu hw
  subst hu; subst hw
  rw [Hypergraph.dist_self]
  exact Nat.zero_le _

/-- A simplex at scale `ε` is a simplex at every scale `δ ≥ ε`. -/
theorem VietorisRipsSimplex.mono_scale {H : Hypergraph V} {ε δ : ℕ}
    {S : Finset V} (h : ε ≤ δ) (hS : H.VietorisRipsSimplex ε S) :
    H.VietorisRipsSimplex δ S := by
  intros u hu v hv
  exact le_trans (hS u hu v hv) h

/-- The simple graph on `V` in which distinct `u`, `v` are adjacent when
`dist u v ≤ ε`. -/
noncomputable def vietorisRipsGraph (H : Hypergraph V) (ε : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ H.dist u v ≤ ε
  symm := by
    rintro u v ⟨hne, hd⟩
    refine ⟨Ne.symm hne, ?_⟩
    rw [Hypergraph.dist_comm]
    exact hd
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

/-- If `v` is reachable from `u` in `H.toSimpleGraph`, then `u` and `v` are
not adjacent in `H.vietorisRipsGraph 0`. Unreachable pairs have
`dist = 0` and are excluded by the hypothesis. -/
theorem vietorisRipsGraph_zero_no_edges_reachable (H : Hypergraph V)
    {u v : V} (hreach : H.toSimpleGraph.Reachable u v) :
    ¬ (H.vietorisRipsGraph 0).Adj u v := by
  rintro ⟨hne, hd⟩
  have h0 : H.dist u v = 0 := Nat.le_zero.mp hd
  unfold Hypergraph.dist at h0
  rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at h0
  cases h0 with
  | inl heq => exact hne heq
  | inr hnr => exact hnr hreach

end Hypergraph

end InfraFormalization
