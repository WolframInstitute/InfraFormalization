/-
**Vietoris-Rips complex** of a hypergraph (Group IT / #133).

The Vietoris-Rips complex `VR_ε(H)` at scale `ε` is the abstract
simplicial complex whose simplices are finite subsets of `V` whose
pairwise hypergraph distances are all `≤ ε`.

This file formalises:

  * `VietorisRipsEdge H ε u v` — `u` and `v` are within `ε` under
    the hypergraph distance.
  * `VietorisRipsSimplex H ε S` — a finset `S ⊆ V` where every pair
    is `≤ ε`-close.
  * The 1-skeleton as a `SimpleGraph V` (`VietorisRipsGraph`).

Full ASC structure with higher-dimensional simplices is deferred;
this stub plus the topological-invariant interface (Betti numbers,
persistence) lives in IT2/IT4 follow-ups.

**Connection to hypergraphs.** Native. `VR_ε` is defined directly
in terms of `Hypergraph.dist`, which comes from the clique-expansion
adjacency — no continuum objects appear.
-/

import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Hypergraph

/-- **Vietoris-Rips 1-simplex predicate**: `u` and `v` are within
hypergraph-distance `ε`. -/
def VietorisRipsEdge (H : Hypergraph V) (ε : ℕ) (u v : V) : Prop :=
  H.dist u v ≤ ε

/-- **Vietoris-Rips simplex predicate**: every pair in `S` is within
`ε`. -/
def VietorisRipsSimplex (H : Hypergraph V) (ε : ℕ) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, H.dist u v ≤ ε

/-- **Every subset of a VR-simplex is a VR-simplex** (simplicial
closure property). -/
theorem VietorisRipsSimplex.mono {H : Hypergraph V} {ε : ℕ}
    {S T : Finset V} (hS : H.VietorisRipsSimplex ε S) (hsub : T ⊆ S) :
    H.VietorisRipsSimplex ε T := by
  intros u hu v hv
  exact hS u (hsub hu) v (hsub hv)

/-- **Empty simplex** is always a VR-simplex. -/
theorem VietorisRipsSimplex.empty (H : Hypergraph V) (ε : ℕ) :
    H.VietorisRipsSimplex ε ∅ := by
  intros u hu
  exact absurd hu (Finset.notMem_empty u)

/-- **Singletons are VR-simplices** (self-distance is 0). -/
theorem VietorisRipsSimplex.singleton (H : Hypergraph V) (ε : ℕ) (v : V) :
    H.VietorisRipsSimplex ε {v} := by
  intros u hu w hw
  rw [Finset.mem_singleton] at hu hw
  subst hu; subst hw
  rw [Hypergraph.dist_self]
  exact Nat.zero_le _

/-- **Monotonicity in `ε`**: enlarging the scale only adds simplices. -/
theorem VietorisRipsSimplex.mono_scale {H : Hypergraph V} {ε δ : ℕ}
    {S : Finset V} (h : ε ≤ δ) (hS : H.VietorisRipsSimplex ε S) :
    H.VietorisRipsSimplex δ S := by
  intros u hu v hv
  exact le_trans (hS u hu v hv) h

/-- **The VR 1-skeleton as a `SimpleGraph V`.** Vertices are all of
`V`; edges are unordered pairs at hypergraph distance `≤ ε` (and
distinct). Noncomputable because `dist` is noncomputable. -/
noncomputable def vietorisRipsGraph (H : Hypergraph V) (ε : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ H.dist u v ≤ ε
  symm := by
    rintro u v ⟨hne, hd⟩
    refine ⟨Ne.symm hne, ?_⟩
    rw [Hypergraph.dist_comm]
    exact hd
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

/-- **At `ε = 0`, the VR graph has no edges on a connected component**
— if `u` and `v` are distinct and reachable, they have distance `≥ 1`.
For pairs in different components the VR-0 edge predicate reduces to
the junk `dist = 0` value on the unreachable side; we state the
version restricted to reachable pairs. -/
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
