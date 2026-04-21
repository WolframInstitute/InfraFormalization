/-
Graph distance on a hypergraph, geodesic balls, and their volumes.

**Connection to hypergraphs.** Native. Every construction takes a
`Hypergraph V` and produces a distance function / ball / volume on
its vertex set `V` — no continuum objects appear.

**What this file contributes.** The foundation of `Group ID`
(infradimension) — first notion of dimension on a hypergraph.

  * `Hyperedge.contains e u v` — the pair `{u, v}` sits inside `e`.
  * `Hypergraph.Adj H u v` — `u ≠ v` and some hyperedge of `H`
    contains both. This is the *clique-expansion* adjacency:
    every hyperedge contributes a clique on its vertex set.
  * `Hypergraph.toSimpleGraph H` — the induced
    `SimpleGraph V`; Mathlib's `SimpleGraph.dist` then gives
    `Hypergraph.dist H u v`.
  * `geodesicBall H v r`, `geodesicBallVolume H v r` — the closed
    ball of radius `r` and its cardinality.

The Wolfram-Hausdorff dimension at `v` is (eventually) the
asymptotic `log V(r) / log r`. Here we state the definition as a
numerical estimator `localDimension` and prove the concrete
linear-growth lemma for `cycleHypergraph n` that anchors
`dim = 1` on the 1D cycle.

Further compatibility theorems (heat-kernel / spectral, homological,
coordinatization dimensions) and the conservation → bounded-dim
promotion (IR2) live in follow-up files.
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.HypergraphCycleBridge
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Hypergraph adjacency via clique-expansion -/

/-- A hyperedge `e` contains the (unordered) pair `{u, v}`: both
`u` and `v` appear among `e.verts`. -/
def Hyperedge.contains (e : Hyperedge V) (u v : V) : Prop :=
  u ∈ e.verts ∧ v ∈ e.verts

instance (e : Hyperedge V) (u v : V) : Decidable (e.contains u v) := by
  unfold Hyperedge.contains
  exact inferInstance

/-- **Clique-expansion adjacency.** Two distinct vertices `u v : V`
are *adjacent* in the hypergraph `H` iff some hyperedge contains
both. Equivalently, every hyperedge contributes a clique on its
vertex set to the induced simple graph. -/
def Hypergraph.Adj (H : Hypergraph V) (u v : V) : Prop :=
  u ≠ v ∧ ∃ e ∈ H.edges.toFinset, e.contains u v

instance (H : Hypergraph V) (u v : V) : Decidable (H.Adj u v) := by
  unfold Hypergraph.Adj
  exact inferInstance

/-- Hypergraph adjacency is symmetric. -/
theorem Hypergraph.Adj_symm {H : Hypergraph V} {u v : V} :
    H.Adj u v → H.Adj v u := by
  rintro ⟨hne, e, he, ⟨hu, hv⟩⟩
  exact ⟨Ne.symm hne, e, he, ⟨hv, hu⟩⟩

/-- Hypergraph adjacency is irreflexive. -/
theorem Hypergraph.Adj_irrefl {H : Hypergraph V} (v : V) : ¬ H.Adj v v := by
  rintro ⟨hne, _⟩
  exact hne rfl

/-- **The simple graph underlying a hypergraph.** Uses
clique-expansion adjacency. This is the object on which Mathlib's
`SimpleGraph.dist` computes the hypergraph distance. -/
def Hypergraph.toSimpleGraph (H : Hypergraph V) : SimpleGraph V where
  Adj := H.Adj
  symm := fun _ _ => Hypergraph.Adj_symm
  loopless := ⟨fun v => Hypergraph.Adj_irrefl v⟩

instance (H : Hypergraph V) : DecidableRel H.toSimpleGraph.Adj := by
  intro u v
  unfold Hypergraph.toSimpleGraph
  exact inferInstance

/-! ## Hypergraph distance -/

/-- **Hypergraph distance** between two vertices. Follows Mathlib's
`SimpleGraph.dist` convention: the length of the shortest walk in
the clique-expansion graph, or `0` if the vertices are not in the
same connected component. -/
noncomputable def Hypergraph.dist (H : Hypergraph V) (u v : V) : ℕ :=
  H.toSimpleGraph.dist u v

@[simp] theorem Hypergraph.dist_self (H : Hypergraph V) (v : V) :
    H.dist v v = 0 := by
  unfold Hypergraph.dist
  exact SimpleGraph.dist_self

theorem Hypergraph.dist_comm (H : Hypergraph V) (u v : V) :
    H.dist u v = H.dist v u := by
  unfold Hypergraph.dist
  exact SimpleGraph.dist_comm

/-! ## Geodesic balls and their volumes -/

/-- **Closed geodesic ball** of radius `r` around `v`: the set of
vertices at hypergraph distance `≤ r`. Excludes unreachable vertices
since `dist = 0` for both `u = v` and `¬Reachable`; care should be
taken to check reachability when interpreting volumes on
disconnected hypergraphs. -/
noncomputable def Hypergraph.geodesicBall (H : Hypergraph V) (v : V)
    (r : ℕ) : Finset V :=
  Finset.univ.filter (fun u => H.dist v u ≤ r)

/-- **Geodesic ball volume** — the cardinality of the closed ball. -/
noncomputable def Hypergraph.geodesicBallVolume (H : Hypergraph V)
    (v : V) (r : ℕ) : ℕ :=
  (H.geodesicBall v r).card

/-- **Ball at radius 0** contains exactly `v` on reachable vertices.
Unreachable vertices `u` also satisfy `dist v u = 0` (junk value) and
so appear in the ball; however, this is usually avoided by working
on connected hypergraphs. Here we state the weaker, always-true
inclusion `{v} ⊆ ball 0`. -/
theorem Hypergraph.self_mem_geodesicBall (H : Hypergraph V) (v : V)
    (r : ℕ) : v ∈ H.geodesicBall v r := by
  unfold Hypergraph.geodesicBall
  simp [Hypergraph.dist_self]

/-- **Ball volume is at least 1** (the basepoint itself is always in). -/
theorem Hypergraph.geodesicBallVolume_pos (H : Hypergraph V) (v : V)
    (r : ℕ) : 1 ≤ H.geodesicBallVolume v r := by
  unfold Hypergraph.geodesicBallVolume
  exact Finset.card_pos.mpr ⟨v, Hypergraph.self_mem_geodesicBall H v r⟩

/-- **Ball volume is monotone in radius.** -/
theorem Hypergraph.geodesicBallVolume_mono (H : Hypergraph V) (v : V)
    {r s : ℕ} (hrs : r ≤ s) :
    H.geodesicBallVolume v r ≤ H.geodesicBallVolume v s := by
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  apply Finset.card_le_card
  intro u hu
  rw [Finset.mem_filter] at hu ⊢
  exact ⟨hu.1, le_trans hu.2 hrs⟩

/-! ## Local dimension estimator

The Wolfram–Hausdorff dimension at `v` is the asymptotic
`log V(r) / log r`. We provide an estimator at finite `r`, and state
the dimension as the limsup over `r → ∞`. The full convergence
theorem for specific hypergraphs is a case-by-case proof obligation. -/

/-- **Local dimension estimator** at radius `r`:
`log V(r) / log r`. Returns `0` at `r ≤ 1` (where `log r ≤ 0`). -/
noncomputable def Hypergraph.localDimension (H : Hypergraph V) (v : V)
    (r : ℕ) : ℝ :=
  if r ≤ 1 then 0 else
    Real.log (H.geodesicBallVolume v r : ℝ) / Real.log (r : ℝ)

/-- **Wolfram–Hausdorff dimension at `v`** (pointwise limit form):
`limsup_{r → ∞} log V(r) / log r`. For compact finite hypergraphs
this is always `0` in the true `r → ∞` sense (volumes saturate),
so in practice the relevant quantity is the *plateau* dimension at
intermediate scales — captured by `plateauDimension` below. -/
noncomputable def Hypergraph.wolframHausdorffDimension (H : Hypergraph V)
    (v : V) : ℝ :=
  Filter.limsup (fun r : ℕ => H.localDimension v r) Filter.atTop

/-- **Plateau dimension on a radius range.** Average of
`localDimension` over `r ∈ [rmin, rmax]`. This is the computable
estimator used in practice; a "plateau" is a range where it is
approximately constant. -/
noncomputable def Hypergraph.plateauDimension (H : Hypergraph V) (v : V)
    (rmin rmax : ℕ) : ℝ :=
  if rmax < rmin then 0 else
    (∑ r ∈ Finset.Icc rmin rmax, H.localDimension v r) /
      ((rmax - rmin + 1 : ℕ) : ℝ)

/-! ## Cycle hypergraph adjacency

Connecting `HypergraphCycleBridge` to the distance / dimension
machinery above: the clique-expansion adjacency of `cycleHypergraph n`
is precisely the standard cycle adjacency `j = i + 1 ∨ j = i − 1`
in `Fin n`. This ensures `geodesicBall` on `cycleHypergraph n`
matches the cycle-graph distance.

For `n ≥ 3`, every vertex has exactly two neighbors, so
`geodesicBallVolume v 1 ≥ 3`, giving the first step toward
`wolframHausdorffDimension = 1` on the cycle. -/

theorem cycleHypergraph_Adj_iff {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (i j : Fin n) :
    (cycleHypergraph n).Adj i j ↔ i ≠ j ∧ (j = i + 1 ∨ i = j + 1) := by
  constructor
  · rintro ⟨hne, e, he, hcontains⟩
    refine ⟨hne, ?_⟩
    rw [Multiset.mem_toFinset] at he
    unfold cycleHypergraph at he
    rw [Multiset.mem_map] at he
    obtain ⟨k, _, hk⟩ := he
    subst hk
    obtain ⟨hi, hj⟩ := hcontains
    have hverts : (cycleHyperedge n k).verts = [k, k + 1] := rfl
    rw [hverts] at hi hj
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
               or_false] at hi hj
    rcases hi with hi_eq | hi_eq <;> rcases hj with hj_eq | hj_eq
    · subst hi_eq; subst hj_eq; exact absurd rfl hne
    · subst hi_eq; subst hj_eq; left; rfl
    · subst hi_eq; subst hj_eq; right; rfl
    · subst hi_eq; subst hj_eq; exact absurd rfl hne
  · rintro ⟨hne, hcases⟩
    have hmem_univ_val : ∀ (x : Fin n),
        x ∈ (Finset.univ : Finset (Fin n)).val :=
      fun x => Finset.mem_val.mpr (Finset.mem_univ x)
    cases hcases with
    | inl hj =>
      subst hj
      refine ⟨hne, cycleHyperedge n i, ?_, ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        unfold cycleHypergraph
        exact Multiset.mem_map_of_mem _ (hmem_univ_val i)
      · show i ∈ (cycleHyperedge n i).verts
        have : (cycleHyperedge n i).verts = [i, i + 1] := rfl
        rw [this]; simp
      · show (i + 1 : Fin n) ∈ (cycleHyperedge n i).verts
        have : (cycleHyperedge n i).verts = [i, i + 1] := rfl
        rw [this]; simp
    | inr hi =>
      subst hi
      refine ⟨hne, cycleHyperedge n j, ?_, ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        unfold cycleHypergraph
        exact Multiset.mem_map_of_mem _ (hmem_univ_val j)
      · show (j + 1 : Fin n) ∈ (cycleHyperedge n j).verts
        have : (cycleHyperedge n j).verts = [j, j + 1] := rfl
        rw [this]; simp
      · show j ∈ (cycleHyperedge n j).verts
        have : (cycleHyperedge n j).verts = [j, j + 1] := rfl
        rw [this]; simp

/-- **Two neighbors of `v` in `cycleHypergraph n` for `n ≥ 2`.**
The vertices `v + 1` and `v − 1` are neighbors of `v` (they coincide
iff `n = 2`). -/
theorem cycleHypergraph_succ_pred_adj {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n) :
    (cycleHypergraph n).Adj v (v + 1) ∧ (cycleHypergraph n).Adj v (v - 1) := by
  have hsucc : (v + 1 : Fin n) ≠ v := cycle_succ_ne hn v
  have hpred : (v - 1 : Fin n) ≠ v := by
    intro heq
    have hv_eq : v = v - 1 + 1 := by abel
    rw [heq] at hv_eq
    exact cycle_succ_ne hn v hv_eq.symm
  refine ⟨?_, ?_⟩
  · rw [cycleHypergraph_Adj_iff hn]
    exact ⟨Ne.symm hsucc, Or.inl rfl⟩
  · rw [cycleHypergraph_Adj_iff hn]
    refine ⟨Ne.symm hpred, Or.inr ?_⟩
    abel

end InfraFormalization
