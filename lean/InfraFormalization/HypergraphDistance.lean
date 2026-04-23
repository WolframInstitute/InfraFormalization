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

/-- **Adjacency is monotone under union on the left.** Adding more
edges can only add to adjacency: `H₁.Adj u v → (H₁ + H₂).Adj u v`.
Lifts Multiset.mem_add to the adjacency level. -/
theorem Hypergraph.Adj_add_left {H₁ H₂ : Hypergraph V} {u v : V}
    (h : H₁.Adj u v) : (H₁ + H₂).Adj u v := by
  obtain ⟨hne, e, he, hcontains⟩ := h
  refine ⟨hne, e, ?_, hcontains⟩
  rw [Multiset.mem_toFinset] at he ⊢
  show e ∈ (H₁.edges + H₂.edges)
  exact Multiset.mem_add.mpr (Or.inl he)

/-- **Adjacency is monotone under union on the right.** Symmetric. -/
theorem Hypergraph.Adj_add_right {H₁ H₂ : Hypergraph V} {u v : V}
    (h : H₂.Adj u v) : (H₁ + H₂).Adj u v := by
  obtain ⟨hne, e, he, hcontains⟩ := h
  refine ⟨hne, e, ?_, hcontains⟩
  rw [Multiset.mem_toFinset] at he ⊢
  show e ∈ (H₁.edges + H₂.edges)
  exact Multiset.mem_add.mpr (Or.inr he)

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

/-- **Triangle inequality for the hypergraph distance**, conditional on
reachability (via `SimpleGraph.Reachable.dist_triangle_left`). On a
disconnected graph, `dist = 0` as a junk value on unreachable pairs,
so the unconditional inequality fails; this form requires the
connecting edge `u ⇝ v` to be reachable. -/
theorem Hypergraph.dist_triangle_of_reachable_left (H : Hypergraph V)
    {u v : V} (h : H.toSimpleGraph.Reachable u v) (w : V) :
    H.dist u w ≤ H.dist u v + H.dist v w := by
  unfold Hypergraph.dist
  exact SimpleGraph.Reachable.dist_triangle_left h w

/-- **Triangle inequality**, right-variant. -/
theorem Hypergraph.dist_triangle_of_reachable_right (H : Hypergraph V)
    (u : V) {v w : V} (h : H.toSimpleGraph.Reachable v w) :
    H.dist u w ≤ H.dist u v + H.dist v w := by
  unfold Hypergraph.dist
  exact SimpleGraph.Reachable.dist_triangle_right h u

/-- **Unconditional triangle inequality** on a connected hypergraph:
for any three vertices `u, v, w : V`, `dist u w ≤ dist u v + dist v w`.
This is the condition needed for `(V, Hypergraph.dist H)` to be a
pseudo-metric space (modulo the ℕ → ℝ cast). -/
theorem Hypergraph.dist_triangle (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected) (u v w : V) :
    H.dist u w ≤ H.dist u v + H.dist v w := by
  unfold Hypergraph.dist
  exact hconn.dist_triangle

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

/-- **For `n ≥ 3`, `v + 1 ≠ v − 1` in `Fin n`.** This separates the
two neighbors in `cycleHypergraph_succ_pred_adj`. -/
theorem cycle_succ_ne_pred {n : Nat} [NeZero n] (hn : 3 ≤ n) (v : Fin n) :
    (v + 1 : Fin n) ≠ (v - 1 : Fin n) := by
  intro heq
  have hn_pos : 0 < n := by omega
  have h1 : (1 : Fin n).val = 1 := by
    show 1 % n = 1
    have : 1 < n := by omega
    exact Nat.mod_eq_of_lt this
  have h_succ_val : (v + 1 : Fin n).val = (v.val + 1) % n := by
    rw [Fin.val_add, h1]
  have h_pred_val : (v - 1 : Fin n).val = (n - 1 + v.val) % n := by
    rw [Fin.sub_def, h1]
  have hval : (v.val + 1) % n = (n - 1 + v.val) % n := by
    rw [← h_succ_val, ← h_pred_val, heq]
  have hv_lt : v.val < n := v.isLt
  -- Case split on where v.val sits in [0, n-1].
  rcases Nat.lt_or_ge v.val (n - 1) with hlt1 | hge1
  · -- v.val ≤ n - 2, so v.val + 1 < n, (v.val+1) % n = v.val + 1.
    have h_lhs : (v.val + 1) % n = v.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    rcases Nat.eq_zero_or_pos v.val with hz | hpos
    · -- v.val = 0: RHS = (n - 1) % n = n - 1, LHS = 1. Need 1 = n-1, i.e., n=2.
      rw [hz] at hval h_lhs
      rw [h_lhs] at hval
      have h_rhs : (n - 1 + 0) % n = n - 1 := Nat.mod_eq_of_lt (by omega)
      rw [h_rhs] at hval
      omega
    · -- v.val ≥ 1: RHS = (n - 1 + v.val) % n = v.val - 1.
      have h_ge_n : n ≤ n - 1 + v.val := by omega
      have h_lt_2n : n - 1 + v.val < 2 * n := by omega
      have h_rhs : (n - 1 + v.val) % n = n - 1 + v.val - n := by
        rw [Nat.mod_eq_sub_mod h_ge_n]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h_lhs, h_rhs] at hval
      omega
  · -- v.val = n - 1.
    have hv_eq : v.val = n - 1 := by omega
    rw [hv_eq] at hval
    have h_lhs : (n - 1 + 1) % n = 0 := by
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.mod_self]
    rw [h_lhs] at hval
    have h_rhs_aux : n - 1 + (n - 1) = 2 * n - 2 := by omega
    rw [h_rhs_aux] at hval
    -- hval : 0 = (2n - 2) % n; for n ≥ 3, 2n - 2 = n + (n - 2), so mod = n - 2.
    have h_eq : 2 * n - 2 = n + (n - 2) := by omega
    have h_ge : n ≤ 2 * n - 2 := by omega
    have h_rhs : (2 * n - 2) % n = n - 2 := by
      rw [h_eq, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_rhs] at hval
    omega

/-- **For `n ≥ 4`, `v + 2 ≠ v` in `Fin n`.** The shift-by-2 is
non-trivial once `n ≥ 3`; the proof handles the `n = 3` edge case. -/
theorem cycle_add_two_ne_self {n : Nat} [NeZero n] (hn : 3 ≤ n) (v : Fin n) :
    (v + 2 : Fin n) ≠ v := by
  intro heq
  have hval : (v + 2 : Fin n).val = v.val := congrArg Fin.val heq
  have h_two : (2 : Fin n).val = 2 := by
    show 2 % n = 2; exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_add, h_two] at hval
  have hvlt : v.val < n := v.isLt
  rcases Nat.lt_or_ge (v.val + 2) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hval; omega
  · have h_ge_n : n ≤ v.val + 2 := hge
    have h_lt_2n : v.val + 2 < 2 * n := by omega
    have hmod : (v.val + 2) % n = v.val + 2 - n := by
      rw [Nat.mod_eq_sub_mod h_ge_n]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod] at hval; omega

/-- **For `n ≥ 3`, `v − 2 ≠ v` in `Fin n`.** Symmetric counterpart of
`cycle_add_two_ne_self`: shift-by-(−2) is also non-trivial. -/
theorem cycle_sub_two_ne_self {n : Nat} [NeZero n] (hn : 3 ≤ n) (v : Fin n) :
    (v - 2 : Fin n) ≠ v := by
  intro heq
  -- v - 2 = v ⟹ (v - 2) + 2 = v + 2 ⟹ v = v + 2, contradicting `cycle_add_two_ne_self`.
  have h_add : (v - 2 : Fin n) + 2 = v + 2 := by rw [heq]
  have h_eq : v = v + 2 := by
    have : (v - 2 : Fin n) + 2 = v := by abel
    rw [this] at h_add; exact h_add
  exact cycle_add_two_ne_self hn v h_eq.symm

/-- **Radius-1 ball volume in cycleHypergraph (n ≥ 3) is ≥ 3.**
Exhibits three distinct vertices (`v`, `v + 1`, `v − 1`) in the
ball, all at distance ≤ 1. This establishes the first concrete
dimensional step on the cycle: `V(v, 1) ≥ 3`, hence
`localDimension v 1`-class expectations are consistent with the
cycle being 1-dimensional (where `V(v, r) ~ 2r + 1`). -/
theorem cycleHypergraph_ballVolume_one_ge_three {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v : Fin n) :
    3 ≤ (cycleHypergraph n).geodesicBallVolume v 1 := by
  have hn2 : 2 ≤ n := by omega
  have ⟨hadj_succ, hadj_pred⟩ := cycleHypergraph_succ_pred_adj hn2 v
  have h_succ_in : v + 1 ∈ (cycleHypergraph n).geodesicBall v 1 := by
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Hypergraph.dist
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj_succ]
  have h_pred_in : v - 1 ∈ (cycleHypergraph n).geodesicBall v 1 := by
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Hypergraph.dist
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj_pred]
  have h_self_in : v ∈ (cycleHypergraph n).geodesicBall v 1 :=
    Hypergraph.self_mem_geodesicBall _ _ _
  have hne_succ : v ≠ v + 1 := Ne.symm (cycle_succ_ne hn2 v)
  have hne_pred : v ≠ v - 1 := by
    intro heq
    have h_ : v = v - 1 + 1 := by abel
    rw [← heq] at h_
    exact cycle_succ_ne hn2 v h_.symm
  have hne_succ_pred : v + 1 ≠ v - 1 := cycle_succ_ne_pred hn v
  have h_not_mem_1 : v + 1 ∉ ({v - 1} : Finset (Fin n)) := by
    rw [Finset.mem_singleton]; exact hne_succ_pred
  have h_not_mem_2 : v ∉ ({v + 1, v - 1} : Finset (Fin n)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    intro hcases
    cases hcases with
    | inl h => exact hne_succ h
    | inr h => exact hne_pred h
  have h_triple_card :
      ({v, v + 1, v - 1} : Finset (Fin n)).card = 3 := by
    rw [show ({v, v + 1, v - 1} : Finset (Fin n))
        = insert v (insert (v + 1) {v - 1}) from rfl]
    rw [Finset.card_insert_of_notMem h_not_mem_2]
    rw [Finset.card_insert_of_notMem h_not_mem_1]
    rw [Finset.card_singleton]
  have h_subset :
      ({v, v + 1, v - 1} : Finset (Fin n)) ⊆
      (cycleHypergraph n).geodesicBall v 1 := by
    intros u hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact h_self_in
    · exact h_succ_in
    · exact h_pred_in
  unfold Hypergraph.geodesicBallVolume
  calc 3 = ({v, v + 1, v - 1} : Finset (Fin n)).card := h_triple_card.symm
    _ ≤ _ := Finset.card_le_card h_subset

/-! ## Cycle-hypergraph connectivity

For `n ≥ 2`, `cycleHypergraph n` is a connected graph. This lets us
apply the unconditional triangle inequality `Hypergraph.dist_triangle`
to cycles. -/

/-- **Reachability from `0` to any vertex in `cycleHypergraph n`** via
the successor-adjacency ladder. -/
theorem cycleHypergraph_reachable_zero {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n) :
    (cycleHypergraph n).toSimpleGraph.Reachable 0 v := by
  -- Auxiliary lemma: for every k : ℕ with k < n, Reachable 0 ⟨k, _⟩.
  suffices haux : ∀ (k : ℕ) (hkn : k < n),
      (cycleHypergraph n).toSimpleGraph.Reachable 0 ⟨k, hkn⟩ by
    have := haux v.val v.isLt
    convert this
  intro k
  induction k with
  | zero =>
    intro hkn
    exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro hkn
    have hk_lt : k < n := by omega
    let vk : Fin n := ⟨k, hk_lt⟩
    have ih' : (cycleHypergraph n).toSimpleGraph.Reachable 0 vk := ih hk_lt
    -- ⟨k+1, hkn⟩ = vk + 1 in Fin n.
    have h_one : (1 : Fin n).val = 1 := by
      show 1 % n = 1; exact Nat.mod_eq_of_lt (by omega)
    have hv_eq : (⟨k + 1, hkn⟩ : Fin n) = vk + 1 := by
      apply Fin.ext
      rw [Fin.val_add, h_one]
      rw [Nat.mod_eq_of_lt (by omega : vk.val + 1 < n)]
    have hadj : (cycleHypergraph n).toSimpleGraph.Adj vk (vk + 1) :=
      (cycleHypergraph_succ_pred_adj hn vk).1
    rw [hv_eq]
    exact ih'.trans hadj.reachable

/-- **`cycleHypergraph n` is connected** for `n ≥ 2`. Using the
reachability-from-zero theorem + symmetry + transitivity. -/
theorem cycleHypergraph_connected {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (cycleHypergraph n).toSimpleGraph.Connected := by
  refine SimpleGraph.Connected.mk ?_
  intro u v
  have hu := cycleHypergraph_reachable_zero hn u
  have hv := cycleHypergraph_reachable_zero hn v
  exact hu.symm.trans hv

/-- **Triangle inequality specialised to `cycleHypergraph n`**. -/
theorem cycleHypergraph_dist_triangle {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (u v w : Fin n) :
    (cycleHypergraph n).dist u w ≤
      (cycleHypergraph n).dist u v + (cycleHypergraph n).dist v w :=
  Hypergraph.dist_triangle _ (cycleHypergraph_connected hn) u v w

/-- **`v + 1 + 1 = v + 2` in `Fin n`** — follows from associativity and
`(1 + 1 : Fin n) = 2`. Used to re-shape adjacency statements. -/
private theorem cycle_add_one_one_eq_add_two {n : Nat} [NeZero n] (v : Fin n) :
    (v + 1 + 1 : Fin n) = v + 2 := by
  rw [add_assoc]
  congr 1
  apply Fin.ext
  simp [Fin.val_add]

/-- **`v - 1 - 1 = v - 2` in `Fin n`** — commutative-group computation. -/
private theorem cycle_sub_one_one_eq_sub_two {n : Nat} [NeZero n] (v : Fin n) :
    (v - 1 - 1 : Fin n) = v - 2 := by
  rw [sub_sub]
  congr 1
  apply Fin.ext
  simp [Fin.val_add]

/-- **Adjacency `(v + 1, v + 2)` on `cycleHypergraph n` for `n ≥ 2`.** Obtained
by applying `cycleHypergraph_succ_pred_adj` at `v + 1`. -/
theorem cycleHypergraph_succ_succ_adj {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n) :
    (cycleHypergraph n).Adj (v + 1) (v + 2) := by
  have h := (cycleHypergraph_succ_pred_adj hn (v + 1)).1
  rwa [cycle_add_one_one_eq_add_two] at h

/-- **Adjacency `(v - 1, v - 2)` on `cycleHypergraph n` for `n ≥ 2`.** Obtained
by applying `cycleHypergraph_succ_pred_adj` at `v - 1`. -/
theorem cycleHypergraph_pred_pred_adj {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n) :
    (cycleHypergraph n).Adj (v - 1) (v - 2) := by
  have h := (cycleHypergraph_succ_pred_adj hn (v - 1)).2
  rwa [cycle_sub_one_one_eq_sub_two] at h

/-- **`dist v (v + 2) ≤ 2` on `cycleHypergraph n` for `n ≥ 2`.**
Via triangle inequality: `dist v (v+2) ≤ dist v (v+1) + dist (v+1) (v+2)
= 1 + 1 = 2`. -/
theorem cycleHypergraph_dist_add_two_le {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v : Fin n) :
    (cycleHypergraph n).dist v (v + 2) ≤ 2 := by
  have h1 : (cycleHypergraph n).dist v (v + 1) = 1 := by
    unfold Hypergraph.dist
    exact SimpleGraph.dist_eq_one_iff_adj.mpr (cycleHypergraph_succ_pred_adj hn v).1
  have h2 : (cycleHypergraph n).dist (v + 1) (v + 2) = 1 := by
    unfold Hypergraph.dist
    exact SimpleGraph.dist_eq_one_iff_adj.mpr (cycleHypergraph_succ_succ_adj hn v)
  calc (cycleHypergraph n).dist v (v + 2)
      ≤ (cycleHypergraph n).dist v (v + 1) + (cycleHypergraph n).dist (v + 1) (v + 2) :=
        cycleHypergraph_dist_triangle hn v (v + 1) (v + 2)
    _ = 1 + 1 := by rw [h1, h2]
    _ = 2 := rfl

/-- **`dist v (v - 2) ≤ 2` on `cycleHypergraph n` for `n ≥ 2`.**
Symmetric counterpart via the predecessor walk. -/
theorem cycleHypergraph_dist_sub_two_le {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v : Fin n) :
    (cycleHypergraph n).dist v (v - 2) ≤ 2 := by
  have h1 : (cycleHypergraph n).dist v (v - 1) = 1 := by
    unfold Hypergraph.dist
    exact SimpleGraph.dist_eq_one_iff_adj.mpr (cycleHypergraph_succ_pred_adj hn v).2
  have h2 : (cycleHypergraph n).dist (v - 1) (v - 2) = 1 := by
    unfold Hypergraph.dist
    exact SimpleGraph.dist_eq_one_iff_adj.mpr (cycleHypergraph_pred_pred_adj hn v)
  calc (cycleHypergraph n).dist v (v - 2)
      ≤ (cycleHypergraph n).dist v (v - 1) + (cycleHypergraph n).dist (v - 1) (v - 2) :=
        cycleHypergraph_dist_triangle hn v (v - 1) (v - 2)
    _ = 1 + 1 := by rw [h1, h2]
    _ = 2 := rfl

/-- **Iterated forward shift is `k` steps away from `v` on
`cycleHypergraph n` for `n ≥ 2`**: `dist v (((· + 1)^[k]) v) ≤ k`. Induction
on `k` via triangle inequality + adjacency. Provides a uniform upper
bound without relying on `Fin.NatCast` coercion. -/
theorem cycleHypergraph_dist_iterSucc_le {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v : Fin n) : ∀ (k : ℕ),
    (cycleHypergraph n).dist v ((fun x : Fin n => x + 1)^[k] v) ≤ k := by
  intro k
  induction k with
  | zero =>
    show (cycleHypergraph n).dist v v ≤ 0
    exact le_of_eq (Hypergraph.dist_self _ v)
  | succ k ih =>
    -- (f^[k+1]) v = f (f^[k] v), so the shifted vertex is f^[k] v + 1
    have h_iter : (fun x : Fin n => x + 1)^[k + 1] v = (fun x : Fin n => x + 1)^[k] v + 1 := by
      rw [Function.iterate_succ']; rfl
    have h_adj : (cycleHypergraph n).Adj
        ((fun x : Fin n => x + 1)^[k] v)
        ((fun x : Fin n => x + 1)^[k] v + 1) :=
      (cycleHypergraph_succ_pred_adj hn _).1
    have h_dist_step : (cycleHypergraph n).dist
        ((fun x : Fin n => x + 1)^[k] v)
        ((fun x : Fin n => x + 1)^[k] v + 1) = 1 := by
      unfold Hypergraph.dist
      exact SimpleGraph.dist_eq_one_iff_adj.mpr h_adj
    calc (cycleHypergraph n).dist v ((fun x : Fin n => x + 1)^[k + 1] v)
        = (cycleHypergraph n).dist v ((fun x : Fin n => x + 1)^[k] v + 1) := by rw [h_iter]
      _ ≤ (cycleHypergraph n).dist v ((fun x : Fin n => x + 1)^[k] v)
          + (cycleHypergraph n).dist ((fun x : Fin n => x + 1)^[k] v)
              ((fun x : Fin n => x + 1)^[k] v + 1) :=
            cycleHypergraph_dist_triangle hn v _ _
      _ ≤ k + 1 := by rw [h_dist_step]; exact Nat.add_le_add_right ih 1

/-- **Iterated backward shift is `k` steps away from `v`**: symmetric
counterpart of `cycleHypergraph_dist_iterSucc_le`. -/
theorem cycleHypergraph_dist_iterPred_le {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v : Fin n) : ∀ (k : ℕ),
    (cycleHypergraph n).dist v ((fun x : Fin n => x - 1)^[k] v) ≤ k := by
  intro k
  induction k with
  | zero =>
    show (cycleHypergraph n).dist v v ≤ 0
    exact le_of_eq (Hypergraph.dist_self _ v)
  | succ k ih =>
    have h_iter : (fun x : Fin n => x - 1)^[k + 1] v = (fun x : Fin n => x - 1)^[k] v - 1 := by
      rw [Function.iterate_succ']; rfl
    have h_adj : (cycleHypergraph n).Adj
        ((fun x : Fin n => x - 1)^[k] v)
        ((fun x : Fin n => x - 1)^[k] v - 1) :=
      (cycleHypergraph_succ_pred_adj hn _).2
    have h_dist_step : (cycleHypergraph n).dist
        ((fun x : Fin n => x - 1)^[k] v)
        ((fun x : Fin n => x - 1)^[k] v - 1) = 1 := by
      unfold Hypergraph.dist
      exact SimpleGraph.dist_eq_one_iff_adj.mpr h_adj
    calc (cycleHypergraph n).dist v ((fun x : Fin n => x - 1)^[k + 1] v)
        = (cycleHypergraph n).dist v ((fun x : Fin n => x - 1)^[k] v - 1) := by rw [h_iter]
      _ ≤ (cycleHypergraph n).dist v ((fun x : Fin n => x - 1)^[k] v)
          + (cycleHypergraph n).dist ((fun x : Fin n => x - 1)^[k] v)
              ((fun x : Fin n => x - 1)^[k] v - 1) :=
            cycleHypergraph_dist_triangle hn v _ _
      _ ≤ k + 1 := by rw [h_dist_step]; exact Nat.add_le_add_right ih 1

/-- **Value of iterated successor on `Fin n`**: `((· + 1)^[k] v).val = (v.val + k) % n`.
Useful for distinctness reasoning: two iterates are equal iff their offsets
agree modulo `n`. -/
theorem cycleHypergraph_iterSucc_val {n : Nat} [NeZero n] (v : Fin n) :
    ∀ (k : ℕ), ((fun x : Fin n => x + 1)^[k] v).val = (v.val + k) % n := by
  intro k
  induction k with
  | zero =>
    simp
    exact (Nat.mod_eq_of_lt v.isLt).symm
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    show ((fun x : Fin n => x + 1)^[k] v + 1).val = (v.val + (k + 1)) % n
    rw [Fin.val_add, ih]
    have h1 : (1 : Fin n).val = 1 % n := rfl
    rw [h1, ← Nat.add_mod, Nat.add_assoc]

/-- **Injectivity of iterated successor on small range**: for `n ≥ 2` and
`i, j ≤ r` with `2r + 1 ≤ n`, `F^[i] v = F^[j] v ↔ i = j`. Forward shifts
don't wrap back onto themselves within the admissible range. -/
theorem cycleHypergraph_iterSucc_injOn {n : Nat} [NeZero n] (v : Fin n)
    {r i j : ℕ} (hir : i ≤ r) (hjr : j ≤ r) (hr : 2 * r + 1 ≤ n)
    (h : (fun x : Fin n => x + 1)^[i] v = (fun x : Fin n => x + 1)^[j] v) :
    i = j := by
  have h_val := congrArg Fin.val h
  rw [cycleHypergraph_iterSucc_val v i, cycleHypergraph_iterSucc_val v j] at h_val
  -- h_val: (v.val + i) % n = (v.val + j) % n
  have h_modeq : v.val + i ≡ v.val + j [MOD n] := h_val
  have hij_modeq : i ≡ j [MOD n] := Nat.ModEq.add_left_cancel' v.val h_modeq
  have hi_lt : i < n := by omega
  have hj_lt : j < n := by omega
  unfold Nat.ModEq at hij_modeq
  rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt] at hij_modeq
  exact hij_modeq

/-- **Value of iterated predecessor on `Fin n`**: `((· - 1)^[k] v).val = (v.val + (n - 1) * k) % n`
for `n ≥ 2`. Used analogously to `cycleHypergraph_iterSucc_val` for distinctness
reasoning on the backward-shift family. -/
theorem cycleHypergraph_iterPred_val {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n) : ∀ (k : ℕ),
    ((fun x : Fin n => x - 1)^[k] v).val = (v.val + (n - 1) * k) % n := by
  intro k
  induction k with
  | zero =>
    simp
    exact (Nat.mod_eq_of_lt v.isLt).symm
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    show ((fun x : Fin n => x - 1)^[k] v - 1).val = (v.val + (n - 1) * (k + 1)) % n
    rw [Fin.sub_def, ih]
    have h1 : (1 : Fin n).val = 1 := by
      show 1 % n = 1; exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    show (n - 1 + (v.val + (n - 1) * k) % n) % n = (v.val + (n - 1) * (k + 1)) % n
    have hmod : ((n - 1) % n) = n - 1 := Nat.mod_eq_of_lt (by omega)
    rw [show (n - 1 + (v.val + (n - 1) * k) % n : ℕ)
        = ((n - 1) % n + (v.val + (n - 1) * k) % n) from by rw [hmod]]
    rw [← Nat.add_mod]
    congr 1
    ring

/-- **Conjugation identity**: `(· - 1)^[k] v = -((· + 1)^[k] (-v))` in `Fin n`.
This lets us derive `iterPred_injOn` from `iterSucc_injOn` via a negation
conjugation. -/
private theorem cycleHypergraph_iterPred_neg_iterSucc {n : Nat} [NeZero n]
    (w : Fin n) : ∀ (k : ℕ),
    (fun x : Fin n => x - 1)^[k] w = -((fun x : Fin n => x + 1)^[k] (-w)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih]
    rw [Function.iterate_succ', Function.comp_apply]
    show -((fun x : Fin n => x + 1)^[k] (-w)) - 1 = -((fun x : Fin n => x + 1)^[k] (-w) + 1)
    abel

/-- **Forward and backward shift families don't overlap in the admissible range.**
For `n ≥ 2`, `i ≤ r`, `1 ≤ j ≤ r`, and `2r + 1 ≤ n`:
`F^[i] v ≠ G^[j] v`. The proof uses `.val` closed forms plus the fact that
`i + j ∈ [1, 2r]` with `2r < n` rules out the wrap-around collision. -/
theorem cycleHypergraph_iterSucc_ne_iterPred {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n) {r i j : ℕ} (hir : i ≤ r) (hj_pos : 1 ≤ j) (hjr : j ≤ r)
    (hr : 2 * r + 1 ≤ n) :
    (fun x : Fin n => x + 1)^[i] v ≠ (fun x : Fin n => x - 1)^[j] v := by
  intro h
  have h_val := congrArg Fin.val h
  rw [cycleHypergraph_iterSucc_val, cycleHypergraph_iterPred_val hn] at h_val
  have h_modeq : v.val + i ≡ v.val + (n - 1) * j [MOD n] := h_val
  have hij_modeq : i ≡ (n - 1) * j [MOD n] :=
    Nat.ModEq.add_left_cancel' v.val h_modeq
  have h_plus : i + j ≡ (n - 1) * j + j [MOD n] := Nat.ModEq.add_right j hij_modeq
  have hnj : (n - 1) * j + j = n * j := by
    rw [show n * j = (n - 1 + 1) * j from by congr 1; omega]
    rw [Nat.add_mul, Nat.one_mul]
  have h_zero : (n - 1) * j + j ≡ 0 [MOD n] := by
    unfold Nat.ModEq; rw [hnj]; simp [Nat.mul_mod_right]
  have h_sum : i + j ≡ 0 [MOD n] := h_plus.trans h_zero
  have h_lt : i + j < n := by omega
  unfold Nat.ModEq at h_sum
  rw [Nat.mod_eq_of_lt h_lt, Nat.zero_mod] at h_sum
  omega

/-- **Injectivity of iterated predecessor on small range**: symmetric
counterpart of `cycleHypergraph_iterSucc_injOn`, derived via the
conjugation `G^[k] v = -(F^[k] (-v))`. -/
theorem cycleHypergraph_iterPred_injOn {n : Nat} [NeZero n] (v : Fin n)
    {r i j : ℕ} (hir : i ≤ r) (hjr : j ≤ r) (hr : 2 * r + 1 ≤ n)
    (h : (fun x : Fin n => x - 1)^[i] v = (fun x : Fin n => x - 1)^[j] v) :
    i = j := by
  rw [cycleHypergraph_iterPred_neg_iterSucc v i,
      cycleHypergraph_iterPred_neg_iterSucc v j] at h
  have h' : (fun x : Fin n => x + 1)^[i] (-v) = (fun x : Fin n => x + 1)^[j] (-v) :=
    neg_injective h
  exact cycleHypergraph_iterSucc_injOn (-v) hir hjr hr h'

/-- **Forward-shift lower bound for ball volume**: for `n ≥ 2` and
`2r + 1 ≤ n`, `V(v, r) ≥ r + 1`. Exhibits the `r + 1` forward iterates
`F^[0] v, F^[1] v, ..., F^[r] v` as distinct ball members. This is the
one-sided (forward only) half of the general `V(v, r) ≥ 2r + 1` claim;
the backward half doubles it with `G^[1] v, ..., G^[r] v`. -/
theorem cycleHypergraph_ballVolume_forward_ge {n : Nat} [NeZero n]
    (hn : 2 ≤ n) {r : ℕ} (hr : 2 * r + 1 ≤ n) (v : Fin n) :
    r + 1 ≤ (cycleHypergraph n).geodesicBallVolume v r := by
  -- Shift family f^[k] v for k ∈ [0, r]
  let F : ℕ → Fin n := fun k => (fun x : Fin n => x + 1)^[k] v
  -- Finset of shifts
  let S : Finset (Fin n) := (Finset.range (r + 1)).image F
  -- S ⊆ ball(v, r)
  have h_in_ball : S ⊆ (cycleHypergraph n).geodesicBall v r := by
    intro u hu
    simp only [S, Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨k, hk, hku⟩ := hu
    subst hku
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (cycleHypergraph n).dist v ((fun x : Fin n => x + 1)^[k] v) ≤ r
    have h_le_k := cycleHypergraph_dist_iterSucc_le hn v k
    omega
  -- card S = r + 1 via injectivity
  have h_card : S.card = r + 1 := by
    show ((Finset.range (r + 1)).image F).card = r + 1
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range _
    · intros i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      exact cycleHypergraph_iterSucc_injOn v (by omega : i ≤ r) (by omega : j ≤ r) hr hij
  -- Conclude
  unfold Hypergraph.geodesicBallVolume
  calc r + 1 = S.card := h_card.symm
    _ ≤ _ := Finset.card_le_card h_in_ball

/-- **General ID6 lower bound**: `V(v, r) ≥ 2r + 1` on `cycleHypergraph n`
for every `n ≥ 2` and `r` with `2r + 1 ≤ n`.

Builds the `2r + 1` distinct vertices as
  `{F^[0] v, F^[1] v, ..., F^[r] v} ∪ {G^[1] v, G^[2] v, ..., G^[r] v}`
(forward shifts on the left, backward on the right, both using the single
step-by-1 adjacency on the cycle). Each iterate lies in `ball(v, r)` by
`cycleHypergraph_dist_iter{Succ,Pred}_le`; pairwise distinctness uses
`iterSucc_injOn`, `iterPred_injOn`, and `iterSucc_ne_iterPred`.

Combined with `cycleHypergraph_ballVolume_one_exact`, `_zero_exact`,
`_two_exact`, this recovers the `V(v, r) = 2r + 1` pattern for every
admissible base case and advances ID6 toward closure. The matching
upper bound `V(v, r) ≤ 2r + 1` requires the general shortest-walk
structural analysis and remains open in this form. -/
theorem cycleHypergraph_ballVolume_ge {n : Nat} [NeZero n]
    (hn : 2 ≤ n) {r : ℕ} (hr : 2 * r + 1 ≤ n) (v : Fin n) :
    2 * r + 1 ≤ (cycleHypergraph n).geodesicBallVolume v r := by
  let F : ℕ → Fin n := fun k => (fun x : Fin n => x + 1)^[k] v
  let G : ℕ → Fin n := fun k => (fun x : Fin n => x - 1)^[k] v
  let S1 : Finset (Fin n) := (Finset.range (r + 1)).image F
  let S2 : Finset (Fin n) := (Finset.Ioc 0 r).image G
  -- Cardinalities
  have hcard1 : S1.card = r + 1 := by
    show ((Finset.range (r + 1)).image F).card = r + 1
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range _
    · intros i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      exact cycleHypergraph_iterSucc_injOn v (by omega : i ≤ r) (by omega : j ≤ r) hr hij
  have hcard2 : S2.card = r := by
    show ((Finset.Ioc 0 r).image G).card = r
    rw [Finset.card_image_of_injOn]
    · rw [Nat.card_Ioc]; omega
    · intros i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_Ioc] at hi hj
      exact cycleHypergraph_iterPred_injOn v hi.2 hj.2 hr hij
  -- Disjointness
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_iff_ne]
    intros a ha b hb
    rw [show S1 = (Finset.range (r + 1)).image F from rfl] at ha
    rw [show S2 = (Finset.Ioc 0 r).image G from rfl] at hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨i, hi, hia⟩ := ha
    obtain ⟨j, hj, hjb⟩ := hb
    subst hia; subst hjb
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ioc] at hj
    exact cycleHypergraph_iterSucc_ne_iterPred hn v
      (by omega : i ≤ r) hj.1 hj.2 hr
  -- Union contained in ball
  have h_in_ball : (S1 ∪ S2) ⊆ (cycleHypergraph n).geodesicBall v r := by
    intro u hu
    rw [Finset.mem_union] at hu
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hu with h1 | h2
    · rw [show S1 = (Finset.range (r + 1)).image F from rfl, Finset.mem_image] at h1
      obtain ⟨i, hi, hiu⟩ := h1
      subst hiu
      rw [Finset.mem_range] at hi
      show (cycleHypergraph n).dist v ((fun x : Fin n => x + 1)^[i] v) ≤ r
      have := cycleHypergraph_dist_iterSucc_le hn v i
      omega
    · rw [show S2 = (Finset.Ioc 0 r).image G from rfl, Finset.mem_image] at h2
      obtain ⟨j, hj, hjv⟩ := h2
      subst hjv
      rw [Finset.mem_Ioc] at hj
      show (cycleHypergraph n).dist v ((fun x : Fin n => x - 1)^[j] v) ≤ r
      have := cycleHypergraph_dist_iterPred_le hn v j
      omega
  unfold Hypergraph.geodesicBallVolume
  calc 2 * r + 1 = (r + 1) + r := by ring
    _ = S1.card + S2.card := by rw [hcard1, hcard2]
    _ = (S1 ∪ S2).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ _ := Finset.card_le_card h_in_ball

/-- **Exact ball volume at radius 1** on `cycleHypergraph n` for `n ≥ 3`:
`geodesicBallVolume v 1 = 3`. Combined with `_one_ge_three` for the
lower bound and a direct upper bound from `dist ≤ 1 ⇒ Adj ∨ =`. -/
theorem cycleHypergraph_ballVolume_one_exact {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 1 = 3 := by
  have hn2 : 2 ≤ n := by omega
  refine le_antisymm ?_ (cycleHypergraph_ballVolume_one_ge_three hn v)
  -- Upper bound: ball v 1 ⊆ {v, v+1, v-1}.
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  have h_subset : (Finset.univ.filter
      (fun u => (cycleHypergraph n).dist v u ≤ 1)) ⊆
      ({v, v + 1, v - 1} : Finset (Fin n)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨_, h_dist⟩ := hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    -- h_dist: dist v u ≤ 1. So u = v (dist 0) or Adj v u (dist 1).
    rw [Nat.le_one_iff_eq_zero_or_eq_one] at h_dist
    rcases h_dist with h0 | h1
    · -- dist = 0 implies u = v (connected graph, else junk value).
      left
      unfold Hypergraph.dist at h0
      have hreach : (cycleHypergraph n).toSimpleGraph.Reachable v u := by
        exact (cycleHypergraph_connected hn2).preconnected v u
      have := (SimpleGraph.Reachable.dist_eq_zero_iff hreach).mp h0
      exact this.symm
    · -- dist = 1 implies Adj v u.
      unfold Hypergraph.dist at h1
      have hadj : (cycleHypergraph n).toSimpleGraph.Adj v u :=
        SimpleGraph.dist_eq_one_iff_adj.mp h1
      have := (cycleHypergraph_Adj_iff hn2 v u).mp hadj
      obtain ⟨_, hor⟩ := this
      rcases hor with hsucc | hpred
      · right; left; exact hsucc
      · right; right
        have : u = v - 1 := by
          have : v - 1 = (v + 1) - 1 - 1 := by abel
          have h2 : u = v + 1 - 1 - 1 := by
            have : u + 1 = v := hpred.symm
            have hu : u = v - 1 := by
              have : (u + 1) - 1 = v - 1 := by rw [this]
              simpa using this
            rw [hu]; abel
          rw [h2]; abel
        exact this
  calc (Finset.univ.filter
          (fun u => (cycleHypergraph n).dist v u ≤ 1)).card
      ≤ ({v, v + 1, v - 1} : Finset (Fin n)).card := Finset.card_le_card h_subset
    _ ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine Nat.succ_le_succ ?_
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp

/-! ## Five-vertex distinctness on `Fin n` for `n ≥ 5`

The five shift-offsets `0, 1, -1, 2, -2` are pairwise distinct in
`Fin n` when `n ≥ 5`. This drives `V(v, 2) ≥ 5` on cycleHypergraph. -/

/-- **Offset shift is left-cancellable in `Fin n`** (since `Fin n` with
`NeZero n` is an `AddCommGroup`). -/
private lemma fin_add_ne_of_ne {n : Nat} [NeZero n] (v : Fin n) {a b : Fin n}
    (hab : a ≠ b) : v + a ≠ v + b := by
  intro h
  exact hab (add_left_cancel h)

/-- **Value of `(1 : Fin n)` for `n ≥ 2`**. -/
private lemma fin_val_one {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (1 : Fin n).val = 1 := by
  show 1 % n = 1; exact Nat.mod_eq_of_lt (by omega)

/-- **Value of `(2 : Fin n)` for `n ≥ 3`**. -/
private lemma fin_val_two {n : Nat} [NeZero n] (hn : 3 ≤ n) :
    (2 : Fin n).val = 2 := by
  show 2 % n = 2; exact Nat.mod_eq_of_lt (by omega)

/-- **Value of `(-1 : Fin n)` for `n ≥ 2`**: equals `n - 1`. -/
private lemma fin_val_neg_one {n : Nat} [NeZero n] (hn : 2 ≤ n) :
    (-1 : Fin n).val = n - 1 := by
  have h1 : (1 : Fin n).val = 1 := fin_val_one hn
  rw [Fin.val_neg']
  rw [h1]
  exact Nat.mod_eq_of_lt (by omega)

/-- **Value of `(-2 : Fin n)` for `n ≥ 3`**: equals `n - 2`. -/
private lemma fin_val_neg_two {n : Nat} [NeZero n] (hn : 3 ≤ n) :
    (-2 : Fin n).val = n - 2 := by
  have h2 : (2 : Fin n).val = 2 := fin_val_two hn
  rw [Fin.val_neg']
  rw [h2]
  exact Nat.mod_eq_of_lt (by omega)

/-- **`(v + 2 : Fin n) ≠ (v - 2 : Fin n)` for `n ≥ 5`.** Differ by 4 in
Fin n, and 4 < n. -/
theorem cycle_add_two_ne_sub_two {n : Nat} [NeZero n] (hn : 5 ≤ n) (v : Fin n) :
    (v + 2 : Fin n) ≠ (v - 2 : Fin n) := by
  have h3 : 3 ≤ n := by omega
  intro h
  rw [sub_eq_add_neg] at h
  have h2eq : (2 : Fin n) = -(2 : Fin n) := add_left_cancel h
  have hv : (2 : Fin n).val = (-(2 : Fin n)).val := congrArg Fin.val h2eq
  rw [fin_val_two h3, show (-(2 : Fin n)).val = n - 2 from fin_val_neg_two h3] at hv
  omega

/-- **`(v + 1 : Fin n) ≠ (v - 2 : Fin n)` for `n ≥ 4`.** Differ by 3 in
Fin n. -/
theorem cycle_succ_ne_sub_two {n : Nat} [NeZero n] (hn : 4 ≤ n) (v : Fin n) :
    (v + 1 : Fin n) ≠ (v - 2 : Fin n) := by
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  intro h
  rw [sub_eq_add_neg] at h
  have h2eq : (1 : Fin n) = -(2 : Fin n) := add_left_cancel h
  have hv : (1 : Fin n).val = (-(2 : Fin n)).val := congrArg Fin.val h2eq
  rw [fin_val_one h2, show (-(2 : Fin n)).val = n - 2 from fin_val_neg_two h3] at hv
  omega

/-- **`(v - 1 : Fin n) ≠ (v + 2 : Fin n)` for `n ≥ 4`.** Symmetric of
`cycle_succ_ne_sub_two`. -/
theorem cycle_pred_ne_add_two {n : Nat} [NeZero n] (hn : 4 ≤ n) (v : Fin n) :
    (v - 1 : Fin n) ≠ (v + 2 : Fin n) := by
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  intro h
  rw [sub_eq_add_neg] at h
  have h2eq : -(1 : Fin n) = (2 : Fin n) := add_left_cancel h
  have hv : (-(1 : Fin n)).val = (2 : Fin n).val := congrArg Fin.val h2eq
  rw [show (-(1 : Fin n)).val = n - 1 from fin_val_neg_one h2, fin_val_two h3] at hv
  omega

/-- **`(v + 1 : Fin n) ≠ (v + 2 : Fin n)` for `n ≥ 2`.** Directly from
`cycle_succ_ne` applied at `v + 1`. -/
theorem cycle_succ_ne_add_two {n : Nat} [NeZero n] (hn : 2 ≤ n) (v : Fin n) :
    (v + 1 : Fin n) ≠ (v + 2 : Fin n) := by
  intro heq
  have h := cycle_succ_ne hn (v + 1)
  apply h
  rw [cycle_add_one_one_eq_add_two]
  exact heq.symm

/-- **`(v - 1 : Fin n) ≠ (v - 2 : Fin n)` for `n ≥ 3`.** Reduce via left
cancellation to `(-1 : Fin n) ≠ (-2 : Fin n)`, then compare `.val`. -/
theorem cycle_pred_ne_sub_two {n : Nat} [NeZero n] (hn : 3 ≤ n) (v : Fin n) :
    (v - 1 : Fin n) ≠ (v - 2 : Fin n) := by
  have h2 : 2 ≤ n := by omega
  intro heq
  have h1 : -(1 : Fin n) = -(2 : Fin n) := by
    have h' : v + (-(1 : Fin n)) = v + (-(2 : Fin n)) := by
      rw [← sub_eq_add_neg, ← sub_eq_add_neg]; exact heq
    exact add_left_cancel h'
  have h12 : (1 : Fin n) = (2 : Fin n) := neg_injective h1
  have hv : (1 : Fin n).val = (2 : Fin n).val := congrArg Fin.val h12
  rw [fin_val_one h2, fin_val_two hn] at hv
  omega

/-- **Radius-2 ball volume on `cycleHypergraph n` is `≥ 5` for `n ≥ 5`.**
Exhibits five distinct vertices `v, v + 1, v - 1, v + 2, v - 2` all within
distance 2 of `v`. This advances ID6 past the `r = 1` base case toward
the general `V(v, r) = 2r + 1` claim on cycles. -/
theorem cycleHypergraph_ballVolume_two_ge_five {n : Nat} [NeZero n]
    (hn : 5 ≤ n) (v : Fin n) :
    5 ≤ (cycleHypergraph n).geodesicBallVolume v 2 := by
  have h4 : 4 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  -- Ball membership facts
  have ⟨hadj_succ, hadj_pred⟩ := cycleHypergraph_succ_pred_adj h2 v
  have hadj_succ2 := cycleHypergraph_succ_succ_adj h2 v
  have hadj_pred2 := cycleHypergraph_pred_pred_adj h2 v
  have h_self_in : v ∈ (cycleHypergraph n).geodesicBall v 2 :=
    Hypergraph.self_mem_geodesicBall _ _ _
  have h_succ_in : v + 1 ∈ (cycleHypergraph n).geodesicBall v 2 := by
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Hypergraph.dist
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj_succ]
    omega
  have h_pred_in : v - 1 ∈ (cycleHypergraph n).geodesicBall v 2 := by
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Hypergraph.dist
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj_pred]
    omega
  have h_succ2_in : v + 2 ∈ (cycleHypergraph n).geodesicBall v 2 := by
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact cycleHypergraph_dist_add_two_le h2 v
  have h_pred2_in : v - 2 ∈ (cycleHypergraph n).geodesicBall v 2 := by
    unfold Hypergraph.geodesicBall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact cycleHypergraph_dist_sub_two_le h2 v
  -- Distinctness facts
  have hne_01 : v ≠ v + 1 := Ne.symm (cycle_succ_ne h2 v)
  have hne_0m1 : v ≠ v - 1 := by
    intro heq
    have h_ : v = v - 1 + 1 := by abel
    rw [← heq] at h_
    exact cycle_succ_ne h2 v h_.symm
  have hne_02 : v ≠ v + 2 := Ne.symm (cycle_add_two_ne_self h3 v)
  have hne_0m2 : v ≠ v - 2 := Ne.symm (cycle_sub_two_ne_self h3 v)
  have hne_1m1 : v + 1 ≠ v - 1 := cycle_succ_ne_pred h3 v
  have hne_12 : v + 1 ≠ v + 2 := cycle_succ_ne_add_two h2 v
  have hne_1m2 : v + 1 ≠ v - 2 := cycle_succ_ne_sub_two h4 v
  have hne_m12 : v - 1 ≠ v + 2 := cycle_pred_ne_add_two h4 v
  have hne_m1m2 : v - 1 ≠ v - 2 := cycle_pred_ne_sub_two h3 v
  have hne_2m2 : v + 2 ≠ v - 2 := cycle_add_two_ne_sub_two hn v
  -- Finset.card = 5
  have h_card : ({v, v + 1, v - 1, v + 2, v - 2} : Finset (Fin n)).card = 5 := by
    rw [show ({v, v + 1, v - 1, v + 2, v - 2} : Finset (Fin n))
        = insert v (insert (v + 1) (insert (v - 1) (insert (v + 2) {v - 2}))) from rfl]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · -- (v+2) ∉ {v-2}
      rw [Finset.mem_singleton]; exact hne_2m2
    · -- (v-1) ∉ {v+2, v-2}
      rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hne_m12, hne_m1m2⟩
    · -- (v+1) ∉ {v-1, v+2, v-2}
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hne_1m1, hne_12, hne_1m2⟩
    · -- v ∉ {v+1, v-1, v+2, v-2}
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hne_01, hne_0m1, hne_02, hne_0m2⟩
  -- Subset into the ball
  have h_subset :
      ({v, v + 1, v - 1, v + 2, v - 2} : Finset (Fin n)) ⊆
      (cycleHypergraph n).geodesicBall v 2 := by
    intros u hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact h_self_in
    · exact h_succ_in
    · exact h_pred_in
    · exact h_succ2_in
    · exact h_pred2_in
  unfold Hypergraph.geodesicBallVolume
  calc 5 = ({v, v + 1, v - 1, v + 2, v - 2} : Finset (Fin n)).card := h_card.symm
    _ ≤ _ := Finset.card_le_card h_subset

/-- **Radius-2 ball volume on `cycleHypergraph n` is `≤ 5` for `n ≥ 5`.**
Every `u` with `dist v u ≤ 2` arises from a shortest walk of length 0, 1,
or 2. Length 0 gives `u = v`; length 1 gives `u ∈ {v ± 1}`; length 2 pins
the intermediate vertex `w ∈ {v ± 1}` via `cycleHypergraph_Adj_iff`, and
then `u ∈ N(w) = {w ± 1} = {v, v ± 2}`. Combined with `u ≠ v`, this puts
`u ∈ {v, v ± 1, v ± 2}`. -/
theorem cycleHypergraph_ballVolume_two_le_five {n : Nat} [NeZero n]
    (hn : 3 ≤ n) (v : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 2 ≤ 5 := by
  have hn2 : 2 ≤ n := by omega
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  have h_subset : (Finset.univ.filter
      (fun u : Fin n => (cycleHypergraph n).dist v u ≤ 2)) ⊆
      ({v, v + 1, v - 1, v + 2, v - 2} : Finset (Fin n)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨_, h_dist⟩ := hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton]
    -- Extract minimal walk
    have hreach : (cycleHypergraph n).toSimpleGraph.Reachable v u :=
      (cycleHypergraph_connected hn2).preconnected v u
    obtain ⟨p, hp_len⟩ := hreach.exists_walk_length_eq_dist
    have hp_le : p.length ≤ 2 := by
      unfold Hypergraph.dist at h_dist
      exact hp_len ▸ h_dist
    -- Case on p.length ∈ {0, 1, 2}
    have hpl_cases : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by omega
    rcases hpl_cases with hpl | hpl | hpl
    · -- length 0: u = v
      left
      have h0 := p.getVert_zero
      have h2 := p.getVert_length
      rw [hpl] at h2
      rw [h0] at h2
      exact h2.symm
    · -- length 1: adj v u
      have hadj : (cycleHypergraph n).toSimpleGraph.Adj v u := by
        have hlt : (0 : ℕ) < p.length := by rw [hpl]; exact Nat.zero_lt_one
        have h := p.adj_getVert_succ hlt
        rw [p.getVert_zero] at h
        have h2 : p.getVert (0 + 1) = u := by
          have := p.getVert_length
          rw [hpl] at this
          simpa using this
        rw [h2] at h
        exact h
      have := (cycleHypergraph_Adj_iff hn2 v u).mp hadj
      obtain ⟨_, hor⟩ := this
      rcases hor with hsucc | hpred
      · right; left; exact hsucc
      · right; right; left
        have h1 : u + 1 - 1 = v - 1 := by rw [hpred.symm]
        rw [add_sub_cancel_right] at h1
        exact h1
    · -- length 2: common-neighbor argument
      -- w = p.getVert 1 is adjacent to both v and u
      have hadj1 : (cycleHypergraph n).toSimpleGraph.Adj v (p.getVert 1) := by
        have hlt : (0 : ℕ) < p.length := by rw [hpl]; norm_num
        have h := p.adj_getVert_succ hlt
        rw [p.getVert_zero] at h
        exact h
      have hadj2 : (cycleHypergraph n).toSimpleGraph.Adj (p.getVert 1) u := by
        have hlt : (1 : ℕ) < p.length := by rw [hpl]; norm_num
        have h := p.adj_getVert_succ hlt
        have h2 : p.getVert (1 + 1) = u := by
          have := p.getVert_length
          rw [hpl] at this
          simpa using this
        rw [h2] at h
        exact h
      -- From Adj v w: w = v+1 or w = v-1
      have hvw_cases := (cycleHypergraph_Adj_iff hn2 v (p.getVert 1)).mp hadj1
      obtain ⟨_, h_vw_or⟩ := hvw_cases
      rcases h_vw_or with hw_eq | hw_eq
      · -- w = v + 1
        -- Adj w u: u = w+1 = v+2 or w = u+1 (u = w-1 = v)
        rw [hw_eq] at hadj2
        have hwu_cases := (cycleHypergraph_Adj_iff hn2 (v + 1) u).mp hadj2
        obtain ⟨_, h_wu_or⟩ := hwu_cases
        rcases h_wu_or with hu_eq | hv_eq
        · -- u = (v + 1) + 1 = v + 2
          right; right; right; left
          rw [hu_eq, cycle_add_one_one_eq_add_two]
        · -- v + 1 = u + 1, hence u = v
          left
          have : u + 1 - 1 = v + 1 - 1 := by rw [hv_eq]
          rw [add_sub_cancel_right, add_sub_cancel_right] at this
          exact this
      · -- v = w + 1, so w = v - 1
        -- hw_eq : v = (p.getVert 1) + 1
        have hw_eq2 : p.getVert 1 = v - 1 := by
          have h := hw_eq.symm
          have : (p.getVert 1) + 1 - 1 = v - 1 := by rw [h]
          rw [add_sub_cancel_right] at this
          exact this
        rw [hw_eq2] at hadj2
        -- Adj (v-1) u: u = (v-1)+1 = v, or v-1 = u+1
        have hwu_cases := (cycleHypergraph_Adj_iff hn2 (v - 1) u).mp hadj2
        obtain ⟨_, h_wu_or⟩ := hwu_cases
        rcases h_wu_or with hu_eq | hv_eq
        · -- u = (v - 1) + 1 = v
          left
          have : u = v := by
            have hrw : (v - 1 + 1 : Fin n) = v := by abel
            rw [hrw] at hu_eq
            exact hu_eq
          exact this
        · -- v - 1 = u + 1, so u = v - 2
          right; right; right; right
          have hu_eq : u = v - 2 := by
            -- v - 1 = u + 1 ⟹ u = v - 1 - 1 = v - 2
            have : v - 1 - 1 = u + 1 - 1 := by rw [hv_eq]
            rw [cycle_sub_one_one_eq_sub_two, add_sub_cancel_right] at this
            exact this.symm
          exact hu_eq
  calc (Finset.univ.filter
          (fun u : Fin n => (cycleHypergraph n).dist v u ≤ 2)).card
      ≤ ({v, v + 1, v - 1, v + 2, v - 2} : Finset (Fin n)).card :=
        Finset.card_le_card h_subset
    _ ≤ 5 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine Nat.succ_le_succ ?_
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine Nat.succ_le_succ ?_
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine Nat.succ_le_succ ?_
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp

/-- **Exact radius-2 ball volume `V(v, 2) = 5` on `cycleHypergraph n`
for `n ≥ 5`.** Combines the `≥ 5` lower bound (`_two_ge_five`) with the
`≤ 5` upper bound (`_two_le_five`). This closes the `r = 2` base case
for the `V(v, r) = 2r + 1` formula on cycles. -/
theorem cycleHypergraph_ballVolume_two_exact {n : Nat} [NeZero n]
    (hn : 5 ≤ n) (v : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 2 = 5 := by
  have h3 : 3 ≤ n := by omega
  exact le_antisymm (cycleHypergraph_ballVolume_two_le_five h3 v)
    (cycleHypergraph_ballVolume_two_ge_five hn v)

/-- **Large-radius ball covers everything on a connected cycle**: for
`n ≥ 2` and radius `r ≥ n`, the closed ball of radius `r` around any
vertex equals all of `Fin n`. Proof: on a connected finite graph,
`dist u v < card V = n`, so `dist ≤ n` always, and every vertex is in
the ball. -/
theorem cycleHypergraph_ballVolume_large {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v : Fin n) (r : ℕ) (hr : n ≤ r) :
    (cycleHypergraph n).geodesicBallVolume v r = n := by
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  -- On a connected cycle, every u has dist v u < n, hence ≤ n ≤ r.
  have h_univ : Finset.univ.filter
      (fun u : Fin n => (cycleHypergraph n).dist v u ≤ r)
      = Finset.univ := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- dist v u < n ≤ r.
    unfold Hypergraph.dist
    have hreach : (cycleHypergraph n).toSimpleGraph.Reachable v u :=
      (cycleHypergraph_connected hn).preconnected v u
    obtain ⟨p, hp_len⟩ := hreach.exists_walk_length_eq_dist
    have h_path := p.toPath
    have h_path_len : h_path.val.length < Fintype.card (Fin n) :=
      SimpleGraph.Walk.IsPath.length_lt h_path.prop
    have h_dist_le_path : (cycleHypergraph n).toSimpleGraph.dist v u
        ≤ h_path.val.length :=
      SimpleGraph.dist_le h_path.val
    have h_card : Fintype.card (Fin n) = n := Fintype.card_fin n
    have h_dist_lt : (cycleHypergraph n).toSimpleGraph.dist v u
        < Fintype.card (Fin n) :=
      lt_of_le_of_lt h_dist_le_path h_path_len
    rw [h_card] at h_dist_lt
    simp only [iff_true]
    exact Nat.le_of_lt (lt_of_lt_of_le h_dist_lt hr)
  rw [h_univ]
  simp

/-- **On a connected hypergraph, `V(v, r) = |V|` for `r ≥ |V|`.**
Generalises `cycleHypergraph_ballVolume_large` to every connected
hypergraph: once the radius exceeds the vertex count, every vertex is
within distance `r` (since finite paths have length < `|V|`). -/
theorem geodesicBallVolume_ge_card (H : Hypergraph V)
    (hconn : H.toSimpleGraph.Connected)
    (v : V) (r : ℕ) (hr : Fintype.card V ≤ r) :
    H.geodesicBallVolume v r = Fintype.card V := by
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  have h_univ : Finset.univ.filter
      (fun u : V => H.dist v u ≤ r) = Finset.univ := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Hypergraph.dist
    have hreach : H.toSimpleGraph.Reachable v u := hconn.preconnected v u
    obtain ⟨p, _hp_len⟩ := hreach.exists_walk_length_eq_dist
    have h_path := p.toPath
    have h_path_len : h_path.val.length < Fintype.card V :=
      SimpleGraph.Walk.IsPath.length_lt h_path.prop
    have h_dist_le_path : H.toSimpleGraph.dist v u ≤ h_path.val.length :=
      SimpleGraph.dist_le h_path.val
    have h_dist_lt : H.toSimpleGraph.dist v u < Fintype.card V :=
      lt_of_le_of_lt h_dist_le_path h_path_len
    simp only [iff_true]
    exact Nat.le_of_lt (lt_of_lt_of_le h_dist_lt hr)
  rw [h_univ]
  simp

/-- **Ball volume at radius 0 on the cycle** `= 1`: only the basepoint
itself is within distance 0 (cycle is connected, so `dist = 0 ↔ u = v`).
This is the `r = 0` case of the ID6 dimension-compatibility formula
`geodesicBallVolume v r = 2r + 1`. -/
theorem cycleHypergraph_ballVolume_zero_exact {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (v : Fin n) :
    (cycleHypergraph n).geodesicBallVolume v 0 = 1 := by
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  -- {u : dist v u ≤ 0} = {u : dist v u = 0} = {v} on a connected graph.
  have h_eq : (Finset.univ.filter
      (fun u : Fin n => (cycleHypergraph n).dist v u ≤ 0)) = {v} := by
    ext u
    rw [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, h_dist⟩
      -- dist ≤ 0 ↔ dist = 0.
      have h0 : (cycleHypergraph n).dist v u = 0 := Nat.le_zero.mp h_dist
      unfold Hypergraph.dist at h0
      have hreach : (cycleHypergraph n).toSimpleGraph.Reachable v u :=
        (cycleHypergraph_connected hn).preconnected v u
      exact ((SimpleGraph.Reachable.dist_eq_zero_iff hreach).mp h0).symm
    · rintro rfl
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Hypergraph.dist_self]
  rw [h_eq]
  simp

end InfraFormalization
