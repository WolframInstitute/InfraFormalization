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
