/-
Evolutions with hyperedge identities and their causal graph.

A `History` lists the identities of the initial hyperedges and, for each
event `k < n`, the identities it consumes (`ins`) and creates (`outs`).
Events are applied one at a time in the order `0, 1, ..., n-1`; any update
order of a rewriting evolution is such a sequence. `History.Valid` requires
every consumed identity to be live and every created identity to be new.
The causal graph has an edge `i → j` when event `j` consumes an identity
created by event `i`.

Results:

* `consumer_unique`: an identity is consumed by at most one event.
* `succ_card_le`: the out-degree of event `i` is at most `|outs i|`.
* `antichain_ins_sum_le`: for an antichain `A` of the causal order with
  strict down-set `D`, `∑_{a ∈ A} |ins a| + ∑_{d ∈ D} |ins d| ≤ |init| +
  ∑_{d ∈ D} |outs d|`. If `|ins k| = |outs k|` for every event,
  `∑_{a ∈ A} |ins a| ≤ |init|` (`antichain_ins_sum_le_init`).
* `ball_card_le`: if every event creates at most `m` identities, at most
  `(m + 1) ^ t` events lie within directed distance `t` of an event.

`RuleHistory r` attaches hyperedge labels and one binding per event, so
that each event is an application of `r` whose right-hand-side-only
vertices are new; `RuleHistory.state_step` shows that consecutive label
states are related by `Application.result`.
-/

import Mathlib
import InfraFormalization.Application
import InfraFormalization.CandidateRuleCatalog

namespace InfraFormalization
namespace CausalHistory

/-- One event: the hyperedge identities it consumes and creates. -/
structure Event where
  ins : Finset ℕ
  outs : Finset ℕ

/-- Initial identities, the number of events `n`, and the events `ev k`
for `k < n`. -/
structure History where
  init : Finset ℕ
  n : ℕ
  ev : ℕ → Event

namespace History

variable (h : History)

/-- Identities live after the first `k` events. -/
def live : ℕ → Finset ℕ
  | 0 => h.init
  | k + 1 => (live k \ (h.ev k).ins) ∪ (h.ev k).outs

/-- Identities that exist at some point among the first `k` events. -/
def seen : ℕ → Finset ℕ
  | 0 => h.init
  | k + 1 => seen k ∪ (h.ev k).outs

/-- Every consumed identity is live; every created identity is new. -/
structure Valid : Prop where
  ins_live : ∀ k < h.n, (h.ev k).ins ⊆ h.live k
  outs_fresh : ∀ k < h.n, Disjoint (h.ev k).outs (h.seen k)

/-- Causal edge `i → j`: event `j` consumes an identity created by
event `i`. -/
def edge (i j : ℕ) : Prop :=
  i < h.n ∧ j < h.n ∧ ((h.ev i).outs ∩ (h.ev j).ins).Nonempty

instance (i j : ℕ) : Decidable (h.edge i j) := by
  unfold edge; infer_instance

/-- The causal order: the transitive closure of `edge`. -/
def prec (i j : ℕ) : Prop := Relation.TransGen h.edge i j

variable {h}

theorem live_subset_seen : ∀ k, h.live k ⊆ h.seen k
  | 0 => fun _ hx => hx
  | k + 1 => by
    intro x hx
    simp only [live, Finset.mem_union, Finset.mem_sdiff] at hx
    simp only [seen, Finset.mem_union]
    rcases hx with ⟨hx, _⟩ | hx
    · exact Or.inl (live_subset_seen k hx)
    · exact Or.inr hx

theorem seen_mono {k l : ℕ} (hkl : k ≤ l) : h.seen k ⊆ h.seen l := by
  induction hkl with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem mem_seen_iff {x : ℕ} :
    ∀ k, x ∈ h.seen k ↔ x ∈ h.init ∨ ∃ i < k, x ∈ (h.ev i).outs
  | 0 => by simp [seen]
  | k + 1 => by
    rw [seen, Finset.mem_union, mem_seen_iff k]
    constructor
    · rintro ((hx | ⟨i, hi, hx⟩) | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨i, by omega, hx⟩
      · exact Or.inr ⟨k, by omega, hx⟩
    · rintro (hx | ⟨i, hi, hx⟩)
      · exact Or.inl (Or.inl hx)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact Or.inl (Or.inr ⟨i, hi, hx⟩)
        · exact Or.inr hx

theorem mem_seen_of_outs {i k : ℕ} (hik : i < k) {x : ℕ}
    (hx : x ∈ (h.ev i).outs) : x ∈ h.seen k :=
  (mem_seen_iff k).2 (Or.inr ⟨i, hik, hx⟩)

/-- A created identity is not initial. -/
theorem not_mem_init_of_outs (hv : h.Valid) {i x : ℕ} (hi : i < h.n)
    (hx : x ∈ (h.ev i).outs) : x ∉ h.init := fun h0 =>
  Finset.disjoint_left.1 (hv.outs_fresh i hi) hx
    (seen_mono (Nat.zero_le i) (by simpa [seen] using h0))

/-- An identity is created by at most one event. -/
theorem producer_unique (hv : h.Valid) {i j x : ℕ} (hi : i < h.n) (hj : j < h.n)
    (hxi : x ∈ (h.ev i).outs) (hxj : x ∈ (h.ev j).outs) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · exact Finset.disjoint_left.1 (hv.outs_fresh j hj) hxj (mem_seen_of_outs hij hxi)
  · exact Finset.disjoint_left.1 (hv.outs_fresh i hi) hxi (mem_seen_of_outs hji hxj)

/-- An identity consumed by event `i` is not live after event `i`. -/
theorem not_mem_live_of_ins (hv : h.Valid) {i x : ℕ} (hi : i < h.n)
    (hx : x ∈ (h.ev i).ins) : ∀ k, i < k → k ≤ h.n → x ∉ h.live k := by
  intro k hik hkn
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [live, Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not]
    refine ⟨fun hl => ?_, fun ho => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hik with hlt | rfl
      · exact absurd hl (ih hlt (by omega))
      · exact hx
    · have hseen : x ∈ h.seen k :=
        seen_mono (by omega) (live_subset_seen i (hv.ins_live i hi hx))
      exact absurd hseen (Finset.disjoint_left.1 (hv.outs_fresh k (by omega)) ho)

/-- An identity is consumed by at most one event. -/
theorem consumer_unique (hv : h.Valid) {i j x : ℕ} (hi : i < h.n) (hj : j < h.n)
    (hxi : x ∈ (h.ev i).ins) (hxj : x ∈ (h.ev j).ins) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · exact not_mem_live_of_ins hv hi hxi j hij hj.le (hv.ins_live j hj hxj)
  · exact not_mem_live_of_ins hv hj hxj i hji hi.le (hv.ins_live i hi hxi)

/-- A consumed identity is initial or created by an earlier event. -/
theorem ins_source (hv : h.Valid) {j x : ℕ} (hj : j < h.n) (hx : x ∈ (h.ev j).ins) :
    x ∈ h.init ∨ ∃ i < j, x ∈ (h.ev i).outs :=
  (mem_seen_iff j).1 (live_subset_seen j (hv.ins_live j hj hx))

/-- Causal edges go forward in event order. -/
theorem edge_lt (hv : h.Valid) {i j : ℕ} (he : h.edge i j) : i < j := by
  obtain ⟨hi, hj, x, hx⟩ := he
  rw [Finset.mem_inter] at hx
  rcases ins_source hv hj hx.2 with h0 | ⟨i', hi', hx'⟩
  · exact absurd h0 (not_mem_init_of_outs hv hi hx.1)
  · have := producer_unique hv hi (by omega) hx.1 hx'
    omega

theorem prec_lt (hv : h.Valid) {i j : ℕ} (hp : h.prec i j) : i < j := by
  induction hp with
  | single he => exact edge_lt hv he
  | tail _ he ih => exact ih.trans (edge_lt hv he)

theorem prec_irrefl (hv : h.Valid) (i : ℕ) : ¬ h.prec i i :=
  fun hp => lt_irrefl _ (prec_lt hv hp)

/-! ## Out-degree -/

/-- Causal successors of `i` among the events. -/
def succ (h : History) (i : ℕ) : Finset ℕ :=
  (Finset.range h.n).filter (h.edge i)

/-- The out-degree of event `i` is at most the number of identities it
creates. -/
theorem succ_card_le (hv : h.Valid) (i : ℕ) : (h.succ i).card ≤ (h.ev i).outs.card := by
  classical
  have key : ∀ j ∈ h.succ i, ((h.ev i).outs ∩ (h.ev j).ins).Nonempty := by
    intro j hj
    simp only [succ, Finset.mem_filter] at hj
    exact hj.2.2.2
  let f : ℕ → ℕ := fun j =>
    if hj : ((h.ev i).outs ∩ (h.ev j).ins).Nonempty then hj.choose else 0
  have hf : ∀ j ∈ h.succ i, f j ∈ (h.ev i).outs ∩ (h.ev j).ins := by
    intro j hj
    simp only [f, dif_pos (key j hj)]
    exact (key j hj).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    exact (Finset.mem_inter.1 (hf j hj)).1
  · intro j₁ hj₁ j₂ hj₂ heq
    have h1 := Finset.mem_inter.1 (hf j₁ hj₁)
    have h2 := Finset.mem_inter.1 (hf j₂ hj₂)
    have hn1 : j₁ < h.n := by simp [succ] at hj₁; exact hj₁.1
    have hn2 : j₂ < h.n := by simp [succ] at hj₂; exact hj₂.1
    rw [heq] at h1
    exact consumer_unique hv hn1 hn2 h1.2 h2.2

/-! ## Cone growth -/

/-- Events within directed distance `t` of event `i`. -/
def ball (h : History) (i : ℕ) : ℕ → Finset ℕ
  | 0 => {i}
  | t + 1 => ball h i t ∪ (ball h i t).biUnion h.succ

/-- If every event creates at most `m` identities, at most `(m+1)^t`
events lie within directed distance `t` of an event. -/
theorem ball_card_le (hv : h.Valid) {m : ℕ} (hm : ∀ k < h.n, (h.ev k).outs.card ≤ m)
    (i t : ℕ) : (h.ball i t).card ≤ (m + 1) ^ t := by
  induction t with
  | zero => simp [ball]
  | succ t ih =>
    have hs : ∀ j, (h.succ j).card ≤ m := by
      intro j
      by_cases hj : j < h.n
      · exact (succ_card_le hv j).trans (hm j hj)
      · have : h.succ j = ∅ := by
          ext k; simp [succ, edge, hj]
        simp [this]
    calc (h.ball i (t + 1)).card
        ≤ (h.ball i t).card + ((h.ball i t).biUnion h.succ).card := Finset.card_union_le _ _
      _ ≤ (h.ball i t).card + (h.ball i t).card * m := by
          gcongr
          exact Finset.card_biUnion_le_card_mul _ _ _ (fun j _ => hs j)
      _ = (h.ball i t).card * (m + 1) := by ring
      _ ≤ (m + 1) ^ t * (m + 1) := by gcongr
      _ = (m + 1) ^ (t + 1) := by ring

/-! ## Antichains -/

/-- `A` is a set of events no two of which are related by `prec`. -/
def IsAntichain (h : History) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, a < h.n) ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ h.prec a b

/-- The general counting bound. Let `D` be a set of events closed under
causal predecessors, and `A` a set of events outside `D` all of whose
causal predecessors lie in `D`. Then the identities consumed by `A`,
together with those consumed by `D`, are at most the initial identities
plus those created by `D`. -/
theorem ins_sum_le_of_downClosed (hv : h.Valid) (A D : Finset ℕ)
    (hAn : ∀ a ∈ A, a < h.n) (hDn : ∀ d ∈ D, d < h.n)
    (hD : ∀ d ∈ D, ∀ i, h.edge i d → i ∈ D)
    (hA : ∀ a ∈ A, ∀ i, h.edge i a → i ∈ D) (hAD : Disjoint A D) :
    ∑ a ∈ A, (h.ev a).ins.card + ∑ d ∈ D, (h.ev d).ins.card
      ≤ h.init.card + ∑ d ∈ D, (h.ev d).outs.card := by
  classical
  -- Identities available to `A ∪ D`: the initial ones and those created by `D`.
  set P : Finset ℕ := h.init ∪ D.biUnion (fun d => (h.ev d).outs) with hP
  have hsrc : ∀ e ∈ A ∪ D, (h.ev e).ins ⊆ P := by
    intro e he x hx
    have hen : e < h.n := by
      rcases Finset.mem_union.1 he with he | he
      · exact hAn e he
      · exact hDn e he
    rcases ins_source hv hen hx with h0 | ⟨i, hi, hxi⟩
    · exact Finset.mem_union_left _ h0
    · have hedge : h.edge i e := ⟨by omega, hen, x, Finset.mem_inter.2 ⟨hxi, hx⟩⟩
      have hiD : i ∈ D := by
        rcases Finset.mem_union.1 he with he | he
        · exact hA e he i hedge
        · exact hD e he i hedge
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hiD, hxi⟩)
  -- The consumed sets of distinct events are disjoint.
  have hdisj : ∀ e₁ ∈ A ∪ D, ∀ e₂ ∈ A ∪ D, e₁ ≠ e₂ →
      Disjoint (h.ev e₁).ins (h.ev e₂).ins := by
    intro e₁ h₁ e₂ h₂ hne
    have n₁ : e₁ < h.n := by
      rcases Finset.mem_union.1 h₁ with h | h
      · exact hAn _ h
      · exact hDn _ h
    have n₂ : e₂ < h.n := by
      rcases Finset.mem_union.1 h₂ with h | h
      · exact hAn _ h
      · exact hDn _ h
    exact Finset.disjoint_left.2 fun x hx₁ hx₂ => hne (consumer_unique hv n₁ n₂ hx₁ hx₂)
  have hcard : ((A ∪ D).biUnion fun e => (h.ev e).ins).card
      = ∑ e ∈ A ∪ D, (h.ev e).ins.card :=
    Finset.card_biUnion (fun e₁ h₁ e₂ h₂ hne => hdisj e₁ h₁ e₂ h₂ hne)
  have hsub : ((A ∪ D).biUnion fun e => (h.ev e).ins) ⊆ P :=
    Finset.biUnion_subset.2 hsrc
  have hPc : P.card ≤ h.init.card + ∑ d ∈ D, (h.ev d).outs.card :=
    (Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_biUnion_le)
  rw [← Finset.sum_union hAD, ← hcard]
  exact (Finset.card_le_card hsub).trans hPc

open Classical in
/-- The strict down-set of `A`: events that precede some element of `A`. -/
noncomputable def downSet (h : History) (A : Finset ℕ) : Finset ℕ :=
  (Finset.range h.n).filter (fun i => ∃ a ∈ A, h.prec i a)

/-- Antichain bound with the down-set correction. -/
theorem antichain_ins_sum_le (hv : h.Valid) {A : Finset ℕ} (hA : h.IsAntichain A) :
    ∑ a ∈ A, (h.ev a).ins.card + ∑ d ∈ h.downSet A, (h.ev d).ins.card
      ≤ h.init.card + ∑ d ∈ h.downSet A, (h.ev d).outs.card := by
  classical
  apply ins_sum_le_of_downClosed hv A (h.downSet A) hA.1
  · intro d hd; simp only [downSet, Finset.mem_filter, Finset.mem_range] at hd; exact hd.1
  · intro d hd i hi
    simp only [downSet, Finset.mem_filter, Finset.mem_range] at hd ⊢
    obtain ⟨_, a, ha, hda⟩ := hd
    exact ⟨hi.1, a, ha, Relation.TransGen.head hi hda⟩
  · intro a ha i hi
    simp only [downSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi.1, a, ha, Relation.TransGen.single hi⟩
  · refine Finset.disjoint_left.2 fun a ha hd => ?_
    simp only [downSet, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨_, b, hb, hab⟩ := hd
    by_cases hab' : a = b
    · subst hab'; exact prec_irrefl hv a hab
    · exact hA.2 a ha b hb hab' hab

/-- Antichain bound for histories whose events consume as many
identities as they create: the identities consumed by an antichain are
at most the initial identities. -/
theorem antichain_ins_sum_le_init (hv : h.Valid)
    (hcons : ∀ k < h.n, (h.ev k).ins.card = (h.ev k).outs.card)
    {A : Finset ℕ} (hA : h.IsAntichain A) :
    ∑ a ∈ A, (h.ev a).ins.card ≤ h.init.card := by
  have key := antichain_ins_sum_le hv hA
  have heq : ∑ d ∈ h.downSet A, (h.ev d).ins.card = ∑ d ∈ h.downSet A, (h.ev d).outs.card := by
    apply Finset.sum_congr rfl
    intro d hd
    simp only [downSet, Finset.mem_filter, Finset.mem_range] at hd
    exact hcons d hd.1
  omega

/-- If every event consumes exactly `m` identities and creates `m`, an
antichain has at most `|init| / m` events: `m * |A| ≤ |init|`. -/
theorem antichain_card_le (hv : h.Valid) {m : ℕ}
    (hin : ∀ k < h.n, (h.ev k).ins.card = m) (hout : ∀ k < h.n, (h.ev k).outs.card = m)
    {A : Finset ℕ} (hA : h.IsAntichain A) : m * A.card ≤ h.init.card := by
  have := antichain_ins_sum_le_init hv (fun k hk => (hin k hk).trans (hout k hk).symm) hA
  rwa [Finset.sum_congr rfl (fun a ha => hin a (hA.1 a ha)), Finset.sum_const,
    smul_eq_mul, mul_comm] at this

end History

/-! ## Histories of a rule -/

/-- A history whose events are applications of rule `r`: identities
carry hyperedge labels, and event `k` has a binding `ρ k` under which the
labels of its consumed and created identities are the images of the
left- and right-hand sides. -/
structure RuleHistory {P : Type*} (r : Rule P) (V : Type*) extends History where
  lab : ℕ → Hyperedge V
  ρ : ℕ → P → V
  ins_lab : ∀ k < n, (ev k).ins.val.map lab = r.lhs.edges.map (Hyperedge.map (ρ k))
  outs_lab : ∀ k < n, (ev k).outs.val.map lab = r.rhs.edges.map (Hyperedge.map (ρ k))
  /-- Right-hand-side-only pattern vertices are bound to vertices that
  occur in no hyperedge seen before the event. -/
  fresh : ∀ k < n, ∀ p : P, (∀ e ∈ r.lhs.edges, p ∉ e.verts) →
    ∀ x ∈ toHistory.seen k, ρ k p ∉ (lab x).verts
  /-- Distinct right-hand-side-only pattern vertices get distinct vertices. -/
  fresh_inj : ∀ k < n, ∀ p q : P, (∀ e ∈ r.lhs.edges, p ∉ e.verts) →
    (∀ e ∈ r.lhs.edges, q ∉ e.verts) → ρ k p = ρ k q → p = q

namespace RuleHistory

variable {P V : Type*} {r : Rule P} (h : RuleHistory r V)

/-- The hypergraph after the first `k` events: labels of the live
identities. -/
def state (k : ℕ) : Hypergraph V := ⟨(h.live k).val.map h.lab⟩

theorem ins_card {k : ℕ} (hk : k < h.n) : (h.ev k).ins.card = r.lhsSize := by
  have := congrArg Multiset.card (h.ins_lab k hk)
  simpa [Rule.lhsSize, Hypergraph.size] using this

theorem outs_card {k : ℕ} (hk : k < h.n) : (h.ev k).outs.card = r.rhsSize := by
  have := congrArg Multiset.card (h.outs_lab k hk)
  simpa [Rule.rhsSize, Hypergraph.size] using this

/-- Event `k` is an application of `r` to `state k` with binding `ρ k`,
and its result is `state (k+1)`. -/
theorem state_step [DecidableEq V] (hv : h.Valid) {k : ℕ} (hk : k < h.n) :
    ∃ a : Application r (h.state k), a.ρ = h.ρ k ∧ a.result = h.state (k + 1) := by
  classical
  have hsub : (h.ev k).ins ⊆ h.live k := hv.ins_live k hk
  have hle : (h.ev k).ins.val ≤ (h.live k).val := Finset.val_le_iff.2 hsub
  refine ⟨⟨h.ρ k, ?_⟩, rfl, ?_⟩
  · rw [← h.ins_lab k hk]
    exact Multiset.map_le_map hle
  · have hdisj : Disjoint (h.live k \ (h.ev k).ins) (h.ev k).outs :=
      Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_left (History.live_subset_seen k)
          (hv.outs_fresh k hk).symm)
    show Hypergraph.mk (((h.live k).val.map h.lab - r.lhs.edges.map (Hyperedge.map (h.ρ k)))
        + r.rhs.edges.map (Hyperedge.map (h.ρ k))) = ⟨(h.live (k + 1)).val.map h.lab⟩
    congr 1
    rw [← h.ins_lab k hk, ← h.outs_lab k hk]
    simp only [History.live]
    obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.1 hle
    rw [← Finset.disjUnion_eq_union _ _ hdisj]
    show _ = ((h.live k).val - (h.ev k).ins.val + (h.ev k).outs.val).map h.lab
    rw [ht, add_tsub_cancel_left, Multiset.map_add, Multiset.map_add,
      add_tsub_cancel_left]

/-- Antichain bound for a rule with `|lhs| = |rhs| = m`:
`m * |A| ≤ |init|`. -/
theorem antichain_card_le (hv : h.Valid) (hcons : r.IsConservative)
    {A : Finset ℕ} (hA : h.IsAntichain A) :
    r.lhsSize * A.card ≤ h.init.card :=
  History.antichain_card_le hv (fun k hk => h.ins_card hk)
    (fun k hk => (h.outs_card hk).trans hcons.symm) hA

/-- Cone bound: at most `(|rhs| + 1)^t` events within directed distance
`t` of an event. -/
theorem ball_card_le (hv : h.Valid) (i t : ℕ) :
    (h.ball i t).card ≤ (r.rhsSize + 1) ^ t :=
  History.ball_card_le hv (fun k hk => (h.outs_card hk).le) i t

end RuleHistory

/-! ## The rule of arXiv:2102.09363 -/

/-- In every valid history of the rule `{{x,y},{y,z},{z,w},{w,v}} →
{{y,u},{u,v},{w,x},{x,u}}` with `N` initial hyperedges, every antichain
of the causal graph has at most `N / 4` events. -/
theorem gorardNamedRule_antichain_card_le {V : Type*}
    (h : RuleHistory CandidateCatalog.gorardNamedRule V) (hv : h.Valid)
    {A : Finset ℕ} (hA : h.IsAntichain A) : 4 * A.card ≤ h.init.card :=
  h.antichain_card_le hv CandidateCatalog.gorardNamedRule_isConservative hA

/-- In every valid history of the rule, at most `5^t` events lie within
directed distance `t` of an event. -/
theorem gorardNamedRule_ball_card_le {V : Type*}
    (h : RuleHistory CandidateCatalog.gorardNamedRule V) (hv : h.Valid) (i t : ℕ) :
    (h.ball i t).card ≤ 5 ^ t :=
  h.ball_card_le hv i t

/-- Statement O1 (OPEN): linear cone growth. For every number `N` of
initial hyperedges there is `c` such that, in every valid history of `r`
with `N` initial hyperedges, every event `i` and every `t` satisfy
`|ball i t| ≤ c * (t + 1)`. The statement quantifies over all update orders. -/
def ConeGrowthLinear {P : Type*} (r : Rule P) : Prop :=
  ∀ N : ℕ, ∃ c : ℕ, ∀ (V : Type) (h : RuleHistory r V), h.Valid →
    h.init.card = N → ∀ i < h.n, ∀ t, (h.ball i t).card ≤ c * (t + 1)

/-- O1 for the rule of arXiv:2102.09363. -/
def GorardNamedRuleConeGrowthLinear : Prop :=
  ConeGrowthLinear CandidateCatalog.gorardNamedRule

end CausalHistory
end InfraFormalization
