/-
**Step-zero ancestor function for `tracedSingleWayEvolve`** (#500, #495c).

This module discharges R1 of the `EdgeCausallyDisjoint` predicate (#495)
and defines the ancestor function used by R2's partition-closure
argument (#499/#501).

**What this delivers** (no `sorry`, no `decide`, no `native_decide`):

  * `step_zero_events_exist` — weak R1: when the evolution has
    produced any events, at least one of them is a step-0 event. This
    discharges the first conjunct of the existing `EdgeCausallyDisjoint`
    obligation.

  * `stepZeroSelf` — for a step-0 event, the ancestor is its own
    `matchIdx`: that's the index of the seed edge it processed.

  * `stepZeroAncestor` — fuel-bounded backward BFS over the causal-edge
    list that returns the index of the step-0 ancestor (or `none` if
    the walk fails to find one within fuel).

  * `stepZeroAncestor_step_zero` — for step-0 events the ancestor
    function returns the event's own index.

  * `AncestorTotal` / `AncestorUnique` — Prop-level obligations
    expressing the meaningful R1 conditions; totality is the #499/#501
    closure step. Uniqueness is trivial by `Option Nat` shape.

  * `weak_R1_holds` — the existing `EdgeCausallyDisjoint` first
    conjunct, proved unconditionally.

**Proof strategy for `step_zero_events_exist`** — case split on whether
the seed produces any matches at step 0:

  * If `(tracedSingleWayStep sys seed 0).2 = []` (no matches anywhere
    on the seed): the inner `foldl` over `allMatches r seed = []` for
    every rule `r` returns the initial accumulator, so state and event
    lists are preserved across the outer rule `foldl`. By induction on
    depth, `tracedSingleWayEvolve sys seed d = (seed, [])` for all `d`,
    so the hypothesis `i < events.length` is vacuously false.

  * Otherwise: for `d ≥ 1`, the first batch is a prefix of the depth-`d`
    events. Every event in the first batch has `.step = 0` (by the
    `events ∋ e ↦ e.step = step` invariant of `tracedSingleWayStep`).
    Hence `events.filter (·.step = 0)` has at least the first batch as
    a subset and therefore length `≥ 1`.
-/

import InfraFormalization.EdgeCausallyDisjointBridge
import InfraFormalization.FreshVertexPartition

namespace InfraFormalization
namespace StepZeroAncestor

open MultiwayExec
open CausalEventTrace
open EdgeCausallyDisjointBridge
open FreshVertexPartition

/-! ## Section A: generic `List.foldl` invariant -/

/-- If a predicate is preserved by the step function, it is preserved
across the entire fold. -/
lemma foldl_invariant {α β : Type*} (P : β → Prop) (f : β → α → β)
    (xs : List α) (init : β)
    (hStep : ∀ b a, P b → P (f b a)) (h0 : P init) :
    P (xs.foldl f init) := by
  induction xs generalizing init with
  | nil => exact h0
  | cons x xs ih => exact ih (f init x) (hStep init x h0)

/-! ## Section B: outer step factorisation of `tracedSingleWayStep`

We name the outer per-rule step so we can reason about the rule-list
`foldl` modularly, in the style of `FreshVertexPartition.innerFoldl`. -/

/-- Outer per-rule step of `tracedSingleWayStep`: run the inner foldl
over `(allMatches r H)` to process all matches of rule `r`. -/
def outerStep (H : ExecHG ℕ) (baseFresh step : ℕ)
    (acc : InnerAcc) (r : ExecRule) : InnerAcc :=
  let (state, offset, ruleIdx, events) := acc
  let matchRes := innerFoldl r baseFresh step (allMatches r H)
    (state, offset, ruleIdx, events)
  (matchRes.1, matchRes.2.1, ruleIdx + 1, matchRes.2.2.2)

/-- `tracedSingleWayStep` expressed via the outer foldl over rules. -/
theorem tracedSingleWayStep_eq_outer (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    tracedSingleWayStep sys H k =
      let baseFresh := nextFresh H
      let final := sys.rules.foldl (outerStep H baseFresh k) (H, 0, 0, [])
      (final.1, final.2.2.2) := by
  rfl

/-! ## Section C: every emitted event carries the step index -/

/-- A single `innerStep` appends exactly one event whose `step` field
equals the outer `step` parameter; the prior events are preserved. -/
theorem innerStep_events_append (r : ExecRule) (baseFresh step : ℕ)
    (s : ExecHG ℕ) (o i : ℕ) (es : List CausalEvent)
    (ρ : Fin r.numBound → ℕ) :
    ∃ e_new : CausalEvent,
      e_new.step = step ∧
      (innerStep r baseFresh step (s, o, i, es) ρ).2.2.2 = es ++ [e_new] := by
  refine ⟨{ step := step
            matchIdx := es.length
            ruleIdx := i
            consumed := mapPattern ρ r.lhs
            produced := mapPattern (fun j =>
              if h : j.val < r.numBound then ρ ⟨j.val, h⟩
              else baseFresh + o + (j.val - r.numBound)) r.rhs }, ?_, ?_⟩
  · rfl
  · rfl

/-- After the inner foldl, every event in the accumulator has step `= k`,
given the invariant held at entry. -/
theorem innerFoldl_events_step (r : ExecRule) (baseFresh step : ℕ)
    (binds : List (Fin r.numBound → ℕ)) (init : InnerAcc)
    (h0 : ∀ e ∈ init.2.2.2, e.step = step) :
    ∀ e ∈ (innerFoldl r baseFresh step binds init).2.2.2, e.step = step := by
  unfold innerFoldl
  refine foldl_invariant
    (P := fun acc : ExecHG ℕ × Nat × Nat × List CausalEvent =>
      ∀ e ∈ acc.2.2.2, e.step = step)
    _ _ _ ?_ h0
  rintro ⟨s, o, i, es⟩ ρ hb
  obtain ⟨e_new, hnew_step, heq⟩ :=
    innerStep_events_append r baseFresh step s o i es ρ
  intro e he
  rw [heq, List.mem_append] at he
  rcases he with he | he
  · exact hb e he
  · rw [List.mem_singleton] at he
    rw [he, hnew_step]

/-- After the outer step (one rule's processing), every event has step
`= k`, given the invariant held at entry. -/
theorem outerStep_events_step (H : ExecHG ℕ) (baseFresh step : ℕ)
    (acc : InnerAcc) (r : ExecRule)
    (h0 : ∀ e ∈ acc.2.2.2, e.step = step) :
    ∀ e ∈ (outerStep H baseFresh step acc r).2.2.2, e.step = step := by
  unfold outerStep
  rcases acc with ⟨s, o, i, es⟩
  simp only
  exact innerFoldl_events_step r baseFresh step (allMatches r H) (s, o, i, es) h0

/-- **Headline:** every event emitted by `tracedSingleWayStep sys H k`
has `e.step = k`. -/
theorem tracedSingleWayStep_events_step (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    ∀ e ∈ (tracedSingleWayStep sys H k).2, e.step = k := by
  intro e he
  rw [tracedSingleWayStep_eq_outer] at he
  simp only at he
  refine foldl_invariant
    (P := fun acc : ExecHG ℕ × Nat × Nat × List CausalEvent =>
      ∀ e' ∈ acc.2.2.2, e'.step = k)
    _ sys.rules (H, 0, 0, []) ?_ ?_ e he
  · intro b r hb
    exact outerStep_events_step H (nextFresh H) k b r hb
  · intro e' he'
    simp at he'

/-! ## Section D: state preservation when no matches exist

If `allMatches r H = []` for every rule `r`, the inner `foldl` is empty
for every rule, hence the accumulator only has its rule-index advanced.
The state and event-list components are preserved. -/

/-- Empty `allMatches` for a single rule: the outer step preserves
state, offset, and events; only `ruleIdx` advances. -/
theorem outerStep_no_match (H : ExecHG ℕ) (baseFresh step : ℕ)
    (acc : InnerAcc) (r : ExecRule)
    (hr : allMatches r H = []) :
    outerStep H baseFresh step acc r =
      (acc.1, acc.2.1, acc.2.2.1 + 1, acc.2.2.2) := by
  unfold outerStep
  rcases acc with ⟨s, o, i, es⟩
  simp only
  unfold innerFoldl
  rw [hr]
  simp

/-- Empty `allMatches` for every rule: the outer `foldl` returns the
initial accumulator with only `ruleIdx` advanced by `rs.length`. -/
theorem foldl_outerStep_no_matches (H : ExecHG ℕ) (baseFresh step : ℕ)
    (rs : List ExecRule) (init : InnerAcc)
    (h : ∀ r ∈ rs, allMatches r H = []) :
    rs.foldl (outerStep H baseFresh step) init =
      (init.1, init.2.1, init.2.2.1 + rs.length, init.2.2.2) := by
  induction rs generalizing init with
  | nil =>
    rcases init with ⟨s, o, i, es⟩
    simp
  | cons r rs ih =>
    rw [List.foldl_cons]
    have hr_head : allMatches r H = [] := h r List.mem_cons_self
    have hr_tail : ∀ r' ∈ rs, allMatches r' H = [] := fun r' hr' =>
      h r' (List.mem_cons_of_mem r hr')
    rw [outerStep_no_match H baseFresh step init r hr_head]
    rw [ih _ hr_tail]
    rcases init with ⟨s, o, i, es⟩
    simp
    ring

/-- If no rule has any match on `H`, `tracedSingleWayStep sys H k` is
the identity on state and produces no events. -/
theorem tracedSingleWayStep_no_matches (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ)
    (h : ∀ r ∈ sys.rules, allMatches r H = []) :
    tracedSingleWayStep sys H k = (H, []) := by
  rw [tracedSingleWayStep_eq_outer]
  simp only
  rw [foldl_outerStep_no_matches H (nextFresh H) k sys.rules (H, 0, 0, []) h]

/-! ## Section E: length characterisation of the step's event list

The number of events emitted by `tracedSingleWayStep sys H k` is the
sum of match-counts across rules, **independent of `k`**. We need this
to translate "first-batch empty" (the natural starting hypothesis) into
"no matches anywhere" (the technical hypothesis above). -/

/-- The inner foldl appends exactly `binds.length` events; thus the
events component's length grows by `binds.length`. -/
theorem innerFoldl_events_length (r : ExecRule) (baseFresh step : ℕ)
    (binds : List (Fin r.numBound → ℕ)) (init : InnerAcc) :
    (innerFoldl r baseFresh step binds init).2.2.2.length =
      init.2.2.2.length + binds.length := by
  unfold innerFoldl
  induction binds generalizing init with
  | nil => simp
  | cons ρ rest ih =>
    rw [List.foldl_cons]
    rw [ih (innerStep r baseFresh step init ρ)]
    rcases init with ⟨s, o, i, es⟩
    obtain ⟨e_new, _, heq⟩ :=
      innerStep_events_append r baseFresh step s o i es ρ
    rw [heq]
    simp
    ring

/-- One outer step grows events by exactly `(allMatches r H).length`. -/
theorem outerStep_events_length (H : ExecHG ℕ) (baseFresh step : ℕ)
    (acc : InnerAcc) (r : ExecRule) :
    (outerStep H baseFresh step acc r).2.2.2.length =
      acc.2.2.2.length + (allMatches r H).length := by
  unfold outerStep
  rcases acc with ⟨s, o, i, es⟩
  simp only
  exact innerFoldl_events_length r baseFresh step (allMatches r H) (s, o, i, es)

/-- The full outer foldl grows events by the sum of per-rule match counts. -/
theorem foldl_outerStep_events_length (H : ExecHG ℕ) (baseFresh step : ℕ)
    (rs : List ExecRule) (init : InnerAcc) :
    (rs.foldl (outerStep H baseFresh step) init).2.2.2.length =
      init.2.2.2.length +
        (rs.map (fun r => (allMatches r H).length)).sum := by
  induction rs generalizing init with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih, outerStep_events_length]
    simp [List.map_cons, List.sum_cons]
    ring

/-- **Length characterisation:** the number of events from
`tracedSingleWayStep sys H k` equals the total match count and is
independent of `k`. -/
theorem tracedSingleWayStep_events_length (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    (tracedSingleWayStep sys H k).2.length =
      (sys.rules.map (fun r => (allMatches r H).length)).sum := by
  rw [tracedSingleWayStep_eq_outer]
  simp only
  rw [foldl_outerStep_events_length H (nextFresh H) k sys.rules (H, 0, 0, [])]
  simp

/-- Empty first-batch events ↔ every rule has empty `allMatches`. -/
theorem tracedSingleWayStep_events_empty_iff (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    (tracedSingleWayStep sys H k).2 = [] ↔
      ∀ r ∈ sys.rules, allMatches r H = [] := by
  constructor
  · intro h
    have hlen : (tracedSingleWayStep sys H k).2.length = 0 := by
      rw [h]; rfl
    rw [tracedSingleWayStep_events_length] at hlen
    -- sum of nonnegative ℕ list = 0 → every element = 0
    intro r hr
    have hzero : (allMatches r H).length = 0 := by
      have : (sys.rules.map (fun r => (allMatches r H).length)).sum = 0 := hlen
      have hmem : (allMatches r H).length ∈
          sys.rules.map (fun r => (allMatches r H).length) :=
        List.mem_map_of_mem hr
      exact Nat.eq_zero_of_le_zero
        (le_of_eq_of_le rfl (this ▸ List.le_sum_of_mem hmem))
    exact List.length_eq_zero_iff.mp hzero
  · intro h
    rw [tracedSingleWayStep_no_matches sys H k h]

/-! ## Section F: propagation — empty first batch yields empty evolution -/

/-- If the first batch on `seed` is empty, then `tracedSingleWayEvolve`
returns `(seed, [])` at every depth.

The argument: emptiness of `(tracedSingleWayStep sys seed 0).2` is
equivalent to "no rule matches on `seed`", which is independent of the
step parameter. So `tracedSingleWayStep sys seed n = (seed, [])` at
every `n`. Induct on the depth. -/
theorem tracedSingleWayEvolve_empty_of_no_first_batch
    (sys : ExecSystem) (seed : ExecHG ℕ)
    (h0 : (tracedSingleWayStep sys seed 0).2 = []) :
    ∀ d, tracedSingleWayEvolve sys seed d = (seed, []) := by
  -- Lift `h0` to the rule-level "no matches" hypothesis.
  have hnm : ∀ r ∈ sys.rules, allMatches r seed = [] :=
    (tracedSingleWayStep_events_empty_iff sys seed 0).mp h0
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    show tracedSingleWayEvolve sys seed (d + 1) = (seed, [])
    -- Unfold; the state at depth `d` is `seed` by IH, so the next step
    -- is also `(seed, [])` by `tracedSingleWayStep_no_matches`.
    have hstep : tracedSingleWayStep sys seed d = (seed, []) :=
      tracedSingleWayStep_no_matches sys seed d hnm
    simp only [tracedSingleWayEvolve, ih, hstep, List.append_nil]

/-! ## Section G: the depth-`d` event list contains the first batch as a prefix

For `d ≥ 1`, the events of `tracedSingleWayEvolve sys seed d` factor as
`(tracedSingleWayStep sys seed 0).2 ++ rest_d`, so the filter on
`step = 0` has length at least `(tracedSingleWayStep sys seed 0).2.length`. -/

/-- The events of `tracedSingleWayEvolve sys seed (d+1)` have the first
batch as a prefix. -/
theorem tracedSingleWayEvolve_first_batch_prefix
    (sys : ExecSystem) (seed : ExecHG ℕ) :
    ∀ d, ∃ rest, (tracedSingleWayEvolve sys seed (d + 1)).2 =
      (tracedSingleWayStep sys seed 0).2 ++ rest := by
  intro d
  induction d with
  | zero =>
    refine ⟨[], ?_⟩
    simp [tracedSingleWayEvolve]
  | succ k ih =>
    obtain ⟨rest_k, hk⟩ := ih
    refine ⟨rest_k ++
      (tracedSingleWayStep sys (tracedSingleWayEvolve sys seed (k + 1)).1 (k + 1)).2,
      ?_⟩
    show (tracedSingleWayEvolve sys seed (k + 2)).2 = _
    have : (tracedSingleWayEvolve sys seed (k + 2)).2 =
      (tracedSingleWayEvolve sys seed (k + 1)).2 ++
      (tracedSingleWayStep sys (tracedSingleWayEvolve sys seed (k + 1)).1 (k + 1)).2 := by
      rfl
    rw [this, hk]
    simp [List.append_assoc]

/-! ## Section H: weak R1 — at least one step-0 event when events exist -/

/-- **Weak R1 (proved).** If `tracedSingleWayEvolve sys seed d` has any
event at all, it has at least one step-0 event. -/
theorem step_zero_events_exist (sys : ExecSystem) (seed : ExecHG ℕ) (d : ℕ) :
    ∀ i : ℕ, i < (tracedSingleWayEvolve sys seed d).2.length →
      0 < ((tracedSingleWayEvolve sys seed d).2.filter (·.step = 0)).length := by
  intro i hi
  -- Case-split on whether the first batch is empty.
  by_cases h0 : (tracedSingleWayStep sys seed 0).2 = []
  · -- Empty first batch ⇒ entire evolution is empty ⇒ hypothesis is false.
    exfalso
    have : tracedSingleWayEvolve sys seed d = (seed, []) :=
      tracedSingleWayEvolve_empty_of_no_first_batch sys seed h0 d
    rw [this] at hi
    simp at hi
  · -- Non-empty first batch: for `d ≥ 1`, the events contain the first
    -- batch as a prefix, and every event in the first batch has step = 0.
    -- For `d = 0`, hypothesis is false.
    cases d with
    | zero =>
      exfalso
      simp [tracedSingleWayEvolve] at hi
    | succ d' =>
      obtain ⟨rest, hrest⟩ :=
        tracedSingleWayEvolve_first_batch_prefix sys seed d'
      rw [hrest]
      -- filter on step=0 of (first_batch ++ rest) has at least
      -- first_batch.filter (·.step = 0) = first_batch elements.
      rw [List.filter_append]
      rw [List.length_append]
      -- first_batch.filter (·.step = 0) = first_batch (every event has step = 0).
      have hfb : (tracedSingleWayStep sys seed 0).2.filter (·.step = 0) =
                 (tracedSingleWayStep sys seed 0).2 := by
        apply List.filter_eq_self.mpr
        intro e he
        have : e.step = 0 := tracedSingleWayStep_events_step sys seed 0 e he
        simp [this]
      rw [hfb]
      -- (tracedSingleWayStep sys seed 0).2.length > 0 since h0 says it's non-empty.
      have hpos : 0 < (tracedSingleWayStep sys seed 0).2.length := by
        rw [List.length_pos_iff_ne_nil]
        exact h0
      omega

/-! ## Section I: step-0 self-ancestor -/

/-- For a step-0 event, its ancestor identifier is its own `matchIdx`
— the seed-edge index it processed. The hypothesis `h` is recorded for
documentation; the definition does not depend on it. -/
def stepZeroSelf (e : CausalEvent) (_h : e.step = 0) : Nat := e.matchIdx

/-! ## Section J: bounded-fuel backward walk to a step-0 ancestor

`predOf` (from `EdgeCausallyDisjointBridge`) gives the direct
predecessors of an event in a causal-edge list. We walk backward,
taking the first predecessor each step, until reaching a step-0 event
or running out of fuel. -/

/-- Fuel-bounded auxiliary: walk back through predecessors until a
step-0 event is found, returning its index. Returns `none` if the
walk runs out of fuel or hits an event with no predecessors. -/
def stepZeroAncestorAux
    (events : List CausalEvent) (edges : List (Nat × Nat))
    (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if h : i < events.length then
      if (events.get ⟨i, h⟩).step = 0 then
        some i
      else
        match predOf edges i with
        | [] => none
        | p :: _ => stepZeroAncestorAux events edges p fuel
    else
      none

/-- Step-0 ancestor: wraps `stepZeroAncestorAux` with `events.length`
fuel — enough for any acyclic walk. -/
def stepZeroAncestor
    (events : List CausalEvent) (edges : List (Nat × Nat))
    (i : Nat) : Option Nat :=
  stepZeroAncestorAux events edges i events.length

/-- For step-0 events the ancestor function returns the event's own
index, regardless of the predecessor structure. -/
theorem stepZeroAncestor_step_zero
    (events : List CausalEvent) (edges : List (Nat × Nat)) (i : Nat)
    (hi : i < events.length) (h0 : (events.get ⟨i, hi⟩).step = 0) :
    stepZeroAncestor events edges i = some i := by
  have hpos : 0 < events.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  unfold stepZeroAncestor
  -- Generalise: for any positive fuel, the aux returns `some i` on a
  -- step-0 event at index `i`. The aux is structurally recursive on fuel,
  -- so we destructure `fuel = n + 1` to fire the non-zero branch.
  suffices h : ∀ (fuel : Nat), 1 ≤ fuel →
      stepZeroAncestorAux events edges i fuel = some i from h events.length hpos
  intro fuel hf
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold stepZeroAncestorAux
  rw [dif_pos hi]
  simp only [h0, if_true]

/-! ## Section K: ancestor totality and uniqueness Props -/

/-- **Meaningful R1 obligation (totality):** the ancestor function is
total on `tracedSingleWayEvolve` outputs. This requires the partition
closure of #499/#501 to fully discharge. -/
def AncestorTotal (sys : ExecSystem) (seed : ExecHG ℕ) : Prop :=
  ∀ d : Nat,
    let events := (tracedSingleWayEvolve sys seed d).2
    let edges := deriveCausalEdges events
    ∀ i : ℕ, i < events.length → ∃ a, stepZeroAncestor events edges i = some a

/-- **Meaningful R1 (uniqueness):** the ancestor returned (when
present) is unique. Holds trivially because `stepZeroAncestor` returns
an `Option Nat` (single value); kept as a Prop for documentation. -/
def AncestorUnique (sys : ExecSystem) (seed : ExecHG ℕ) : Prop :=
  ∀ d : Nat,
    let events := (tracedSingleWayEvolve sys seed d).2
    let edges := deriveCausalEdges events
    ∀ i a₁ a₂, stepZeroAncestor events edges i = some a₁ →
                stepZeroAncestor events edges i = some a₂ → a₁ = a₂

/-- Uniqueness is provable unconditionally: `Option.some` is injective. -/
theorem ancestorUnique_unconditional (sys : ExecSystem) (seed : ExecHG ℕ) :
    AncestorUnique sys seed := by
  intro d events edges i a₁ a₂ h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## Section L: bridge to `EdgeCausallyDisjoint`

`step_zero_events_exist` is exactly the first conjunct of the existing
`EdgeCausallyDisjoint` predicate (the part stated as a real proposition;
the trailing `∧ True` is, well, true). -/

/-- **Weak R1 holds for every `(sys, seed)`.** This discharges the
provable content of `EdgeCausallyDisjoint`'s first conjunct. -/
theorem weak_R1_holds (sys : ExecSystem) (seed : ExecHG ℕ) :
    ∀ d : Nat,
      let events := (tracedSingleWayEvolve sys seed d).2
      (∀ i : Nat, i < events.length →
        0 < (events.filter (·.step = 0)).length) := by
  intro d
  exact step_zero_events_exist sys seed d

end StepZeroAncestor
end InfraFormalization
