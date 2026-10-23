/-
Lemmas about the event list of the fire-all evolution, and a function
`stepZeroAncestor` that walks back to a step-0 event.

The evolution is `tracedFireAllEvolve`. `fireAllStep` applies every match
of every rule found in the state, including matches that share edges. It
is not a Wolfram model update when matches overlap.

PROVED (no `sorry`, no `native_decide`):

  * `tracedFireAllStep_events_step`: every event of
    `tracedFireAllStep sys H k` has step index `k`.
  * `tracedFireAllStep_events_length`: the number of events of one step
    is the sum over rules of `(allMatches r H).length`.
  * `tracedFireAllStep_events_empty_iff`: one step has no events iff no
    rule has a match.
  * `tracedFireAllEvolve_empty_of_no_first_batch`: if step 0 on `seed`
    has no events, the evolution is `(seed, [])` at every depth.
  * `tracedFireAllEvolve_first_batch_prefix`: for d ≥ 1, the step-0
    events are a prefix of the event list at depth d.
  * `step_zero_events_exist` and `weak_R1_holds`: if the event list at
    depth d is nonempty, it contains an event with step index 0.
  * `stepZeroAncestor_step_zero`: for an event with step index 0,
    `stepZeroAncestor` returns its own index.
  * `ancestorUnique_unconditional`: `AncestorUnique` holds because
    `stepZeroAncestor` returns an `Option Nat`.

OPEN: `AncestorTotal`, the statement that `stepZeroAncestor` returns
`some` for every event index.

`EdgeCausallyDisjointBridge.EdgeCausallyDisjoint` is stated for
`tracedSingleWayEvolve`. The lemmas of this module concern
`tracedFireAllEvolve`, so they do not prove any conjunct of
`EdgeCausallyDisjoint`.
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

/-! ## Section B: outer step factorisation of `tracedFireAllStep`

`outerStep` is the per-rule step of the outer fold, in the form of
`FreshVertexPartition.innerFoldl`. -/

/-- Outer per-rule step of `tracedFireAllStep`: run the inner foldl
over `(allMatches r H)` to process all matches of rule `r`. -/
def outerStep (H : ExecHG ℕ) (baseFresh step : ℕ)
    (acc : InnerAcc) (r : ExecRule) : InnerAcc :=
  let (state, offset, ruleIdx, events) := acc
  let matchRes := innerFoldl r baseFresh step (allMatches r H)
    (state, offset, ruleIdx, events)
  (matchRes.1, matchRes.2.1, ruleIdx + 1, matchRes.2.2.2)

/-- `tracedFireAllStep` expressed via the outer foldl over rules. -/
theorem tracedFireAllStep_eq_outer (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    tracedFireAllStep sys H k =
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

/-- The events of `tracedFireAllStep sys H k` all have step index `k`. -/
theorem tracedFireAllStep_events_step (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    ∀ e ∈ (tracedFireAllStep sys H k).2, e.step = k := by
  intro e he
  rw [tracedFireAllStep_eq_outer] at he
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

/-- If no rule has any match on `H`, `tracedFireAllStep sys H k` is
the identity on state and produces no events. -/
theorem tracedFireAllStep_no_matches (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ)
    (h : ∀ r ∈ sys.rules, allMatches r H = []) :
    tracedFireAllStep sys H k = (H, []) := by
  rw [tracedFireAllStep_eq_outer]
  simp only
  rw [foldl_outerStep_no_matches H (nextFresh H) k sys.rules (H, 0, 0, []) h]

/-! ## Section E: length characterisation of the step's event list

The number of events emitted by `tracedFireAllStep sys H k` is the
sum of match counts across rules and does not depend on `k`. Section F
uses this to pass from "step 0 has no events" to "no rule has a match". -/

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

/-- The number of events of
`tracedFireAllStep sys H k` equals the total match count and is
independent of `k`. -/
theorem tracedFireAllStep_events_length (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    (tracedFireAllStep sys H k).2.length =
      (sys.rules.map (fun r => (allMatches r H).length)).sum := by
  rw [tracedFireAllStep_eq_outer]
  simp only
  rw [foldl_outerStep_events_length H (nextFresh H) k sys.rules (H, 0, 0, [])]
  simp

/-- Empty first-batch events ↔ every rule has empty `allMatches`. -/
theorem tracedFireAllStep_events_empty_iff (sys : ExecSystem) (H : ExecHG ℕ) (k : ℕ) :
    (tracedFireAllStep sys H k).2 = [] ↔
      ∀ r ∈ sys.rules, allMatches r H = [] := by
  constructor
  · intro h
    have hlen : (tracedFireAllStep sys H k).2.length = 0 := by
      rw [h]; rfl
    rw [tracedFireAllStep_events_length] at hlen
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
    rw [tracedFireAllStep_no_matches sys H k h]

/-! ## Section F: propagation — empty first batch yields empty evolution -/

/-- If the first batch on `seed` is empty, then `tracedFireAllEvolve`
returns `(seed, [])` at every depth.

The argument: emptiness of `(tracedFireAllStep sys seed 0).2` is
equivalent to "no rule matches on `seed`", which is independent of the
step parameter. So `tracedFireAllStep sys seed n = (seed, [])` at
every `n`. Induct on the depth. -/
theorem tracedFireAllEvolve_empty_of_no_first_batch
    (sys : ExecSystem) (seed : ExecHG ℕ)
    (h0 : (tracedFireAllStep sys seed 0).2 = []) :
    ∀ d, tracedFireAllEvolve sys seed d = (seed, []) := by
  -- Lift `h0` to the rule-level "no matches" hypothesis.
  have hnm : ∀ r ∈ sys.rules, allMatches r seed = [] :=
    (tracedFireAllStep_events_empty_iff sys seed 0).mp h0
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    show tracedFireAllEvolve sys seed (d + 1) = (seed, [])
    -- Unfold; the state at depth `d` is `seed` by IH, so the next step
    -- is also `(seed, [])` by `tracedFireAllStep_no_matches`.
    have hstep : tracedFireAllStep sys seed d = (seed, []) :=
      tracedFireAllStep_no_matches sys seed d hnm
    simp only [tracedFireAllEvolve, ih, hstep, List.append_nil]

/-! ## Section G: the depth-`d` event list contains the first batch as a prefix

For `d ≥ 1`, the events of `tracedFireAllEvolve sys seed d` factor as
`(tracedFireAllStep sys seed 0).2 ++ rest_d`, so the filter on
`step = 0` has length at least `(tracedFireAllStep sys seed 0).2.length`. -/

/-- The events of `tracedFireAllEvolve sys seed (d+1)` have the first
batch as a prefix. -/
theorem tracedFireAllEvolve_first_batch_prefix
    (sys : ExecSystem) (seed : ExecHG ℕ) :
    ∀ d, ∃ rest, (tracedFireAllEvolve sys seed (d + 1)).2 =
      (tracedFireAllStep sys seed 0).2 ++ rest := by
  intro d
  induction d with
  | zero =>
    refine ⟨[], ?_⟩
    simp [tracedFireAllEvolve]
  | succ k ih =>
    obtain ⟨rest_k, hk⟩ := ih
    refine ⟨rest_k ++
      (tracedFireAllStep sys (tracedFireAllEvolve sys seed (k + 1)).1 (k + 1)).2,
      ?_⟩
    show (tracedFireAllEvolve sys seed (k + 2)).2 = _
    have : (tracedFireAllEvolve sys seed (k + 2)).2 =
      (tracedFireAllEvolve sys seed (k + 1)).2 ++
      (tracedFireAllStep sys (tracedFireAllEvolve sys seed (k + 1)).1 (k + 1)).2 := by
      rfl
    rw [this, hk]
    simp [List.append_assoc]

/-! ## Section H: a step-0 event exists when the event list is nonempty -/

/-- If the event list of `tracedFireAllEvolve sys seed d` is nonempty,
it contains an event with step index 0. PROVED. -/
theorem step_zero_events_exist (sys : ExecSystem) (seed : ExecHG ℕ) (d : ℕ) :
    ∀ i : ℕ, i < (tracedFireAllEvolve sys seed d).2.length →
      0 < ((tracedFireAllEvolve sys seed d).2.filter (·.step = 0)).length := by
  intro i hi
  -- Case-split on whether the first batch is empty.
  by_cases h0 : (tracedFireAllStep sys seed 0).2 = []
  · -- Empty first batch ⇒ entire evolution is empty ⇒ hypothesis is false.
    exfalso
    have : tracedFireAllEvolve sys seed d = (seed, []) :=
      tracedFireAllEvolve_empty_of_no_first_batch sys seed h0 d
    rw [this] at hi
    simp at hi
  · -- Non-empty first batch: for `d ≥ 1`, the events contain the first
    -- batch as a prefix, and every event in the first batch has step = 0.
    -- For `d = 0`, hypothesis is false.
    cases d with
    | zero =>
      exfalso
      simp [tracedFireAllEvolve] at hi
    | succ d' =>
      obtain ⟨rest, hrest⟩ :=
        tracedFireAllEvolve_first_batch_prefix sys seed d'
      rw [hrest]
      -- filter on step=0 of (first_batch ++ rest) has at least
      -- first_batch.filter (·.step = 0) = first_batch elements.
      rw [List.filter_append]
      rw [List.length_append]
      -- first_batch.filter (·.step = 0) = first_batch (every event has step = 0).
      have hfb : (tracedFireAllStep sys seed 0).2.filter (·.step = 0) =
                 (tracedFireAllStep sys seed 0).2 := by
        apply List.filter_eq_self.mpr
        intro e he
        have : e.step = 0 := tracedFireAllStep_events_step sys seed 0 e he
        simp [this]
      rw [hfb]
      -- (tracedFireAllStep sys seed 0).2.length > 0 since h0 says it's non-empty.
      have hpos : 0 < (tracedFireAllStep sys seed 0).2.length := by
        rw [List.length_pos_iff_ne_nil]
        exact h0
      omega

/-! ## Section I: `stepZeroSelf` -/

/-- `stepZeroSelf e _h` is `e.matchIdx`, the position of `e` in the event
list of its step (counted across all rules). The hypothesis `_h` is not
used. -/
def stepZeroSelf (e : CausalEvent) (_h : e.step = 0) : Nat := e.matchIdx

/-! ## Section J: backward walk to a step-0 event

`EdgeCausallyDisjointBridge.predOf edges i` lists the `j` with `(j, i)`
in `edges`. The walk follows the first such `j` at each step until it
reaches a step-0 event or the fuel runs out. -/

/-- `stepZeroAncestorAux events edges i fuel` returns `some i` if event
`i` has step 0. Otherwise it moves to the first entry of
`predOf edges i` and decreases the fuel. It returns `none` when the fuel
is 0, when `i` is out of range, or when event `i` has no predecessor. -/
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

/-- `stepZeroAncestor events edges i` is `stepZeroAncestorAux` with fuel
`events.length`. -/
def stepZeroAncestor
    (events : List CausalEvent) (edges : List (Nat × Nat))
    (i : Nat) : Option Nat :=
  stepZeroAncestorAux events edges i events.length

/-- For an event with step index 0, `stepZeroAncestor` returns the
event's own index. -/
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

/-! ## Section K: the statements `AncestorTotal` and `AncestorUnique` -/

/-- `AncestorTotal sys seed` (OPEN): for every depth d and every event
index i of `tracedFireAllEvolve sys seed d`, `stepZeroAncestor` returns
`some a` for some `a`. The library contains no proof of it. -/
def AncestorTotal (sys : ExecSystem) (seed : ExecHG ℕ) : Prop :=
  ∀ d : Nat,
    let events := (tracedFireAllEvolve sys seed d).2
    let edges := deriveCausalEdges events
    ∀ i : ℕ, i < events.length → ∃ a, stepZeroAncestor events edges i = some a

/-- `AncestorUnique sys seed`: two values returned by `stepZeroAncestor`
for the same index are equal. It holds for every function into
`Option Nat` (`ancestorUnique_unconditional`). -/
def AncestorUnique (sys : ExecSystem) (seed : ExecHG ℕ) : Prop :=
  ∀ d : Nat,
    let events := (tracedFireAllEvolve sys seed d).2
    let edges := deriveCausalEdges events
    ∀ i a₁ a₂, stepZeroAncestor events edges i = some a₁ →
                stepZeroAncestor events edges i = some a₂ → a₁ = a₂

/-- Uniqueness holds because `Option.some` is injective. -/
theorem ancestorUnique_unconditional (sys : ExecSystem) (seed : ExecHG ℕ) :
    AncestorUnique sys seed := by
  intro d events edges i a₁ a₂ h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## Section L: relation to `EdgeCausallyDisjoint`

`EdgeCausallyDisjointBridge.EdgeCausallyDisjoint sys seed` is stated for
`tracedSingleWayEvolve`. Its first conjunct has the same form as
`weak_R1_holds`, and its second conjunct is `True`. `weak_R1_holds` is
stated for `tracedFireAllEvolve`, so it does not prove the first
conjunct of `EdgeCausallyDisjoint`. -/

/-- For every system, seed and depth d: if the event list of
`tracedFireAllEvolve sys seed d` is nonempty, it contains an event with
step index 0. This is `step_zero_events_exist`. -/
theorem weak_R1_holds (sys : ExecSystem) (seed : ExecHG ℕ) :
    ∀ d : Nat,
      let events := (tracedFireAllEvolve sys seed d).2
      (∀ i : Nat, i < events.length →
        0 < (events.filter (·.step = 0)).length) := by
  intro d
  exact step_zero_events_exist sys seed d

end StepZeroAncestor
end InfraFormalization
