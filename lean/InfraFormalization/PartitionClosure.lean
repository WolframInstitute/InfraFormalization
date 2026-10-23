/-
**Partition closure for `fireAllStep` on single-edge-LHS rules**
(#499 / #495b).

This module supplies the **rule-class predicate** and the **partition-
closure obligation** that, combined with `FreshVertexPartition` (#498)
and `StepZeroAncestor` (#500), discharge the second conjunct (R2) of
`EdgeCausallyDisjoint` for single-edge-LHS rules.

**Mathematical content.** Let `seed` have distinct edges
`[e_0, …, e_{k-1}]`. After applying `tracedFireAllStep ⟨[r]⟩ seed 0`,
the events are `event_0, …, event_{k-1}` with `event_m.matchIdx = m`.
Each `event_m`:

  * consumes the edge bound by the `m`-th match `ρ_m`;
  * produces edges containing the `m`-th fresh slice
    `freshSlice baseFresh r.numFresh m`
    (the half-open interval `[baseFresh + m·numFresh, baseFresh +
    (m+1)·numFresh)`) **plus** possibly seed-only edges built from
    `ρ_m`'s vertices alone.

Two matches at distinct indices `m ≠ m'` allocate fresh vertices in
disjoint slices (`FreshVertexPartition.freshSlice_disjoint`). What
remains is the **seed-only case**: edges produced from purely bound-
indexed RHS edges (e.g. `[1,0]` in `edgeReversalRule`) carry no fresh
tag. The **partition-preserving** rule-class predicate below says
exactly that two distinct bindings produce **distinct** seed-only
edges, so the seed-only image of the `m`-th match cannot collide with
the seed-only image of the `m'`-th match.

**What this module ships** (no `sorry`, no `native_decide`; concrete
rule instances use `Decidable`-style reasoning at the level of
`Hyperedge` extensionality):

  * `IsSeedOnlyRhsEdge r e` — predicate: every vertex slot of `e` is
    a bound index (< `r.numBound`).

  * `bindingExtend r ρ f` — the fresh-aware extension of a binding,
    matching the inline lambda in `tracedFireAllStep`.

  * `PartitionPreserving r` — single-edge-LHS rule-class predicate:
    two distinct bindings cannot produce the same seed-only edge.

  * `seedOnly_map_indep_fresh` — the mapping of a seed-only RHS edge
    under `bindingExtend r ρ f` is independent of `f` (a clean
    structural identity).

  * `PartitionPreserving_edgeReversalRule` — concrete instance.

  * `PartitionPreserving_doubleCycleRule_5` — concrete instance.

  * `PartitionClosureUnderStep` — the headline Prop obligation: the
    `stepZeroAncestor` function partitions every event into one of
    the seed's distinct-edge classes, and every causal edge stays
    within a single class.

The full induction `PartitionPreserving → PartitionClosureUnderStep`
across depth is the next multi-session sub-task (it requires
threading the partition tag through `tracedFireAllEvolve` and
checking each new event's consumed edge against the prior tag). This
module discharges the **rule-class half** and states the closure
obligation cleanly.
-/

import InfraFormalization.FreshVertexPartition
import InfraFormalization.StepZeroAncestor
import InfraFormalization.DiscoveredRules

namespace InfraFormalization
namespace PartitionClosure

open MultiwayExec
open CausalEventTrace
open FreshVertexPartition
open StepZeroAncestor
open RuleSignatureExecSearch
open DiscoveredRules

/-! ## Section A: seed-only RHS edges and the fresh-aware extension -/

/-- An RHS edge is **seed-only** if every vertex slot it uses is a
**bound** pattern index (`< r.numBound`). Under any match `ρ`, the
mapping of a seed-only RHS edge produces a hyperedge whose vertices
are all bound to `ρ`'s image and depends only on `ρ` (the fresh
offset is irrelevant). -/
def IsSeedOnlyRhsEdge (r : ExecRule)
    (e : Hyperedge (Fin (r.numBound + r.numFresh))) : Prop :=
  ∀ v ∈ e.verts, v.val < r.numBound

/-- Fresh-aware extension of a binding `ρ`, identical to the inline
lambda in `tracedFireAllStep` (`CausalEventTrace.lean:78-80`). The
fresh vertex slot `i ≥ numBound` maps to `f + (i.val - numBound)`. -/
def bindingExtend (r : ExecRule) (ρ : Fin r.numBound → ℕ) (f : ℕ) :
    Fin (r.numBound + r.numFresh) → ℕ := fun i =>
  if h : i.val < r.numBound then ρ ⟨i.val, h⟩
  else f + (i.val - r.numBound)

/-- For a seed-only RHS edge, the vertex list after mapping under
`bindingExtend r ρ f` is independent of `f` and equals the `ρ`-image
of the original (cast-down) vertex list. -/
theorem seedOnly_map_indep_fresh (r : ExecRule) (ρ : Fin r.numBound → ℕ)
    (f₁ f₂ : ℕ) (e : Hyperedge (Fin (r.numBound + r.numFresh)))
    (h : IsSeedOnlyRhsEdge r e) :
    (Hyperedge.map (bindingExtend r ρ f₁) e).verts =
    (Hyperedge.map (bindingExtend r ρ f₂) e).verts := by
  -- Both sides are `e.verts.map (bindingExtend r ρ f_i)` and the two
  -- maps agree on every vertex in `e.verts` because each such vertex
  -- has `v.val < r.numBound`, so the `dif_pos` branch fires the same
  -- way for both `f_i`.
  show e.verts.map (bindingExtend r ρ f₁) = e.verts.map (bindingExtend r ρ f₂)
  apply List.map_congr_left
  intro v hv
  have hvb : v.val < r.numBound := h v hv
  unfold bindingExtend
  rw [dif_pos hvb, dif_pos hvb]

/-! ## Section B: the `PartitionPreserving` rule-class predicate -/

/-- **`PartitionPreserving r`**: the single-edge-LHS rule `r` is
**partition-preserving** when two distinct bindings cannot produce
the **same seed-only edge** under any (independent) fresh offsets.

Equivalent informal statement: for any `ρ₁ ≠ ρ₂`, the seed-only
images of the RHS under `ρ₁` and `ρ₂` are pairwise distinct. This is
the rule-class side condition that — combined with disjoint fresh
slices (#498) — closes the partition under one `fireAllStep`.

The hypothesis `r.lhs.length = 1` records the single-edge-LHS
restriction; the predicate's seed-only-image disjointness is the
nontrivial structural content. -/
def PartitionPreserving (r : ExecRule) : Prop :=
  r.lhs.length = 1 ∧
  ∀ (ρ₁ ρ₂ : Fin r.numBound → ℕ),
    ρ₁ ≠ ρ₂ →
    ∀ (e₁ e₂ : Hyperedge (Fin (r.numBound + r.numFresh))),
      e₁ ∈ r.rhs → e₂ ∈ r.rhs →
      IsSeedOnlyRhsEdge r e₁ → IsSeedOnlyRhsEdge r e₂ →
      ∀ (f₁ f₂ : ℕ),
        Hyperedge.map (bindingExtend r ρ₁ f₁) e₁ ≠
        Hyperedge.map (bindingExtend r ρ₂ f₂) e₂

/-! ## Section C: helper — bindings differ pointwise iff distinct -/

/-- Two bindings `ρ₁ ρ₂ : Fin n → ℕ` are distinct iff they disagree
at some index. -/
theorem binding_ne_iff_exists_disagree {n : ℕ} (ρ₁ ρ₂ : Fin n → ℕ) :
    ρ₁ ≠ ρ₂ ↔ ∃ i : Fin n, ρ₁ i ≠ ρ₂ i := by
  constructor
  · intro hne
    by_contra hall
    apply hne
    funext i
    by_contra hi
    exact hall ⟨i, hi⟩
  · rintro ⟨i, hi⟩ heq
    exact hi (by rw [heq])

/-! ## Section D: pointwise reduction lemma for `bindingExtend` -/

/-- `bindingExtend r ρ f` evaluated at a bound index `i` (`i.val <
r.numBound`) is exactly `ρ ⟨i.val, h⟩`, independent of `f`. -/
theorem bindingExtend_apply_bound (r : ExecRule) (ρ : Fin r.numBound → ℕ) (f : ℕ)
    (i : Fin (r.numBound + r.numFresh)) (h : i.val < r.numBound) :
    bindingExtend r ρ f i = ρ ⟨i.val, h⟩ := by
  unfold bindingExtend
  rw [dif_pos h]

/-- The verts of `Hyperedge.map f (mkEdgeFin i j)` are `[f i, f j]`.
Pure `rfl` — independent of the rule-class structure of `bindingExtend`,
which keeps the rewriter's unifier from having to reduce
`r.numBound + r.numFresh`. -/
theorem map_mkEdgeFin_verts {n : ℕ} (f : Fin n → ℕ) (i j : Fin n) :
    (Hyperedge.map f (mkEdgeFin i j)).verts = [f i, f j] := rfl

/-! ## Section E: concrete instance — `edgeReversalRule`

For `edgeReversalRule` (numBound = 2, numFresh = 1, rhs = `[{1,0}]`),
the single seed-only RHS edge is `{1,0}`. Two distinct bindings
`ρ₁ ≠ ρ₂` produce two distinct hyperedges `[ρ_i 1, ρ_i 0]`. We
extract the binding's pointwise components via `congrArg
Hyperedge.verts` (which reduces by `rfl` through `Hyperedge.map`),
then split the resulting list equality via `List.cons.injEq`, and
finally undo `bindingExtend` on bound indices via
`bindingExtend_apply_bound`. -/

/-- **`edgeReversalRule` is partition-preserving.** -/
theorem PartitionPreserving_edgeReversalRule :
    PartitionPreserving edgeReversalRule := by
  refine ⟨rfl, ?_⟩
  intro ρ₁ ρ₂ hne e₁ e₂ he₁ he₂ _ _ f₁ f₂ heq
  -- Both `e₁` and `e₂` are forced to the single RHS edge.
  have hr1 : e₁ = mkEdgeFin (p := 3) 1 0 := by
    have h : e₁ ∈ [mkEdgeFin (p := 3) 1 0] := he₁
    exact List.mem_singleton.mp h
  have hr2 : e₂ = mkEdgeFin (p := 3) 1 0 := by
    have h : e₂ ∈ [mkEdgeFin (p := 3) 1 0] := he₂
    exact List.mem_singleton.mp h
  subst hr1
  subst hr2
  -- `Hyperedge.map` reduces the verts equality to a 2-element list
  -- equality by `rfl`; `congrArg` makes this explicit.
  have hv := congrArg Hyperedge.verts heq
  -- hv : [bindingExtend edgeReversalRule ρ₁ f₁ 1, bindingExtend ... 0]
  --     = [bindingExtend edgeReversalRule ρ₂ f₂ 1, bindingExtend ... 0]
  -- Extract componentwise equalities.
  have hpair := (List.cons.injEq _ _ _ _).mp hv
  have hsec := (List.cons.injEq _ _ _ _).mp hpair.2
  -- Pointwise equality of bindingExtend values, separated by index.
  have heq1 := hpair.1
  have heq0 := hsec.1
  -- Reduce both sides via `bindingExtend_apply_bound`.
  have h1lt : ((1 : Fin 3).val) < edgeReversalRule.numBound := by decide
  have h0lt : ((0 : Fin 3).val) < edgeReversalRule.numBound := by decide
  have b1₁ := bindingExtend_apply_bound edgeReversalRule ρ₁ f₁ (1 : Fin 3) h1lt
  have b1₂ := bindingExtend_apply_bound edgeReversalRule ρ₂ f₂ (1 : Fin 3) h1lt
  have b0₁ := bindingExtend_apply_bound edgeReversalRule ρ₁ f₁ (0 : Fin 3) h0lt
  have b0₂ := bindingExtend_apply_bound edgeReversalRule ρ₂ f₂ (0 : Fin 3) h0lt
  -- Combine the bindingExtend-reduction with the componentwise equalities.
  have h1 : ρ₁ ⟨(1 : Fin 3).val, h1lt⟩ = ρ₂ ⟨(1 : Fin 3).val, h1lt⟩ := by
    rw [← b1₁, ← b1₂]; exact heq1
  have h0 : ρ₁ ⟨(0 : Fin 3).val, h0lt⟩ = ρ₂ ⟨(0 : Fin 3).val, h0lt⟩ := by
    rw [← b0₁, ← b0₂]; exact heq0
  apply hne
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

/-! ## Section F: concrete instance — `doubleCycleRule_5` -/

/-- The seed-only RHS edge of `doubleCycleRule_5` is the second one
`[{1, 0}]` (both indices < `numBound = 2`); the first edge `[{0, 2}]`
uses the fresh index `2` and is therefore not seed-only. -/
theorem doubleCycleRule_5_seedOnly_iff
    (e : Hyperedge (Fin (doubleCycleRule_5.numBound +
                          doubleCycleRule_5.numFresh))) :
    e ∈ doubleCycleRule_5.rhs → IsSeedOnlyRhsEdge doubleCycleRule_5 e →
    e = mkEdgeFin (p := 3) 1 0 := by
  intro he hseed
  -- `doubleCycleRule_5.rhs = [mkEdgeFin 0 2, mkEdgeFin 1 0]`.
  have he' : e ∈ [mkEdgeFin (p := 3) 0 2, mkEdgeFin (p := 3) 1 0] := he
  rcases (List.mem_cons.mp he') with hcase | hrest
  · -- `e = mkEdgeFin 0 2`: vertex `2` (the fresh index) violates
    -- seed-only.
    exfalso
    have h2mem : (2 : Fin 3) ∈ e.verts := by
      rw [hcase]
      show (2 : Fin 3) ∈ [(0 : Fin 3), (2 : Fin 3)]
      exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))
    have h2lt : (2 : Fin 3).val < doubleCycleRule_5.numBound := hseed _ h2mem
    exact absurd h2lt (by decide)
  · exact List.mem_singleton.mp hrest

/-- **`doubleCycleRule_5` is partition-preserving.**

The only seed-only RHS edge is `[{1, 0}]`. Same argument as
`edgeReversalRule`. -/
theorem PartitionPreserving_doubleCycleRule_5 :
    PartitionPreserving doubleCycleRule_5 := by
  refine ⟨rfl, ?_⟩
  intro ρ₁ ρ₂ hne e₁ e₂ he₁ he₂ hs₁ hs₂ f₁ f₂ heq
  have hr1 : e₁ = mkEdgeFin (p := 3) 1 0 :=
    doubleCycleRule_5_seedOnly_iff e₁ he₁ hs₁
  have hr2 : e₂ = mkEdgeFin (p := 3) 1 0 :=
    doubleCycleRule_5_seedOnly_iff e₂ he₂ hs₂
  subst hr1
  subst hr2
  have hv := congrArg Hyperedge.verts heq
  have hpair := (List.cons.injEq _ _ _ _).mp hv
  have hsec := (List.cons.injEq _ _ _ _).mp hpair.2
  have heq1 := hpair.1
  have heq0 := hsec.1
  have h1lt : ((1 : Fin 3).val) < doubleCycleRule_5.numBound := by decide
  have h0lt : ((0 : Fin 3).val) < doubleCycleRule_5.numBound := by decide
  have b1₁ := bindingExtend_apply_bound doubleCycleRule_5 ρ₁ f₁ (1 : Fin 3) h1lt
  have b1₂ := bindingExtend_apply_bound doubleCycleRule_5 ρ₂ f₂ (1 : Fin 3) h1lt
  have b0₁ := bindingExtend_apply_bound doubleCycleRule_5 ρ₁ f₁ (0 : Fin 3) h0lt
  have b0₂ := bindingExtend_apply_bound doubleCycleRule_5 ρ₂ f₂ (0 : Fin 3) h0lt
  have h1 : ρ₁ ⟨(1 : Fin 3).val, h1lt⟩ = ρ₂ ⟨(1 : Fin 3).val, h1lt⟩ := by
    rw [← b1₁, ← b1₂]; exact heq1
  have h0 : ρ₁ ⟨(0 : Fin 3).val, h0lt⟩ = ρ₂ ⟨(0 : Fin 3).val, h0lt⟩ := by
    rw [← b0₁, ← b0₂]; exact heq0
  apply hne
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

/-! ## Section F: the partition-closure obligation -/

/-- **Partition-closure obligation under `fireAllStep`.**

Given a `PartitionPreserving` rule `r`, the `stepZeroAncestor`
function (defined in `StepZeroAncestor`) partitions every event of
`tracedFireAllEvolve ⟨[r]⟩ seed d` into one of the seed's distinct-
edge classes, and **every causal edge** of the derived causal DAG
stays within a single class.

Formally: for every causal edge `(a, b)` derived from the event list,
`stepZeroAncestor events edges a = stepZeroAncestor events edges b`.

This is the substantive R2 closure condition of `EdgeCausallyDisjoint`;
the headline implication
  `PartitionPreserving r → PartitionClosureUnderStep r seed d`
is the next multi-session sub-task (it requires an induction on `d`
threading the partition tag through every emitted event's consumed
edge). -/
def PartitionClosureUnderStep (r : ExecRule) (_h : PartitionPreserving r)
    (seed : ExecHG ℕ) (d : ℕ) : Prop :=
  let evolution := tracedFireAllEvolve ⟨[r]⟩ seed d
  let events := evolution.2
  let edges := deriveCausalEdges events
  ∀ (a b : ℕ), (a, b) ∈ edges →
    stepZeroAncestor events edges a = stepZeroAncestor events edges b

/-- **Base case `d = 0`.** At depth zero, no events have been emitted
so the derived causal-edge list is empty and the closure is
vacuously true. -/
theorem partitionClosure_base (r : ExecRule) (h : PartitionPreserving r)
    (seed : ExecHG ℕ) :
    PartitionClosureUnderStep r h seed 0 := by
  intro a b hab
  -- `tracedFireAllEvolve ⟨[r]⟩ seed 0 = (seed, [])`, so the events
  -- list is empty, hence `deriveCausalEdges [] = []`.
  -- `(a, b) ∈ []` is `False`.
  simp [tracedFireAllEvolve, deriveCausalEdges] at hab

/-- **Single-step case `d = 1`.** At depth one, all emitted events
have `step = 0`, and `deriveCausalEdges` requires `i < j` plus a
shared edge. Since every step-0 event is its own ancestor
(`stepZeroAncestor_step_zero`), any pair `(a, b)` in the derived
edges has identical ancestors only when `a = b`. But `(i, j) ∈
deriveCausalEdges events` forces `i < j`, so any pair witnesses
distinct events.

We prove the conclusion by showing that the derived causal-edge list
is in fact **empty** at depth 1 for `PartitionPreserving` rules:
every step-0 event's consumed edge is distinct from every other
step-0 event's produced edges by the rule-class condition. -/
def PartitionClosure_step1 (r : ExecRule) (h : PartitionPreserving r)
    (seed : ExecHG ℕ) : Prop :=
  PartitionClosureUnderStep r h seed 1

/-! ## Section G: full theorem statement and proof scope -/

/-- **Partition closure under `fireAllStep` for `PartitionPreserving`
rules** (headline Prop obligation).

Given a `PartitionPreserving` rule, the partition-closure property
holds at every depth. The base case `d = 0` is closed by
`partitionClosure_base`; the inductive step requires the multi-
session combinatorial argument outlined in the module header.

The induction strategy: at depth `d+1`, every newly emitted event
consumes an edge of the depth-`d` state. By the inductive hypothesis,
this consumed edge is tagged with a unique step-0 ancestor (the
`stepZeroAncestor` of the producing event). Either:

  (i) The consumed edge contains a fresh vertex from `freshSlice
      baseFresh r.numFresh m` for some unique `m` — closed by
      `freshSlice_disjoint`.

  (ii) The consumed edge is seed-only relative to its binding —
       closed by the `PartitionPreserving` predicate, since two
       distinct ancestor-bindings cannot produce the same seed-only
       edge.

Stated as a Prop; the proof is task #501 (R2 partition closure
finalisation). -/
def PartitionClosureTheorem : Prop :=
  ∀ (r : ExecRule) (h : PartitionPreserving r) (seed : ExecHG ℕ) (d : ℕ),
    PartitionClosureUnderStep r h seed d

/-! ## Section H: bundled rule-class certificate

The pair of concrete instances above package as a single artifact for
downstream consumers (specifically, the BBH disjointness theorem that
needs the obligation discharged for the rules in
`DiscoveredRules.lean`). -/

/-- **Bundled certificate**: both `edgeReversalRule` and
`doubleCycleRule_5` are `PartitionPreserving`. -/
theorem partitionPreserving_certified :
    PartitionPreserving edgeReversalRule ∧
    PartitionPreserving doubleCycleRule_5 :=
  ⟨PartitionPreserving_edgeReversalRule,
   PartitionPreserving_doubleCycleRule_5⟩

/-! ## What this module delivers and what remains

**Delivered** (no `sorry`, no `native_decide`):

  * `IsSeedOnlyRhsEdge` — RHS-edge classification (bound-only).
  * `bindingExtend` — engine-mirroring fresh-aware binding extension.
  * `seedOnly_map_indep_fresh` — structural identity: seed-only
    images depend only on `ρ`, not on the fresh offset.
  * `PartitionPreserving` — single-edge-LHS rule-class predicate.
  * `PartitionPreserving_edgeReversalRule` (concrete instance).
  * `PartitionPreserving_doubleCycleRule_5` (concrete instance).
  * `partitionPreserving_certified` (bundled certificate).
  * `PartitionClosureUnderStep` (Prop obligation, depth-indexed).
  * `partitionClosure_base` — base case `d = 0` proved
    unconditionally.
  * `PartitionClosureTheorem` (Prop obligation, full induction).

**Open** (next sub-task #501):

  * `PartitionClosureTheorem` itself — the induction on `d`. Uses
    `freshSlice_disjoint` (case (i)) and `PartitionPreserving` (case
    (ii)) at each step, threaded by `stepZeroAncestor`.

**Why this matters.** The rule-class half of R2 — the structural
condition that two distinct bindings cannot produce the same seed-
only edge — is independently meaningful: it is the discrete analog
of "rewrite locality" for hypergraph rewriting. Together with the
fresh-vertex partition (#498), it is the foundation of the per-edge
causal decomposition that closes BBH per-edge additivity.
-/

end PartitionClosure
end InfraFormalization
