/-
A rule-class predicate `PartitionPreserving` for single-edge-LHS rules,
two instances of it, and the statement `PartitionClosureUnderStep` about
the fire-all evolution.

The evolution is `tracedFireAllEvolve ⟨[r]⟩ seed d`. `fireAllStep`
applies every match of every rule found in the state, including matches
that share edges. It is not a Wolfram model update when matches overlap.

At step 0, the k-th match of the seed allocates fresh vertices in the
half-open interval `[baseFresh + k·numFresh, baseFresh + (k+1)·numFresh)`
(`FreshVertexPartition.freshSlice`). Slices of different matches are
disjoint (`FreshVertexPartition.freshSlice_disjoint`). A produced edge
whose RHS pattern uses only bound indices ("seed-only", for example
`{1,0}` in `edgeReversalRule`) contains no fresh vertex.
`PartitionPreserving r` states that two different bindings never
produce the same seed-only edge.

The module proves:

  * `seedOnly_map_indep_fresh`: the image of a seed-only RHS edge under
    `bindingExtend r ρ f` does not depend on `f`.
  * `PartitionPreserving_edgeReversalRule`,
    `PartitionPreserving_doubleCycleRule_5`: the two instances.
  * `partitionClosure_base`: `PartitionClosureUnderStep` at depth 0,
    where the event list is empty.

`PartitionClosureTheorem` states that for every `PartitionPreserving` rule, every seed and every
depth d, every causal edge `(a, b)` of the fire-all trace satisfies
`stepZeroAncestor events edges a = stepZeroAncestor events edges b`. It is not proved, and neither
is the case d = 1 (`PartitionClosure_step1`).
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

/-- An RHS edge is seed-only if every vertex slot it uses is a bound
pattern index (`< r.numBound`). -/
def IsSeedOnlyRhsEdge (r : ExecRule)
    (e : Hyperedge (Fin (r.numBound + r.numFresh))) : Prop :=
  ∀ v ∈ e.verts, v.val < r.numBound

/-- `bindingExtend r ρ f` sends a bound index `i < r.numBound` to `ρ i`
and a fresh index `i ≥ r.numBound` to `f + (i - r.numBound)`. The
extension in `CausalEventTrace.tracedFireAllStep` has the same form with
`f = baseFresh + offset'`. -/
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

/-- `PartitionPreserving r` holds when `r.lhs.length = 1` and, for any
two different bindings `ρ₁ ≠ ρ₂`, any two seed-only RHS edges `e₁`,
`e₂` and any fresh offsets `f₁`, `f₂`, the image of `e₁` under
`bindingExtend r ρ₁ f₁` differs from the image of `e₂` under
`bindingExtend r ρ₂ f₂`. -/
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

/-- The vertex list of `Hyperedge.map f (mkEdgeFin i j)` is `[f i, f j]`, by `rfl`. -/
theorem map_mkEdgeFin_verts {n : ℕ} (f : Fin n → ℕ) (i j : Fin n) :
    (Hyperedge.map f (mkEdgeFin i j)).verts = [f i, f j] := rfl

/-! ## Section E: instance `edgeReversalRule`

`edgeReversalRule` is `{0,1} → {1,0}` (`numBound = 2`). Its only RHS
edge `{1,0}` is seed-only. If two bindings `ρ₁`, `ρ₂` give equal images
`[ρ₁ 1, ρ₁ 0] = [ρ₂ 1, ρ₂ 0]`, then `ρ₁ = ρ₂`. The proof extracts the
two list components with `congrArg Hyperedge.verts` and
`List.cons.injEq`, then applies `bindingExtend_apply_bound`. -/

/-- `edgeReversalRule` satisfies `PartitionPreserving`. -/
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

/-! ## Section F: instance `doubleCycleRule_5` -/

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

/-- `doubleCycleRule_5` satisfies `PartitionPreserving`. Its only
seed-only RHS edge is `{1, 0}`, and the proof follows the one for
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

/-! ## Section G: the statement `PartitionClosureUnderStep` -/

/-- `PartitionClosureUnderStep r h seed d` states that every causal edge
`(a, b)` derived from the events of
`tracedFireAllEvolve ⟨[r]⟩ seed d` satisfies
`stepZeroAncestor events edges a = stepZeroAncestor events edges b`.

The evolution is the fire-all operator: every match found in the state
fires, including matches that share edges. The hypothesis `_h` is not
used in the statement. `partitionClosure_base` proves the case d = 0.
The implication `PartitionPreserving r → PartitionClosureUnderStep r h seed d` for d ≥ 1 is not
proved. -/
def PartitionClosureUnderStep (r : ExecRule) (_h : PartitionPreserving r)
    (seed : ExecHG ℕ) (d : ℕ) : Prop :=
  let evolution := tracedFireAllEvolve ⟨[r]⟩ seed d
  let events := evolution.2
  let edges := deriveCausalEdges events
  ∀ (a b : ℕ), (a, b) ∈ edges →
    stepZeroAncestor events edges a = stepZeroAncestor events edges b

/-- At depth 0 the event list is empty, so the derived causal-edge list
is empty and `PartitionClosureUnderStep r h seed 0` holds. -/
theorem partitionClosure_base (r : ExecRule) (h : PartitionPreserving r)
    (seed : ExecHG ℕ) :
    PartitionClosureUnderStep r h seed 0 := by
  intro a b hab
  -- `tracedFireAllEvolve ⟨[r]⟩ seed 0 = (seed, [])`, so the events
  -- list is empty, hence `deriveCausalEdges [] = []`.
  -- `(a, b) ∈ []` is `False`.
  simp [tracedFireAllEvolve, deriveCausalEdges] at hab

/-- `PartitionClosure_step1 r h seed` is the `Prop`
`PartitionClosureUnderStep r h seed 1`. The library contains no proof
of it. -/
def PartitionClosure_step1 (r : ExecRule) (h : PartitionPreserving r)
    (seed : ExecHG ℕ) : Prop :=
  PartitionClosureUnderStep r h seed 1

/-! ## Section H: the statement `PartitionClosureTheorem` -/

/-- `PartitionClosureTheorem`: for every rule `r` with
`PartitionPreserving r`, every seed and every depth d,
`PartitionClosureUnderStep r h seed d` holds.

`partitionClosure_base` proves the case d = 0. The library contains no
proof of the inductive step. A possible argument at depth d+1 splits on
whether the consumed edge of a new event contains a fresh vertex from
some slice `freshSlice baseFresh r.numFresh m`
(`FreshVertexPartition.freshSlice_disjoint`) or is seed-only relative to
its binding (`PartitionPreserving`). This argument is not formalized. -/
def PartitionClosureTheorem : Prop :=
  ∀ (r : ExecRule) (h : PartitionPreserving r) (seed : ExecHG ℕ) (d : ℕ),
    PartitionClosureUnderStep r h seed d

/-! ## Section I: conjunction of the two instances -/

/-- `edgeReversalRule` and `doubleCycleRule_5` both satisfy
`PartitionPreserving`. -/
theorem partitionPreserving_certified :
    PartitionPreserving edgeReversalRule ∧
    PartitionPreserving doubleCycleRule_5 :=
  ⟨PartitionPreserving_edgeReversalRule,
   PartitionPreserving_doubleCycleRule_5⟩

/-! ## Contents

Theorems:

  * `seedOnly_map_indep_fresh`: the image of a seed-only RHS edge does
    not depend on the fresh offset.
  * `binding_ne_iff_exists_disagree`, `bindingExtend_apply_bound`,
    `map_mkEdgeFin_verts`: helper lemmas.
  * `PartitionPreserving_edgeReversalRule`,
    `PartitionPreserving_doubleCycleRule_5`, and their conjunction
    `partitionPreserving_certified`.
  * `partitionClosure_base`: `PartitionClosureUnderStep r h seed 0`.

Definitions: `IsSeedOnlyRhsEdge`, `bindingExtend`, `PartitionPreserving`,
`PartitionClosureUnderStep`, `PartitionClosure_step1`,
`PartitionClosureTheorem`.

Not proved: `PartitionClosureTheorem`, and `PartitionClosureUnderStep` at every depth d ≥ 1.
-/

end PartitionClosure
end InfraFormalization
