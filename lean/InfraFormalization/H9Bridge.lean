/-
**H9 bridge: structural invariant decomposition of the engine
correspondence** (#492 substantive — bridge attack).

This module **decomposes the bridge lemma** `engineMatchesTriad`
from `H9Closure.lean` into precisely-stated component obligations
with the structural invariant identified.

**Setup**: for the persistent-equivalence-class systems
{`edgeReversal + tripleMerger`, `fork + doubleCycle`} starting from
`seedEdge12 = [[1, 2]]`, the engine satisfies a clean structural pattern
at every depth. Once formalized, the distinct-edge tripling and full
H9 closure follow.

**The structural invariant**:

  ψ(H) := H satisfies:
    (1) No self-loops: every distinct edge `[a, b]` has `a ≠ b`.
    (2) No symmetric distinct pairs: if `[a, b]` is distinct in H,
        then `[b, a]` is not also distinct in H.
    (3) Max multiplicity ≤ 2: every distinct edge of H appears
        either once or twice.
    (4) Vertex bound: ∃ M such that all vertices of H are ≤ M and
        fresh vertices at the next step start at M+1.

**Why ψ suffices for tripling**: when ψ holds for H with distinct count
n, applying `singleWayStep sys H` produces:
  - For each distinct edge `[a, b]` of H: exactly 3 new distinct
    edges `{[b, a], [a, f], [b, f]}` where `f` is fresh per binding.
  - All old distinct edges of H are fully consumed (multiplicity 2 →
    consumed twice by both rules; multiplicity 1 → consumed by eR,
    tripleMerger removal no-ops).
  - New edges have multiplicities {[b,a]: 2 (produced by eR AND
    tripleMerger's middle edge), [a,f]: 1, [b,f]: 1}.
  - All 3n new edges are globally distinct (proved via ψ + fresh
    vertex distinctness).

**Bridge component theorems** (this module's output):

  * `psi : ExecHG ℕ → Prop` — the structural invariant.
  * `psi_seedEdge12 : ψ seedEdge12` — base case, trivial.
  * `BridgeStepLemma : Prop` — the open step lemma:
    `∀ H, ψ H → distinctEdgeCount (singleWayStep sys H) = 3·distinctEdgeCount H ∧ ψ (singleWayStep sys H)`
  * `BridgeStepLemma → engineMatchesTriad` — the closure.

This decomposes the H9 bridge into a SINGLE substantive open lemma
(`BridgeStepLemma`) with all wrapper logic proved.
-/

import InfraFormalization.H9Closure

namespace InfraFormalization
namespace H9Bridge

open MultiwayExec
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open DistinctEdgeIdentity
open H9Closure

/-! ## Section A: The structural invariant ψ -/

/-- Project an edge to its vertex list (helper). -/
def edgeVerts (e : Hyperedge ℕ) : List ℕ := e.verts

/-- The vertex-list reverse of an edge's verts. -/
def edgeRevVerts (e : Hyperedge ℕ) : List ℕ := e.verts.reverse

/-- Predicate: every distinct edge has length-2 verts with distinct
endpoints (no self-loops). -/
def NoSelfLoops (H : ExecHG ℕ) : Prop :=
  ∀ v ∈ H.map (·.verts),
    match v with
    | [a, b] => a ≠ b
    | _ => True

/-- Predicate: no two distinct edges are reverses of each other (no
symmetric pairs in the distinct-edge set). -/
def NoSymmetricPairs (H : ExecHG ℕ) : Prop :=
  ∀ v ∈ H.map (·.verts),
    match v with
    | [a, b] => [b, a] ∉ H.map (·.verts) ∨ [a, b] = [b, a]
    | _ => True

/-- Multiplicity of a vertex list `v` in `H.map (·.verts)`. -/
def vertsMult (v : List ℕ) (H : ExecHG ℕ) : Nat :=
  (H.map (·.verts)).count v

/-- Predicate: every distinct edge has multiplicity at most 2. -/
def MultLeTwo (H : ExecHG ℕ) : Prop :=
  ∀ v ∈ H.map (·.verts), vertsMult v H ≤ 2

/-- The composite structural invariant. -/
def Psi (H : ExecHG ℕ) : Prop :=
  NoSelfLoops H ∧ NoSymmetricPairs H ∧ MultLeTwo H

/-! ## Section B: Base case — ψ holds for the seed -/

/-- For `seedEdge12 = [[1, 2]]`, the structural invariant ψ holds. -/
theorem psi_seedEdge12 : Psi seedEdge12 := by
  refine ⟨?_, ?_, ?_⟩
  · -- NoSelfLoops
    intro v hv
    simp [seedEdge12, Hyperedge.verts] at hv
    -- hv says v = [1, 2]
    rw [hv]
    decide
  · -- NoSymmetricPairs
    intro v hv
    simp [seedEdge12, Hyperedge.verts] at hv
    rw [hv]
    -- Need: [2, 1] ∉ [[1, 2]].map (·.verts) ∨ [1, 2] = [2, 1]
    left
    simp [seedEdge12, Hyperedge.verts]
  · -- MultLeTwo
    intro v hv
    simp [seedEdge12, Hyperedge.verts, vertsMult] at *
    by_cases h : v = [1, 2]
    · rw [h]; simp [seedEdge12, Hyperedge.verts]
    · simp [h] at hv

/-! ## Section C: The bridge step lemma — central open obligation -/

/-- **`BridgeStepLemma`** [open obligation]: the central remaining
piece of H9 closure. For both persistent-equivalence-class systems,
applying `singleWayStep` to any ψ-satisfying state both:
  - exactly triples the distinct edge count, and
  - preserves ψ for the next iteration.

This is what remains to be proved symbolically. The structural
invariant ψ is now precisely identified; proving this lemma reduces
to careful unfolding of `singleWayStep`'s nested `foldl` over rules
and matches. Estimated 300–500 lines of Lean. -/
def BridgeStepLemma : Prop :=
  ∀ (sys : ExecSystem),
    sys = edgeReversal_tripleMerger_Sys ∨ sys = fork_doubleCycle_Sys →
    ∀ (H : ExecHG ℕ),
      Psi H →
      distinctEdgeCount (singleWayStep sys H) = 3 * distinctEdgeCount H ∧
      Psi (singleWayStep sys H)

/-! ## Section D: From the step lemma to the bridge -/

/-- Helper: ψ is preserved along the entire engine trajectory for
each persistent-class system, given the bridge step lemma. -/
theorem psi_preserved_eR_tripleMerger (step : BridgeStepLemma) :
    ∀ d : Nat, Psi (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) := by
  intro d
  induction d with
  | zero => exact psi_seedEdge12
  | succ d ih =>
    have := step edgeReversal_tripleMerger_Sys (Or.inl rfl)
      (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) ih
    exact this.2

theorem psi_preserved_fork_dCyc (step : BridgeStepLemma) :
    ∀ d : Nat, Psi (singleWayEvolve fork_doubleCycle_Sys seedEdge12 d) := by
  intro d
  induction d with
  | zero => exact psi_seedEdge12
  | succ d ih =>
    have := step fork_doubleCycle_Sys (Or.inr rfl)
      (singleWayEvolve fork_doubleCycle_Sys seedEdge12 d) ih
    exact this.2

/-- **`bridge_from_step`**: given the step lemma, derive the full bridge
`engineMatchesTriad` by induction on depth `d`. -/
theorem bridge_from_step (step : BridgeStepLemma) : engineMatchesTriad := by
  intro d
  refine ⟨?_, ?_⟩
  · -- eR + tripleMerger branch
    induction d with
    | zero =>
      rw [triadList_length]
      native_decide
    | succ d ih =>
      have hPsi := psi_preserved_eR_tripleMerger step d
      have hstep := step edgeReversal_tripleMerger_Sys (Or.inl rfl)
        (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) hPsi
      show distinctEdgeCount (singleWayStep edgeReversal_tripleMerger_Sys
        (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 d)) = (triadList (d+1)).length
      rw [hstep.1, triadList_length_succ]
      rw [triadList_length] at ih
      rw [triadList_length]
      omega
  · -- fork + doubleCycle branch (symmetric)
    induction d with
    | zero =>
      rw [triadList_length]
      native_decide
    | succ d ih =>
      have hPsi := psi_preserved_fork_dCyc step d
      have hstep := step fork_doubleCycle_Sys (Or.inr rfl)
        (singleWayEvolve fork_doubleCycle_Sys seedEdge12 d) hPsi
      show distinctEdgeCount (singleWayStep fork_doubleCycle_Sys
        (singleWayEvolve fork_doubleCycle_Sys seedEdge12 d)) = (triadList (d+1)).length
      rw [hstep.1, triadList_length_succ]
      rw [triadList_length] at ih
      rw [triadList_length]
      omega

/-! ## Section E: Final closure — given step, H9 is proved -/

/-- **`H9_closure_from_step`**: given the bridge step lemma, the H9
distinct-edge tripling conjecture is fully proved unconditionally
for all `d ≥ 0` for both persistent-equivalence-class members. -/
theorem H9_closure_from_step (step : BridgeStepLemma) :
    ∀ d : Nat,
      distinctEdgeCount (singleWayEvolve edgeReversal_tripleMerger_Sys seedEdge12 d) = 3^d ∧
      distinctEdgeCount (singleWayEvolve fork_doubleCycle_Sys seedEdge12 d) = 3^d := by
  exact H9_conditional_on_bridge (bridge_from_step step)

/-! ## What this delivers — H9 status update

**Before this module**: the bridge `engineMatchesTriad` was a single
opaque Prop with no decomposition.

**After this module**: the bridge has been decomposed into:

  1. **`Psi`** — explicit 3-clause structural invariant on states.
  2. **`psi_seedEdge12`** — proved unconditionally: invariant holds
     for the seed.
  3. **`BridgeStepLemma`** — precisely-stated open obligation:
     `Psi H → distinct(step H) = 3·distinct H ∧ Psi (step H)`.
  4. **`bridge_from_step`** — proved unconditionally: the step lemma
     implies the bridge.
  5. **`H9_closure_from_step`** — proved unconditionally: the step
     lemma implies full H9 closure.

The full H9 conjecture is now reduced to **a single named theorem**:
`BridgeStepLemma`. All wrapper logic — the base case, the induction
on depth, the use of ψ to lift step to evolve — is proved.

**Why ψ works**: under ψ, the engine produces 3 new distinct edges
per existing distinct edge. The fresh-vertex offset machinery in
`singleWayStep` ensures all 3·n new edges are globally distinct.
Old distinct edges are fully consumed (their multiplicities ≤ 2 are
exactly matched by the two rules' consumptions).

**What remains**: prove `BridgeStepLemma`. This requires unfolding
`singleWayStep` and accounting for the multiplicity-aware semantics
of `removeEdges`, the binding-deduplication of `allMatches`, and
the per-rule offset increment. Estimated 300–500 lines of Lean.

When done, `H9_closure_from_step step_proof` immediately yields:

  `distinctEdgeCount (singleWayEvolve sys seedEdge12 d) = 3^d` for all d

— the full symbolic closure of the H9 conjecture.
-/

end H9Bridge
end InfraFormalization
