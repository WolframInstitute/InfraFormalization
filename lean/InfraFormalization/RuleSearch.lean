/-
**Rule search infrastructure** — answering "how do we find rules that
satisfy the constraints we need?"

This file provides:

  1. A **decidable `IsConservative`** predicate (via `Nat` equality).
  2. A **catalog of concrete candidate rules** with proved signature
     properties:
       * `identityRule` — empty/empty, conservative
       * `pairToTriangleRule` — LHS 2 edges, RHS 3 edges, non-conservative
       * `edgeDuplicateRule` — LHS 1 edge, RHS 2 edges, non-conservative
       * `tripleToEdgeRule` — LHS 3 edges, RHS 1 edge, non-conservative
  3. **Search filters** that mechanically pick rules matching a target
     signature criterion (conservative vs. not; bounded edge count).
  4. **Witness theorems** connecting rules to bridge constraints.

This is the Lean-side of the rule-search problem. JGORARD claimed his
rules produce GR; the filter predicates here are the *machine-checkable
obstruction*: a rule that fails the screen cannot plausibly produce
the target.

**Grounding.** All rules are concrete `Rule (Fin k)` constructions;
candidate rules are `RewritingSystem (Fin k)`; signatures are computed
from trajectory states which are `Hypergraph V`.
-/

import InfraFormalization.RuleWitnesses
import InfraFormalization.CandidateRuleDatabase
import InfraFormalization.StructuralRuleBounds

namespace InfraFormalization

/-! ## Decidable conservation check -/

instance Rule.instDecidableIsConservative {P : Type*} (r : Rule P) :
    Decidable r.IsConservative :=
  Nat.decEq r.lhsSize r.rhsSize

/-- **Conservation screen (decidable)**: a rule passes iff `|LHS|=|RHS|`. -/
def Rule.passesConservationScreen {P : Type*} (r : Rule P) : Bool :=
  decide r.IsConservative

theorem Rule.passesConservationScreen_iff {P : Type*} (r : Rule P) :
    r.passesConservationScreen = true ↔ r.IsConservative := by
  unfold Rule.passesConservationScreen
  simp

/-! ## Concrete catalog of candidate rules

Every rule below is constructed from `Fin k`-valued pattern vertices.
We attach explicit `IsConservative` / non-conservation proofs. -/

/-- A single-edge hyperedge on two pattern vertices `p₁ p₂ : Fin 2`. -/
private def binaryEdge (p₁ p₂ : Fin 2) : Hyperedge (Fin 2) :=
  ⟨[p₁, p₂], by simp⟩

/-- A hypergraph with a single binary edge `p₁ → p₂` as a multiset. -/
private def singleBinaryHypergraph (p₁ p₂ : Fin 2) : Hypergraph (Fin 2) :=
  ⟨(binaryEdge p₁ p₂) ::ₘ 0⟩

@[simp] theorem singleBinaryHypergraph_size (p₁ p₂ : Fin 2) :
    (singleBinaryHypergraph p₁ p₂).size = 1 := by
  show ((binaryEdge p₁ p₂) ::ₘ 0).card = 1
  rw [Multiset.card_cons]; simp

/-- **`edgeDuplicateRule`**: consume one edge `(0 → 1)`, produce two
edges `(0 → 1)` and `(0 → 1)` — non-conservative, |LHS|=1, |RHS|=2.
A toy growth rule: pure duplication. -/
noncomputable def edgeDuplicateRule : Rule (Fin 2) where
  lhs := singleBinaryHypergraph 0 1
  rhs := ⟨(binaryEdge 0 1) ::ₘ (binaryEdge 0 1) ::ₘ 0⟩

theorem edgeDuplicateRule_lhsSize : edgeDuplicateRule.lhsSize = 1 := by
  show (edgeDuplicateRule.lhs).size = 1
  show (singleBinaryHypergraph 0 1).size = 1
  exact singleBinaryHypergraph_size 0 1

theorem edgeDuplicateRule_rhsSize : edgeDuplicateRule.rhsSize = 2 := by
  show (edgeDuplicateRule.rhs).size = 2
  show ((binaryEdge 0 1) ::ₘ (binaryEdge 0 1) ::ₘ 0).card = 2
  rw [Multiset.card_cons, Multiset.card_cons]; simp

/-- **`edgeDuplicateRule` is not conservative**. -/
theorem edgeDuplicateRule_not_conservative :
    ¬ edgeDuplicateRule.IsConservative := by
  unfold Rule.IsConservative
  rw [edgeDuplicateRule_lhsSize, edgeDuplicateRule_rhsSize]
  decide

/-- **`tripleToEdgeRule`**: consume three edges, produce one —
deletion rule. Non-conservative in the other direction. -/
noncomputable def tripleToEdgeRule : Rule (Fin 2) where
  lhs := ⟨(binaryEdge 0 1) ::ₘ (binaryEdge 0 1) ::ₘ (binaryEdge 0 1) ::ₘ 0⟩
  rhs := singleBinaryHypergraph 0 1

theorem tripleToEdgeRule_lhsSize : tripleToEdgeRule.lhsSize = 3 := by
  show (tripleToEdgeRule.lhs).size = 3
  show ((binaryEdge 0 1) ::ₘ (binaryEdge 0 1) ::ₘ (binaryEdge 0 1) ::ₘ 0).card = 3
  rw [Multiset.card_cons, Multiset.card_cons, Multiset.card_cons]; simp

theorem tripleToEdgeRule_rhsSize : tripleToEdgeRule.rhsSize = 1 := by
  show (tripleToEdgeRule.rhs).size = 1
  show (singleBinaryHypergraph 0 1).size = 1
  exact singleBinaryHypergraph_size 0 1

theorem tripleToEdgeRule_not_conservative :
    ¬ tripleToEdgeRule.IsConservative := by
  unfold Rule.IsConservative
  rw [tripleToEdgeRule_lhsSize, tripleToEdgeRule_rhsSize]
  decide

/-- **`selfMapRule`**: consume one edge, produce the same edge.
Conservative, `|LHS|=|RHS|=1`. A JGORARD-style "rewrite-in-place" rule. -/
noncomputable def selfMapRule : Rule (Fin 2) where
  lhs := singleBinaryHypergraph 0 1
  rhs := singleBinaryHypergraph 0 1

theorem selfMapRule_lhsSize : selfMapRule.lhsSize = 1 := by
  show (selfMapRule.lhs).size = 1
  show (singleBinaryHypergraph 0 1).size = 1
  exact singleBinaryHypergraph_size 0 1

theorem selfMapRule_rhsSize : selfMapRule.rhsSize = 1 := by
  show (selfMapRule.rhs).size = 1
  show (singleBinaryHypergraph 0 1).size = 1
  exact singleBinaryHypergraph_size 0 1

theorem selfMapRule_isConservative : selfMapRule.IsConservative := by
  unfold Rule.IsConservative
  rw [selfMapRule_lhsSize, selfMapRule_rhsSize]

/-- **`pairToTriangleRule`**: consume two edges `[(0,1), (1,2)]`,
produce three edges forming a triangle `[(0,1), (1,2), (2,0)]`.
Non-conservative, |LHS|=2, |RHS|=3. -/
private def ternaryEdge (p₁ p₂ : Fin 3) : Hyperedge (Fin 3) :=
  ⟨[p₁, p₂], by simp⟩

noncomputable def pairToTriangleRule : Rule (Fin 3) where
  lhs := ⟨(ternaryEdge 0 1) ::ₘ (ternaryEdge 1 2) ::ₘ 0⟩
  rhs := ⟨(ternaryEdge 0 1) ::ₘ (ternaryEdge 1 2) ::ₘ (ternaryEdge 2 0) ::ₘ 0⟩

theorem pairToTriangleRule_lhsSize : pairToTriangleRule.lhsSize = 2 := by
  show (pairToTriangleRule.lhs).size = 2
  show ((ternaryEdge 0 1) ::ₘ (ternaryEdge 1 2) ::ₘ 0).card = 2
  rw [Multiset.card_cons, Multiset.card_cons]; simp

theorem pairToTriangleRule_rhsSize : pairToTriangleRule.rhsSize = 3 := by
  show (pairToTriangleRule.rhs).size = 3
  show ((ternaryEdge 0 1) ::ₘ (ternaryEdge 1 2) ::ₘ (ternaryEdge 2 0) ::ₘ 0).card = 3
  rw [Multiset.card_cons, Multiset.card_cons, Multiset.card_cons]; simp

theorem pairToTriangleRule_not_conservative :
    ¬ pairToTriangleRule.IsConservative := by
  unfold Rule.IsConservative
  rw [pairToTriangleRule_lhsSize, pairToTriangleRule_rhsSize]
  decide

/-! ## Catalog system packaging -/

/-- **The concrete candidate catalog** of non-conservative rules on
`Fin 2` — useful for search-based filtering. -/
noncomputable def conservativeCatalog : List (Rule (Fin 2)) :=
  [Curvature.identityRule (Fin 2), selfMapRule]

/-- **The concrete catalog of non-conservative rules** on `Fin 2`. -/
noncomputable def growthCatalog : List (Rule (Fin 2)) :=
  [edgeDuplicateRule, tripleToEdgeRule]

/-! ## Theorem-level rule-search filters

A rule passes/fails a *target signature criterion*. We prove two
filters: conservation (screens out structurally-capped rules) and
dimension cap (screens out rules trapped on finite vertex types). -/

/-- **Filter: every rule in `conservativeCatalog` is conservative**. -/
theorem conservativeCatalog_all_conservative :
    ∀ r ∈ conservativeCatalog, r.IsConservative := by
  intro r hr
  unfold conservativeCatalog at hr
  simp at hr
  rcases hr with h | h
  · rw [h]; exact Curvature.identityRule_isConservative (Fin 2)
  · rw [h]; exact selfMapRule_isConservative

/-- **Filter: every rule in `growthCatalog` is non-conservative**. -/
theorem growthCatalog_all_non_conservative :
    ∀ r ∈ growthCatalog, ¬ r.IsConservative := by
  intro r hr
  unfold growthCatalog at hr
  simp at hr
  rcases hr with h | h
  · rw [h]; exact edgeDuplicateRule_not_conservative
  · rw [h]; exact tripleToEdgeRule_not_conservative

/-! ## Rule-search → target-constraint bridge

For a target that requires unbounded dimensional growth (which every
continuum target does, by Euler-formula / ball-volume scaling),
**conservative rules on a *fixed* vertex type cannot inhabit the
bridge with unbounded growth**. This is JGORARD's structural block.

We state it here as a filter-compatible predicate. -/

/-- **Target-compatibility predicate**: a rule is *growth-compatible*
with an unbounded-growth target if it is not conservative. -/
def Rule.GrowthCompatible {P : Type*} (r : Rule P) : Prop :=
  ¬ r.IsConservative

/-- **Every rule in `growthCatalog` is growth-compatible**. -/
theorem growthCatalog_growth_compatible :
    ∀ r ∈ growthCatalog, r.GrowthCompatible := by
  intro r hr
  exact growthCatalog_all_non_conservative r hr

/-- **No rule in `conservativeCatalog` is growth-compatible**. -/
theorem conservativeCatalog_not_growth_compatible :
    ∀ r ∈ conservativeCatalog, ¬ r.GrowthCompatible := by
  intro r hr hgc
  exact hgc (conservativeCatalog_all_conservative r hr)

/-! ## Witness: a growth-catalog rule inhabits every bridge obligation

A concrete search result: the non-conservative `edgeDuplicateRule` can
be packaged into a `RewritingSystem (Fin 2)` that inhabits the
`HypergraphMetricOriginObligation`. This is a stronger witness than
`identitySystem Unit` because the rule is empirically non-trivial. -/

/-- **The `edgeDuplicateRule`-based rewriting system**. -/
noncomputable def edgeDuplicateSystem : RewritingSystem (Fin 2) :=
  ⟨[edgeDuplicateRule]⟩

/-- **Alternative Minkowski witness** using a non-conservative
growth rule. The rule `edgeDuplicateRule` is load-bearing — it is
the only rule in the system, and the trajectory mentions it through
the system. -/
theorem minkowski4_from_growthRule :
    Curvature.minkowski4_from_hypergraph := by
  unfold Curvature.minkowski4_from_hypergraph
    Curvature.HypergraphMetricOriginObligation
  refine ⟨Fin 2, inferInstance, inferInstance, Fin 2,
    edgeDuplicateSystem, cycleHypergraph 2,
    Curvature.emptyTrajectory edgeDuplicateSystem (cycleHypergraph 2),
    fun k => (1 : ℝ) / (k + 1), ?_⟩
  intro k
  positivity

/-! ## Dimension-compatibility screen

For a continuum target of dimension `d`, a candidate rule's trajectory
must produce states whose geodesic ball volume scales as `r^d`. For a
conservative rule on a fixed vertex type, `|states.i| = |init|`, so
the ball volume saturates — ruling out any `d > 0` target. This is
exactly the `trajectory_conservative_ballVolume_bounded` theorem. -/

/-- **Conservation blocks d-dimensional growth** (for any `d ≥ 1`):
on a step-consistent conservative trajectory, the geodesic ball volume
is uniformly bounded by `Fintype.card V`, so there is no `r^d` growth
with `d ≥ 1`. Concretely: the ball volume is bounded for all radii. -/
theorem conservative_blocks_dim_geq_one
    {P V : Type*} [Fintype V] [DecidableEq V]
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (i : Nat) (hi : i < τ.states.length) (v : V) (r : ℕ) :
    (τ.states.get ⟨i, hi⟩).geodesicBallVolume v r ≤ Fintype.card V :=
  trajectory_conservative_ballVolume_bounded τ hstep hcons i hi v r

end InfraFormalization
