/-
Conservation of small rules.

The module makes `Rule.IsConservative` (`|LHS| = |RHS|`) decidable and defines five rules: the rule
with empty sides, a self-map of one edge, edge duplication, a three-edges-to-one rule and a
two-edges-to-triangle rule. It computes their left- and right-hand sizes and states which are
conservative. It defines two catalogs, `conservativeCatalog` and `nonConservativeCatalog`, and the predicate
`Rule.GrowthCompatible r := ¬ r.IsConservative`.
-/

import InfraFormalization.CandidateRuleDatabase
import InfraFormalization.StructuralRuleBounds

namespace InfraFormalization

/-! ## Decidable conservation check -/

instance Rule.instDecidableIsConservative {P : Type*} (r : Rule P) :
    Decidable r.IsConservative :=
  Nat.decEq r.lhsSize r.rhsSize

/-- `true` iff `|LHS| = |RHS|`. -/
def Rule.passesConservationScreen {P : Type*} (r : Rule P) : Bool :=
  decide r.IsConservative

theorem Rule.passesConservationScreen_iff {P : Type*} (r : Rule P) :
    r.passesConservationScreen = true ↔ r.IsConservative := by
  unfold Rule.passesConservationScreen
  simp

/-! ## Rules over `Fin 2` and `Fin 3` -/

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

/-- `{(0,1)} → {(0,1), (0,1)}`. `|LHS| = 1`, `|RHS| = 2`. -/
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

/-- `edgeDuplicateRule` is not conservative. -/
theorem edgeDuplicateRule_not_conservative :
    ¬ edgeDuplicateRule.IsConservative := by
  unfold Rule.IsConservative
  rw [edgeDuplicateRule_lhsSize, edgeDuplicateRule_rhsSize]
  decide

/-- `{(0,1), (0,1), (0,1)} → {(0,1)}`. `|LHS| = 3`, `|RHS| = 1`. -/
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

/-- `{(0,1)} → {(0,1)}`. `|LHS| = |RHS| = 1`. -/
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

/-- A two-vertex hyperedge over `Fin 3`. -/
private def ternaryEdge (p₁ p₂ : Fin 3) : Hyperedge (Fin 3) :=
  ⟨[p₁, p₂], by simp⟩

/-- `{(0,1), (1,2)} → {(0,1), (1,2), (2,0)}`. `|LHS| = 2`, `|RHS| = 3`. -/
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

/-! ## The rule with empty left- and right-hand sides -/

/-- The rule with empty left-hand side and empty right-hand side. -/
def identityRule (P : Type) : Rule P :=
  { lhs := Hypergraph.empty, rhs := Hypergraph.empty }

@[simp] theorem identityRule_lhsSize (P : Type) :
    (identityRule P).lhsSize = 0 := by
  unfold identityRule Rule.lhsSize Hypergraph.empty Hypergraph.size
  simp

@[simp] theorem identityRule_rhsSize (P : Type) :
    (identityRule P).rhsSize = 0 := by
  unfold identityRule Rule.rhsSize Hypergraph.empty Hypergraph.size
  simp

/-- `identityRule P` has |LHS| = |RHS| = 0. -/
theorem identityRule_isConservative (P : Type) :
    (identityRule P).IsConservative := by
  show (identityRule P).lhsSize = (identityRule P).rhsSize
  rw [identityRule_lhsSize, identityRule_rhsSize]

/-! ## Catalogs -/

/-- The conservative rules `identityRule (Fin 2)` and `selfMapRule`. -/
noncomputable def conservativeCatalog : List (Rule (Fin 2)) :=
  [identityRule (Fin 2), selfMapRule]

/-- The non-conservative rules `edgeDuplicateRule` and `tripleToEdgeRule`. -/
noncomputable def nonConservativeCatalog : List (Rule (Fin 2)) :=
  [edgeDuplicateRule, tripleToEdgeRule]

/-! ## Conservation of the catalogs -/

/-- Every rule in `conservativeCatalog` is conservative. -/
theorem conservativeCatalog_all_conservative :
    ∀ r ∈ conservativeCatalog, r.IsConservative := by
  intro r hr
  unfold conservativeCatalog at hr
  simp at hr
  rcases hr with h | h
  · rw [h]; exact identityRule_isConservative (Fin 2)
  · rw [h]; exact selfMapRule_isConservative

/-- No rule in `nonConservativeCatalog` is conservative. -/
theorem nonConservativeCatalog_all_non_conservative :
    ∀ r ∈ nonConservativeCatalog, ¬ r.IsConservative := by
  intro r hr
  unfold nonConservativeCatalog at hr
  simp at hr
  rcases hr with h | h
  · rw [h]; exact edgeDuplicateRule_not_conservative
  · rw [h]; exact tripleToEdgeRule_not_conservative

/-! ## `Rule.GrowthCompatible`

`Rule.GrowthCompatible r` is defined as `¬ r.IsConservative`. -/

/-- `r` is not conservative. -/
def Rule.GrowthCompatible {P : Type*} (r : Rule P) : Prop :=
  ¬ r.IsConservative

/-- Every rule in `nonConservativeCatalog` satisfies `GrowthCompatible`. -/
theorem nonConservativeCatalog_growth_compatible :
    ∀ r ∈ nonConservativeCatalog, r.GrowthCompatible := by
  intro r hr
  exact nonConservativeCatalog_all_non_conservative r hr

/-- No rule in `conservativeCatalog` satisfies `GrowthCompatible`. -/
theorem conservativeCatalog_not_growth_compatible :
    ∀ r ∈ conservativeCatalog, ¬ r.GrowthCompatible := by
  intro r hr hgc
  exact hgc (conservativeCatalog_all_conservative r hr)

end InfraFormalization
