/-
Elementary properties of `BranchialRelated` and its closure.

This module proves that `BranchialRelated` is symmetric, that a state is
related to itself exactly when it has a one-step predecessor, and defines
the reflexive-transitive closure `BranchialMultiRelated`, which it proves
reflexive, transitive and symmetric.
-/

import InfraFormalization.Branchial

namespace InfraFormalization

variable {V : Type*} [DecidableEq V]
variable {P : Type*}

/-- `BranchialRelated` is symmetric. -/
theorem branchialRelated_symmetric {sys : RewritingSystem P}
    {s₁ s₂ : Hypergraph V}
    (h : BranchialRelated sys s₁ s₂) : BranchialRelated sys s₂ s₁ :=
  branchial_symm sys h

/-- A state is branchially related to itself if and only if some state
reaches it in one step. -/
theorem branchialRelated_self_iff_has_predecessor (sys : RewritingSystem P)
    (s : Hypergraph V) :
    BranchialRelated sys s s ↔ ∃ s₀, Step sys s₀ s := by
  constructor
  · rintro ⟨s₀, h₁, _h₂⟩
    exact ⟨s₀, h₁⟩
  · intro h
    exact branchial_refl_of_has_predecessor sys h

/-- The reflexive-transitive closure of `BranchialRelated`. -/
def BranchialMultiRelated (sys : RewritingSystem P) :
    Hypergraph V → Hypergraph V → Prop :=
  Relation.ReflTransGen (BranchialRelated sys)

/-- `BranchialMultiRelated` is reflexive. -/
theorem branchialMultiRelated_refl (sys : RewritingSystem P)
    (s : Hypergraph V) : BranchialMultiRelated sys s s :=
  Relation.ReflTransGen.refl

/-- `BranchialMultiRelated` is transitive. -/
theorem branchialMultiRelated_trans {sys : RewritingSystem P}
    {s₁ s₂ s₃ : Hypergraph V}
    (h₁₂ : BranchialMultiRelated sys s₁ s₂)
    (h₂₃ : BranchialMultiRelated sys s₂ s₃) :
    BranchialMultiRelated sys s₁ s₃ :=
  Relation.ReflTransGen.trans h₁₂ h₂₃

/-- `BranchialRelated` implies `BranchialMultiRelated`. -/
theorem branchial_implies_branchialMulti {sys : RewritingSystem P}
    {s₁ s₂ : Hypergraph V} (h : BranchialRelated sys s₁ s₂) :
    BranchialMultiRelated sys s₁ s₂ :=
  Relation.ReflTransGen.single h

/-- `BranchialMultiRelated` is symmetric. -/
theorem branchialMultiRelated_symm {sys : RewritingSystem P}
    {s₁ s₂ : Hypergraph V} (h : BranchialMultiRelated sys s₁ s₂) :
    BranchialMultiRelated sys s₂ s₁ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    -- ih : BranchialMultiRelated sys s₂ b, hbc : BranchialRelated sys b c.
    -- Need: BranchialMultiRelated sys c s₁.
    -- Use symmetry of hbc, then tail with ih.
    exact Relation.ReflTransGen.head (branchial_symm sys hbc) ih

end InfraFormalization
