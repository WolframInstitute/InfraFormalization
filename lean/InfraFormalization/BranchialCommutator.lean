/-
**Branchial structure theorems** (IB2, M5 SAHMED-CZAPATA).

Extends `Branchial.lean` with concrete consequences for the
SAHMED-CZAPATA axiomatic-relativity programme (M5).

Grounded: everything on `Hypergraph V` + `RewritingSystem` + `Step`.
-/

import InfraFormalization.Branchial

namespace InfraFormalization

variable {V : Type*} [DecidableEq V]
variable {P : Type*}

/-- **`BranchialRelated` is symmetric** (re-export, used by the M5
programme). -/
theorem branchialRelated_symmetric {sys : RewritingSystem P}
    {s₁ s₂ : Hypergraph V}
    (h : BranchialRelated sys s₁ s₂) : BranchialRelated sys s₂ s₁ :=
  branchial_symm sys h

/-- **BranchialRelated self iff has a predecessor**: the state is
branch-related to itself iff there is some state from which a single
step reaches it. -/
theorem branchialRelated_self_iff_has_predecessor (sys : RewritingSystem P)
    (s : Hypergraph V) :
    BranchialRelated sys s s ↔ ∃ s₀, Step sys s₀ s := by
  constructor
  · rintro ⟨s₀, h₁, _h₂⟩
    exact ⟨s₀, h₁⟩
  · intro h
    exact branchial_refl_of_has_predecessor sys h

/-- **Branchial is not transitive in general.** We state the closure
form: the transitive closure of `BranchialRelated` is the reachability
relation through shared-predecessor chains. This gives the discrete
analog of "causally-disconnected simultaneity". -/
def BranchialMultiRelated (sys : RewritingSystem P) :
    Hypergraph V → Hypergraph V → Prop :=
  Relation.ReflTransGen (BranchialRelated sys)

/-- **Reflexivity of the branchial reflexive-transitive closure**. -/
theorem branchialMultiRelated_refl (sys : RewritingSystem P)
    (s : Hypergraph V) : BranchialMultiRelated sys s s :=
  Relation.ReflTransGen.refl

/-- **Transitivity of the branchial reflexive-transitive closure**. -/
theorem branchialMultiRelated_trans {sys : RewritingSystem P}
    {s₁ s₂ s₃ : Hypergraph V}
    (h₁₂ : BranchialMultiRelated sys s₁ s₂)
    (h₂₃ : BranchialMultiRelated sys s₂ s₃) :
    BranchialMultiRelated sys s₁ s₃ :=
  Relation.ReflTransGen.trans h₁₂ h₂₃

/-- **Branchial → BranchialMulti**: a single branchial step embeds
into the multi-relation. -/
theorem branchial_implies_branchialMulti {sys : RewritingSystem P}
    {s₁ s₂ : Hypergraph V} (h : BranchialRelated sys s₁ s₂) :
    BranchialMultiRelated sys s₁ s₂ :=
  Relation.ReflTransGen.single h

/-- **BranchialMulti is symmetric.** Since `BranchialRelated` is
symmetric, so is its reflexive-transitive closure. -/
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
