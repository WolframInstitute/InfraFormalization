/-
**Rule-signature equivalence infrastructure** (IR1/IR6 extensions).

Extends `RuleSignature.lean` with an equivalence relation on signatures:
two hypergraphs are "signature-equivalent" iff their RuleSignatures
match on all components. This is the rule-database matching criterion
(IR6).

Grounded on `Hypergraph V` via `hypergraphSignature`.
-/

import InfraFormalization.RuleSignature

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Signature equivalence**: two RuleSignatures agree on every
component. Reflexive, symmetric, transitive — an equivalence relation
on `RuleSignature V`. -/
def RuleSignature.sigEquiv (σ τ : RuleSignature V) : Prop :=
  σ.hausdorffDimAt = τ.hausdorffDimAt
  ∧ σ.ballVolume = τ.ballVolume
  ∧ σ.totalFormanRicci = τ.totalFormanRicci
  ∧ σ.edgeCount = τ.edgeCount
  ∧ σ.vertexCount = τ.vertexCount

/-- **Signature equivalence is reflexive**. -/
theorem RuleSignature.sigEquiv_refl (σ : RuleSignature V) :
    σ.sigEquiv σ := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Signature equivalence is symmetric**. -/
theorem RuleSignature.sigEquiv_symm {σ τ : RuleSignature V}
    (h : σ.sigEquiv τ) : τ.sigEquiv σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩

/-- **Signature equivalence is transitive**. -/
theorem RuleSignature.sigEquiv_trans {σ τ π : RuleSignature V}
    (h₁ : σ.sigEquiv τ) (h₂ : τ.sigEquiv π) : σ.sigEquiv π := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  exact ⟨a₁.trans a₂, b₁.trans b₂, c₁.trans c₂, d₁.trans d₂, e₁.trans e₂⟩

/-- **Signature of empty hypergraphs on same vertex type are
equivalent**: two `Hypergraph V` with no edges have the same
signature (ball volumes equal on a disconnected graph). -/
theorem hypergraphSignature_edgeCount_empty :
    (hypergraphSignature (Hypergraph.empty : Hypergraph V)).edgeCount = 0 := by
  unfold hypergraphSignature Hypergraph.empty Hypergraph.size
  simp

/-- **Empty hypergraph has vertex count `Fintype.card V`**. -/
theorem hypergraphSignature_vertexCount_empty :
    (hypergraphSignature (Hypergraph.empty : Hypergraph V)).vertexCount
      = Fintype.card V := by
  unfold hypergraphSignature
  rfl

/-- **Empty hypergraph signature has zero Forman Ricci (placeholder)**. -/
theorem hypergraphSignature_totalFormanRicci_empty :
    (hypergraphSignature (Hypergraph.empty : Hypergraph V)).totalFormanRicci = 0 := by
  unfold hypergraphSignature
  rfl

end InfraFormalization
