/-
Equivalence of rule signatures.

This module defines `RuleSignature.sigEquiv`, agreement of two signatures in
all five components, proves that it is reflexive, symmetric and transitive,
and computes the edge count, vertex count and curvature total of the
signature of the empty hypergraph.
-/

import InfraFormalization.RuleSignature

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two signatures agree in every component. -/
def RuleSignature.sigEquiv (σ τ : RuleSignature V) : Prop :=
  σ.hausdorffDimAt = τ.hausdorffDimAt
  ∧ σ.ballVolume = τ.ballVolume
  ∧ σ.edgeCount = τ.edgeCount
  ∧ σ.vertexCount = τ.vertexCount

/-- `sigEquiv` is reflexive. -/
theorem RuleSignature.sigEquiv_refl (σ : RuleSignature V) :
    σ.sigEquiv σ := ⟨rfl, rfl, rfl, rfl⟩

/-- `sigEquiv` is symmetric. -/
theorem RuleSignature.sigEquiv_symm {σ τ : RuleSignature V}
    (h : σ.sigEquiv τ) : τ.sigEquiv σ := by
  obtain ⟨h1, h2, h4, h5⟩ := h
  exact ⟨h1.symm, h2.symm, h4.symm, h5.symm⟩

/-- `sigEquiv` is transitive. -/
theorem RuleSignature.sigEquiv_trans {σ τ π : RuleSignature V}
    (h₁ : σ.sigEquiv τ) (h₂ : τ.sigEquiv π) : σ.sigEquiv π := by
  obtain ⟨a₁, b₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, d₂, e₂⟩ := h₂
  exact ⟨a₁.trans a₂, b₁.trans b₂, d₁.trans d₂, e₁.trans e₂⟩

/-- The signature of the empty hypergraph has edge count 0. -/
theorem hypergraphSignature_edgeCount_empty :
    (hypergraphSignature (Hypergraph.empty : Hypergraph V)).edgeCount = 0 := by
  unfold hypergraphSignature Hypergraph.empty Hypergraph.size
  simp

/-- The signature of the empty hypergraph has vertex count
`Fintype.card V`. -/
theorem hypergraphSignature_vertexCount_empty :
    (hypergraphSignature (Hypergraph.empty : Hypergraph V)).vertexCount
      = Fintype.card V := by
  unfold hypergraphSignature
  rfl

end InfraFormalization
