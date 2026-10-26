/-
Real scalar fields on the vertices of a hypergraph.

This module defines `ScalarField V := V → ℝ` with the squared ℓ² norm, the
ℓ² norm and the inner product `∑_v φ v · ψ v`, and proves the basic
properties of the inner product. It restates the self-adjointness and
nonpositivity of `Hypergraph.laplacianHyper` in inner-product form,
defines the discrete Klein-Gordon Lagrangian and Hamiltonian with the
Legendre identity between them, and proves that the Euler-Lagrange
predicate `KG_EulerLagrange` is equivalent to `KleinGordonSolution`.
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.HypergraphCalculus
import InfraFormalization.KleinGordon
import Mathlib.Analysis.InnerProductSpace.Basic

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A function `V → ℝ`. -/
abbrev ScalarField (V : Type*) : Type _ := V → ℝ

namespace ScalarField

/-- `∑_v (φ v)²`. -/
noncomputable def normSq (φ : ScalarField V) : ℝ :=
  ∑ v : V, (φ v) ^ 2

/-- `√(∑_v (φ v)²)`. -/
noncomputable def norm₂ (φ : ScalarField V) : ℝ :=
  Real.sqrt (normSq φ)

/-- `∑_v φ v · ψ v`. -/
noncomputable def innerProd (φ ψ : ScalarField V) : ℝ :=
  ∑ v : V, (φ v) * (ψ v)

theorem normSq_nonneg (φ : ScalarField V) : 0 ≤ normSq φ := by
  unfold normSq
  apply Finset.sum_nonneg
  intros v _
  exact sq_nonneg _

theorem norm₂_nonneg (φ : ScalarField V) : 0 ≤ norm₂ φ :=
  Real.sqrt_nonneg _

theorem innerProd_symm (φ ψ : ScalarField V) :
    innerProd φ ψ = innerProd ψ φ := by
  unfold innerProd
  apply Finset.sum_congr rfl
  intros v _
  ring

theorem innerProd_self (φ : ScalarField V) :
    innerProd φ φ = normSq φ := by
  unfold innerProd normSq
  apply Finset.sum_congr rfl
  intros v _
  ring

theorem innerProd_add_left (φ₁ φ₂ ψ : ScalarField V) :
    innerProd (fun v => φ₁ v + φ₂ v) ψ
    = innerProd φ₁ ψ + innerProd φ₂ ψ := by
  unfold innerProd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros v _
  ring

theorem innerProd_smul_left (c : ℝ) (φ ψ : ScalarField V) :
    innerProd (fun v => c * φ v) ψ = c * innerProd φ ψ := by
  unfold innerProd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros v _
  ring

end ScalarField

/-! ## The hypergraph Laplacian in inner-product form -/

/-- `⟨φ, Δ_H φ⟩ = ∑_v φ v · Δ_H φ v`, by definition. -/
theorem innerProd_laplacianHyper (H : Hypergraph V) (φ : ScalarField V) :
    ScalarField.innerProd φ (Hypergraph.laplacianHyper H φ)
    = ∑ v : V, φ v * Hypergraph.laplacianHyper H φ v := by
  rfl

/-- `⟨φ, Δ_H ψ⟩ = ⟨ψ, Δ_H φ⟩`. -/
theorem innerProd_laplacianHyper_symm (H : Hypergraph V)
    (φ ψ : ScalarField V) :
    ScalarField.innerProd φ (Hypergraph.laplacianHyper H ψ)
    = ScalarField.innerProd ψ (Hypergraph.laplacianHyper H φ) := by
  unfold ScalarField.innerProd
  exact Hypergraph.laplacianHyper_self_adjoint H φ ψ

/-- `⟨φ, Δ_H φ⟩ ≤ 0`. -/
theorem innerProd_laplacianHyper_nonpos (H : Hypergraph V)
    (φ : ScalarField V) :
    ScalarField.innerProd φ (Hypergraph.laplacianHyper H φ) ≤ 0 :=
  Hypergraph.laplacianHyper_dirichlet_nonpos H φ

/-! ## Klein-Gordon Lagrangian and Hamiltonian -/

/-- `L(t) = (1/2) ∑_v (dφ t v)² + (1/2) ∑_v φ(t,v) · Δ_H φ(t) v
− (1/2) m² ∑_v (φ t v)²`. -/
noncomputable def discreteLagrangian (H : Hypergraph V) (m : ℝ)
    (φ dφ : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  (1/2) * (∑ v : V, (dφ t v) ^ 2)
  + (1/2) * (∑ v : V, φ t v * Hypergraph.laplacianHyper H (φ t) v)
  - (1/2) * m ^ 2 * (∑ v : V, (φ t v) ^ 2)

/-- `(1/2) ∑ (dφ)² − (1/2) ∑ φ · Δ_H φ + (1/2) m² ∑ φ²`, which is half of
`kleinGordonEnergy`. -/
noncomputable def discreteHamiltonian (H : Hypergraph V) (m : ℝ)
    (φ dφ : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  (1/2) * (∑ v : V, (dφ t v) ^ 2)
  - (1/2) * (∑ v : V, φ t v * Hypergraph.laplacianHyper H (φ t) v)
  + (1/2) * m ^ 2 * (∑ v : V, (φ t v) ^ 2)

/-- `discreteHamiltonian = ∑ (dφ)² − discreteLagrangian`. -/
theorem discreteHamiltonian_eq_legendre
    (H : Hypergraph V) (m : ℝ) (φ dφ : ℝ → V → ℝ) (t : ℝ) :
    discreteHamiltonian H m φ dφ t
    = (∑ v : V, (dφ t v)^2) - discreteLagrangian H m φ dφ t := by
  unfold discreteHamiltonian discreteLagrangian
  ring

/-! ## First variation of the Dirichlet form -/

/-- `⟨η, Δ_H φ⟩ + ⟨φ, Δ_H η⟩ = 2 ⟨η, Δ_H φ⟩`, the first-order term of
`⟨φ + εη, Δ_H (φ + εη)⟩ − ⟨φ, Δ_H φ⟩` divided by `ε`. -/
theorem variational_dirichlet (H : Hypergraph V)
    (φ η : ScalarField V) :
    ScalarField.innerProd η (Hypergraph.laplacianHyper H φ)
    + ScalarField.innerProd φ (Hypergraph.laplacianHyper H η)
    = 2 * ScalarField.innerProd η (Hypergraph.laplacianHyper H φ) := by
  unfold ScalarField.innerProd
  have h := Hypergraph.laplacianHyper_self_adjoint H φ η
  linarith

/-- `∂_t φ = dφ` and `∂_t dφ = Δ_H φ − m² φ` at every time and vertex. -/
def KG_EulerLagrange (H : Hypergraph V) (m : ℝ) (φ dφ : ℝ → V → ℝ) : Prop :=
  (∀ t v, HasDerivAt (fun s => φ s v) (dφ t v) t) ∧
  (∀ t v, HasDerivAt (fun s => dφ s v)
    (Hypergraph.laplacianHyper H (φ t) v - m ^ 2 * φ t v) t)

/-- `KG_EulerLagrange H m φ dφ` is equivalent to
`KleinGordonSolution H m φ dφ`; the two have the same fields. -/
theorem KG_EulerLagrange_iff_KleinGordonSolution (H : Hypergraph V) (m : ℝ)
    (φ dφ : ℝ → V → ℝ) :
    KG_EulerLagrange H m φ dφ ↔ KleinGordonSolution H m φ dφ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact { position := h1, velocity := h2 }
  · intro h
    exact ⟨h.position, h.velocity⟩

end InfraFormalization
