/-
Discrete scalar fields on a hypergraph `Hypergraph V`.

**Connection to hypergraphs.** Native. A discrete scalar field is
simply a function `V → ℝ` (or `V → ℂ`) where `V` is the vertex type
of the same `Hypergraph V` that carries the Wolfram-model rewriting.
Field operations — addition, pointwise multiplication, scalar
multiplication, `ℓ²` norm, discrete `∇` and `Δ` — all factor
through the already-built machinery in `HypergraphCalculus.lean` and
`HypergraphLaplacian.lean`.

**What this file contributes.**

  * `ScalarField V := V → ℝ` — a thin alias with `AddCommGroup` /
    `Module ℝ` structure inherited from `V → ℝ`.
  * `ScalarField.norm₂ φ := √(∑_v (φ v)²)` — the `ℓ²(V)` norm.
  * `ScalarField.normSq φ := ∑_v (φ v)²` — the squared `ℓ²(V)` norm.
  * `ScalarField.innerProd φ ψ := ∑_v (φ v) · (ψ v)` — the real
    counting inner product.
  * `discreteAction H m φ dφ t` — the Klein-Gordon Lagrangian
    density at time `t` for a scalar field `(φ, dφ)` on `H` with
    mass `m`.

These are infrastructure: every wave / heat / Klein-Gordon / Schrödinger
solution constructed elsewhere is a `ScalarField`-valued function of
time, and this file lets downstream code refer to it uniformly.

Complex-valued scalar fields are handled via the real-imaginary pair
in `SchrodingerEquation.lean`; there is no separate complex wrapper
here.
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.HypergraphCalculus
import InfraFormalization.KleinGordon
import Mathlib.Analysis.InnerProductSpace.Basic

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **discrete scalar field** on a hypergraph with vertex type `V`
is simply a function `V → ℝ`. The alias tags intent and allows
downstream code to use a common name. -/
abbrev ScalarField (V : Type*) : Type _ := V → ℝ

namespace ScalarField

/-- **Squared `ℓ²(V)` norm** `‖φ‖² := ∑_v (φ v)²`. -/
noncomputable def normSq (φ : ScalarField V) : ℝ :=
  ∑ v : V, (φ v) ^ 2

/-- **`ℓ²(V)` norm** `‖φ‖ := √(∑_v (φ v)²)`. -/
noncomputable def norm₂ (φ : ScalarField V) : ℝ :=
  Real.sqrt (normSq φ)

/-- **Real counting inner product** `⟨φ, ψ⟩ := ∑_v φ(v) · ψ(v)`. -/
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

/-! ## Euclidean formulation of conservation laws

Using the `ScalarField.innerProd` abstraction, the key identities
for the hypergraph Laplacian can be restated in inner-product form.
This is the natural setting for variational principles (Lagrangians
and Euler-Lagrange equations). -/

/-- **Dirichlet form as inner product.** `⟨φ, Δ_H φ⟩ = ∑_v φ · Δ φ`. -/
theorem innerProd_laplacianHyper (H : Hypergraph V) (φ : ScalarField V) :
    ScalarField.innerProd φ (Hypergraph.laplacianHyper H φ)
    = ∑ v : V, φ v * Hypergraph.laplacianHyper H φ v := by
  rfl

/-- **Self-adjointness in inner-product form.** -/
theorem innerProd_laplacianHyper_symm (H : Hypergraph V)
    (φ ψ : ScalarField V) :
    ScalarField.innerProd φ (Hypergraph.laplacianHyper H ψ)
    = ScalarField.innerProd ψ (Hypergraph.laplacianHyper H φ) := by
  unfold ScalarField.innerProd
  exact Hypergraph.laplacianHyper_self_adjoint H φ ψ

/-- **Dirichlet non-positivity in inner-product form.** -/
theorem innerProd_laplacianHyper_nonpos (H : Hypergraph V)
    (φ : ScalarField V) :
    ScalarField.innerProd φ (Hypergraph.laplacianHyper H φ) ≤ 0 :=
  Hypergraph.laplacianHyper_dirichlet_nonpos H φ

/-! ## Klein-Gordon Lagrangian

The discrete Klein-Gordon Lagrangian at time `t` for a scalar field
`φ : ℝ → V → ℝ` with velocity `dφ : ℝ → V → ℝ` and mass `m : ℝ`:

  `L(t) := (1/2) ∑_v (dφ t v)²
            + (1/2) ∑_v φ(t,v) · Δ_H φ(t) v
            − (1/2) · m² · ∑_v (φ t v)²`.

(Kinetic term with `+` sign; gradient term expressed via the
negative-semidefinite Δ_H so the sign convention matches our
`Δ_H = A − D`.) -/

/-- **Klein-Gordon Lagrangian density** at time `t`. -/
noncomputable def discreteLagrangian (H : Hypergraph V) (m : ℝ)
    (φ dφ : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  (1/2) * (∑ v : V, (dφ t v) ^ 2)
  + (1/2) * (∑ v : V, φ t v * Hypergraph.laplacianHyper H (φ t) v)
  - (1/2) * m ^ 2 * (∑ v : V, (φ t v) ^ 2)

/-- **Total energy (Hamiltonian) of a Klein-Gordon field.**
`H = (1/2) ∑ (dφ)² − (1/2) ∑ φ·Δφ + (1/2) m² ∑ φ²`.

This is `(1/2)` times `kleinGordonEnergy` (a factor-of-2 convention
difference); both are conserved along solutions. The `(1/2)` here
matches the Legendre-transform `H = π·(dφ) − L` when `π = dφ`. -/
noncomputable def discreteHamiltonian (H : Hypergraph V) (m : ℝ)
    (φ dφ : ℝ → V → ℝ) (t : ℝ) : ℝ :=
  (1/2) * (∑ v : V, (dφ t v) ^ 2)
  - (1/2) * (∑ v : V, φ t v * Hypergraph.laplacianHyper H (φ t) v)
  + (1/2) * m ^ 2 * (∑ v : V, (φ t v) ^ 2)

/-- **Legendre-transform identity.** `H = π·(dφ) − L` with
`π = dφ` (conjugate momentum of a standard kinetic term):

  `discreteHamiltonian = ∑ (dφ)² − discreteLagrangian`. -/
theorem discreteHamiltonian_eq_legendre
    (H : Hypergraph V) (m : ℝ) (φ dφ : ℝ → V → ℝ) (t : ℝ) :
    discreteHamiltonian H m φ dφ t
    = (∑ v : V, (dφ t v)^2) - discreteLagrangian H m φ dφ t := by
  unfold discreteHamiltonian discreteLagrangian
  ring

/-! ## Variational / Euler-Lagrange content

The **variational derivative** of the Dirichlet form
`F(φ) := ⟨φ, Δ_H φ⟩` is the map `φ ↦ 2·Δ_H φ`, as follows from
self-adjointness of `Δ_H`: for any perturbation `η`,

  `F(φ + εη) − F(φ) = ε · (⟨η, Δφ⟩ + ⟨φ, Δη⟩) + O(ε²)
                    = ε · 2 ⟨η, Δφ⟩`.

This gives the `∂L/∂φ` for the Klein-Gordon Lagrangian and is the
formal origin of the Euler-Lagrange reduction to Klein-Gordon. -/

/-- **Variational-derivative identity for the Dirichlet form.** The
first-order variation of `∑_v φ(v) · Δ_H φ(v)` under `φ → φ + εη`
equals `2ε · ⟨η, Δ_H φ⟩ + O(ε²)`, captured here by the identity

  `⟨η, Δφ⟩ + ⟨φ, Δη⟩ = 2 · ⟨η, Δφ⟩`. -/
theorem variational_dirichlet (H : Hypergraph V)
    (φ η : ScalarField V) :
    ScalarField.innerProd η (Hypergraph.laplacianHyper H φ)
    + ScalarField.innerProd φ (Hypergraph.laplacianHyper H η)
    = 2 * ScalarField.innerProd η (Hypergraph.laplacianHyper H φ) := by
  unfold ScalarField.innerProd
  have h := Hypergraph.laplacianHyper_self_adjoint H φ η
  linarith

/-- **Euler-Lagrange equation for the discrete Klein-Gordon Lagrangian.**
A pair `(φ, dφ)` with `φ : ℝ → V → ℝ` satisfies the EL condition if
`dφ = ∂_t φ` and `d/dt (∂L/∂(dφ)) = ∂L/∂φ`, i.e.,

  `dφ'(t, v) = Δ_H φ(t) v − m² · φ(t, v)`.

For the Klein-Gordon Lagrangian:
  `∂L/∂(dφ(v)) = dφ(v)`   (direct)
  `∂L/∂φ(v)   = Δ_H φ(v) − m² φ(v)` (via `variational_dirichlet`).

So `d/dt dφ(v) = Δ_H φ(v) − m² φ(v)`. -/
def KG_EulerLagrange (H : Hypergraph V) (m : ℝ) (φ dφ : ℝ → V → ℝ) : Prop :=
  (∀ t v, HasDerivAt (fun s => φ s v) (dφ t v) t) ∧
  (∀ t v, HasDerivAt (fun s => dφ s v)
    (Hypergraph.laplacianHyper H (φ t) v - m ^ 2 * φ t v) t)

/-- **EL equation is KG equation.** The Euler-Lagrange condition
for the discrete Klein-Gordon Lagrangian is literally the
`KleinGordonSolution` structure — by the variational derivatives
computed above. -/
theorem KG_EulerLagrange_iff_KleinGordonSolution (H : Hypergraph V) (m : ℝ)
    (φ dφ : ℝ → V → ℝ) :
    KG_EulerLagrange H m φ dφ ↔ KleinGordonSolution H m φ dφ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact { position := h1, velocity := h2 }
  · intro h
    exact ⟨h.position, h.velocity⟩

end InfraFormalization
