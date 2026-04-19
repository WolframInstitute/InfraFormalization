/-
Discrete calculus on a finite vertex type with a symmetric
neighbourhood relation: graph Laplacian, inner product, linearity.

**Rung 1 of the bridge ladder** (see `BRIDGE_MACHINERY.md`). First
ingredients needed to make "hypergraph as a discrete manifold" a
precise statement. The construction is standard: for a finite graph
`G = (V, E)` with neighbourhood relation `N(v)`, the *graph Laplacian*
is

  `(Δ f)(v) := ∑_{w ∈ N(v)} (f(w) − f(v))`.

We prove here:
  * linearity of `Δ` (additivity + scalar homogeneity),
  * symmetry of the discrete inner product,
  * linearity of the inner product,
  * a "Laplacian on constants is zero" property.

Self-adjointness `⟪Δ f, g⟫ = ⟪f, Δ g⟫` under symmetric adjacency is
the next theorem; it requires a double-sum swap that deserves its own
file (planned `DiscreteCalculusSymm.lean`). The definitions here are
the prerequisites.

This machinery is the foundation for spectral theory (Rung 2), heat
equation (Rung 6), and discrete Ricci curvature (Rungs 3 + 5) — see
`BRIDGE_MACHINERY.md`.
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Module.LinearMap.Basic

namespace InfraFormalization

variable {V : Type*} [Fintype V]

/-- An abstract symmetric, irreflexive neighbourhood relation on a
finite vertex type. This is the input data for the graph Laplacian —
enough to define neighbourhoods without committing to a specific
encoding of edges. -/
structure Neighbourhood (V : Type*) where
  /-- Is `v` adjacent to `w`? -/
  adj : V → V → Prop
  /-- Decidable equality on the adjacency relation (needed for summation). -/
  decAdj : DecidableRel adj
  /-- Symmetry. -/
  symm : ∀ v w, adj v w → adj w v
  /-- Irreflexivity — no self-loops. -/
  irrefl : ∀ v, ¬ adj v v

attribute [instance] Neighbourhood.decAdj

namespace Neighbourhood

variable (N : Neighbourhood V)

/-- The neighbourhood of a vertex as a finset. -/
def nbhd (v : V) : Finset V :=
  Finset.univ.filter (N.adj v)

theorem mem_nbhd {v w : V} : w ∈ N.nbhd v ↔ N.adj v w := by
  unfold nbhd
  simp

/-- Degree of a vertex = size of its neighbourhood. -/
def degree (v : V) : Nat := (N.nbhd v).card

end Neighbourhood

/-- **Graph Laplacian** on a finite vertex type with a given
neighbourhood relation. -/
def laplacian (N : Neighbourhood V) (f : V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ N.nbhd v, (f w - f v)

/-- **Discrete inner product** on `V → ℝ` (counting measure). -/
def discreteInner (f g : V → ℝ) : ℝ :=
  ∑ v : V, f v * g v

notation "⟪" f ", " g "⟫" => discreteInner f g

/-- The Laplacian is additive. -/
theorem laplacian_add (N : Neighbourhood V) (f g : V → ℝ) (v : V) :
    laplacian N (f + g) v = laplacian N f v + laplacian N g v := by
  unfold laplacian
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros w _
  simp [Pi.add_apply]
  ring

/-- The Laplacian commutes with scalar multiplication. -/
theorem laplacian_smul (N : Neighbourhood V) (c : ℝ) (f : V → ℝ) (v : V) :
    laplacian N (fun w => c * f w) v = c * laplacian N f v := by
  unfold laplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros w _
  ring

/-- Laplacian of a constant is zero. -/
theorem laplacian_const (N : Neighbourhood V) (c : ℝ) (v : V) :
    laplacian N (fun _ => c) v = 0 := by
  unfold laplacian
  simp

/-- `discreteInner` is symmetric. -/
theorem discreteInner_symm (f g : V → ℝ) : ⟪f, g⟫ = ⟪g, f⟫ := by
  unfold discreteInner
  apply Finset.sum_congr rfl
  intros v _
  ring

/-- `discreteInner` is additive in the first argument. -/
theorem discreteInner_add_left (f g h : V → ℝ) :
    ⟪f + g, h⟫ = ⟪f, h⟫ + ⟪g, h⟫ := by
  unfold discreteInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros v _
  simp [Pi.add_apply]
  ring

/-- `discreteInner` is additive in the second argument. -/
theorem discreteInner_add_right (f g h : V → ℝ) :
    ⟪f, g + h⟫ = ⟪f, g⟫ + ⟪f, h⟫ := by
  rw [discreteInner_symm, discreteInner_add_left, discreteInner_symm f g,
      discreteInner_symm f h]

/-- `discreteInner` is linear in the first argument (scalar). -/
theorem discreteInner_smul_left (c : ℝ) (f g : V → ℝ) :
    ⟪fun v => c * f v, g⟫ = c * ⟪f, g⟫ := by
  unfold discreteInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros v _
  ring

/-- **Expansion of the Laplacian sum.**
  `⟪Δ f, g⟫ = ∑_{v} ∑_{w ∈ N(v)} (f(w) − f(v)) · g(v)`.

This is the form used in the self-adjointness proof (next file). -/
theorem discreteInner_laplacian_expand (N : Neighbourhood V) (f g : V → ℝ) :
    ⟪laplacian N f, g⟫ = ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v) * g v := by
  unfold discreteInner laplacian
  apply Finset.sum_congr rfl
  intros v _
  rw [Finset.sum_mul]

/-- **Dirichlet-form expansion of the Laplacian.**
  `⟪f, Δ g⟫ = ∑_{v} ∑_{w ∈ N(v)} f(v) · (g(w) − g(v))`. -/
theorem discreteInner_laplacian_right (N : Neighbourhood V) (f g : V → ℝ) :
    ⟪f, laplacian N g⟫ = ∑ v : V, ∑ w ∈ N.nbhd v, f v * (g w - g v) := by
  unfold discreteInner laplacian
  apply Finset.sum_congr rfl
  intros v _
  rw [Finset.mul_sum]

/-- The graph Laplacian as a **linear map** on `V → ℝ`. This makes it
a first-class object for Mathlib's linear-algebra / spectral theory. -/
def laplacianLinear (N : Neighbourhood V) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun f := laplacian N f
  map_add' f g := by
    funext v
    exact laplacian_add N f g v
  map_smul' c f := by
    funext v
    exact laplacian_smul N c f v

@[simp] theorem laplacianLinear_apply (N : Neighbourhood V) (f : V → ℝ) :
    laplacianLinear N f = laplacian N f := rfl

end InfraFormalization
