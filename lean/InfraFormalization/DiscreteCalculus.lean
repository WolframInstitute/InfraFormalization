/-
Discrete calculus on a finite vertex type with a symmetric neighbourhood relation.

The module defines the neighbourhood structure `Neighbourhood`, the graph Laplacian
`(Δ f)(v) := ∑_{w ∈ N(v)} (f(w) − f(v))`, and the discrete inner product
`⟪f, g⟫ := ∑_v f(v) g(v)`. It proves that the Laplacian is linear and vanishes on
constants, that the inner product is symmetric and bilinear, and gives the double-sum
expansions of `⟪Δ f, g⟫` and `⟪f, Δ g⟫`. Self-adjointness is proved in
`DiscreteCalculusSymm.lean`.
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

/-- A symmetric, irreflexive, decidable adjacency relation on a vertex type. -/
structure Neighbourhood (V : Type*) where
  /-- The adjacency relation. -/
  adj : V → V → Prop
  /-- Decidability of the adjacency relation. -/
  decAdj : DecidableRel adj
  /-- Symmetry. -/
  symm : ∀ v w, adj v w → adj w v
  /-- Irreflexivity: no vertex is adjacent to itself. -/
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

/-- The degree of a vertex: the cardinality of its neighbourhood. -/
def degree (v : V) : Nat := (N.nbhd v).card

end Neighbourhood

/-- The graph Laplacian `(Δ f)(v) = ∑_{w ∈ N(v)} (f(w) − f(v))`. -/
def laplacian (N : Neighbourhood V) (f : V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ N.nbhd v, (f w - f v)

/-- The inner product `⟪f, g⟫ = ∑_v f(v) g(v)` on `V → ℝ`. -/
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

/-- `⟪Δ f, g⟫ = ∑_{v} ∑_{w ∈ N(v)} (f(w) − f(v)) · g(v)`. -/
theorem discreteInner_laplacian_expand (N : Neighbourhood V) (f g : V → ℝ) :
    ⟪laplacian N f, g⟫ = ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v) * g v := by
  unfold discreteInner laplacian
  apply Finset.sum_congr rfl
  intros v _
  rw [Finset.sum_mul]

/-- `⟪f, Δ g⟫ = ∑_{v} ∑_{w ∈ N(v)} f(v) · (g(w) − g(v))`. -/
theorem discreteInner_laplacian_right (N : Neighbourhood V) (f g : V → ℝ) :
    ⟪f, laplacian N g⟫ = ∑ v : V, ∑ w ∈ N.nbhd v, f v * (g w - g v) := by
  unfold discreteInner laplacian
  apply Finset.sum_congr rfl
  intros v _
  rw [Finset.mul_sum]

/-- The graph Laplacian as an `ℝ`-linear map on `V → ℝ`. -/
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
