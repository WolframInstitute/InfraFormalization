/-
Self-adjointness of the graph Laplacian under a symmetric adjacency.

For the graph Laplacian `Δ` and inner product `⟪·,·⟫` of `DiscreteCalculus.lean`, the module
proves `⟪Δ f, g⟫ = ⟪f, Δ g⟫`, the identity
`⟪f, -Δ f⟫ = ½ ∑_v ∑_{w ∈ N(v)} (f(w) − f(v))²`, the inequality `⟪f, -Δ f⟫ ≥ 0`, and
`∑_v (Δ f)(v) = 0`. Each proof uses `nbhd_sum_swap`, which exchanges the two indices of a
sum over adjacent pairs.
-/

import InfraFormalization.DiscreteCalculus
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace InfraFormalization

variable {V : Type*} [Fintype V]

/-- `∑_v ∑_{w ∈ N(v)} F(v, w) = ∑_v ∑_{w ∈ N(v)} F(w, v)`. The proof writes both sides as
sums over `V × V` with an adjacency indicator, exchanges the sums, and uses symmetry of the
adjacency relation. -/
theorem nbhd_sum_swap (N : Neighbourhood V) (F : V → V → ℝ) :
    ∑ v : V, ∑ w ∈ N.nbhd v, F v w
    = ∑ v : V, ∑ w ∈ N.nbhd v, F w v := by
  -- Convert both sides to full double sums with `if` indicator via
  -- `N.nbhd v = Finset.univ.filter (N.adj v)` and `Finset.sum_filter`.
  have conv_lhs : ∑ v : V, ∑ w ∈ N.nbhd v, F v w
                = ∑ v : V, ∑ w : V, if N.adj v w then F v w else 0 := by
    apply Finset.sum_congr rfl
    intros v _
    show ∑ w ∈ Finset.univ.filter (N.adj v), F v w
       = ∑ w : V, if N.adj v w then F v w else 0
    rw [Finset.sum_filter]
  have conv_rhs : ∑ v : V, ∑ w ∈ N.nbhd v, F w v
                = ∑ v : V, ∑ w : V, if N.adj v w then F w v else 0 := by
    apply Finset.sum_congr rfl
    intros v _
    show ∑ w ∈ Finset.univ.filter (N.adj v), F w v
       = ∑ w : V, if N.adj v w then F w v else 0
    rw [Finset.sum_filter]
  rw [conv_lhs, conv_rhs]
  -- Exchange the two sums on the left-hand side.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intros v _
  apply Finset.sum_congr rfl
  intros w _
  -- The summands are `if N.adj w v then F w v else 0` and
  -- `if N.adj v w then F w v else 0`; they agree by `N.symm`.
  by_cases h : N.adj v w
  · simp [h, N.symm v w h]
  · have : ¬ N.adj w v := fun hh => h (N.symm w v hh)
    simp [h, this]

/-- `⟪Δ f, g⟫ = ⟪f, Δ g⟫`. The proof shows that twice each side equals the same double sum,
using `nbhd_sum_swap`. -/
theorem laplacian_self_adjoint (N : Neighbourhood V) (f g : V → ℝ) :
    ⟪laplacian N f, g⟫ = ⟪f, laplacian N g⟫ := by
  rw [discreteInner_laplacian_expand, discreteInner_laplacian_right]
  -- Left: ∑_v ∑_{w ∈ N(v)} (f w - f v) · g v. Right: ∑_v ∑_{w ∈ N(v)} f v · (g w - g v).
  have swap_lhs : ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v) * g v
                = ∑ v : V, ∑ w ∈ N.nbhd v, (f v - f w) * g w :=
    nbhd_sum_swap N (fun v w => (f w - f v) * g v)
  have swap_rhs : ∑ v : V, ∑ w ∈ N.nbhd v, f v * (g w - g v)
                = ∑ v : V, ∑ w ∈ N.nbhd v, f w * (g v - g w) :=
    nbhd_sum_swap N (fun v w => f v * (g w - g v))
  have lhs_double : (∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v) * g v)
                  + (∑ v : V, ∑ w ∈ N.nbhd v, (f v - f w) * g w)
                  = ∑ v : V, ∑ w ∈ N.nbhd v,
                      ((f w - f v) * g v + (f v - f w) * g w) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros v _
    rw [← Finset.sum_add_distrib]
  have rhs_double : (∑ v : V, ∑ w ∈ N.nbhd v, f v * (g w - g v))
                  + (∑ v : V, ∑ w ∈ N.nbhd v, f w * (g v - g w))
                  = ∑ v : V, ∑ w ∈ N.nbhd v,
                      (f v * (g w - g v) + f w * (g v - g w)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros v _
    rw [← Finset.sum_add_distrib]
  -- Both summands expand to `f w·g v - f v·g v + f v·g w - f w·g w`.
  have summand_eq : ∀ v w, (f w - f v) * g v + (f v - f w) * g w
                         = f v * (g w - g v) + f w * (g v - g w) := by
    intros v w
    ring
  have double_eq : (∑ v : V, ∑ w ∈ N.nbhd v,
                      ((f w - f v) * g v + (f v - f w) * g w))
                = (∑ v : V, ∑ w ∈ N.nbhd v,
                      (f v * (g w - g v) + f w * (g v - g w))) := by
    apply Finset.sum_congr rfl
    intros v _
    apply Finset.sum_congr rfl
    intros w _
    exact summand_eq v w
  -- `A + A' = B + B'`, `A = A'` and `B = B'` give `A = B`.
  set A : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v) * g v with hA
  set A' : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, (f v - f w) * g w with hA'
  set B : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, f v * (g w - g v) with hB
  set B' : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, f w * (g v - g w) with hB'
  have chain : A + A' = B + B' := by
    rw [hA, hA', hB, hB', lhs_double, rhs_double]
    exact double_eq
  have hAA' : A = A' := swap_lhs
  have hBB' : B = B' := swap_rhs
  linarith

/-- `⟪f, -Δ f⟫ = ½ ∑_v ∑_{w ∈ N(v)} (f(w) - f(v))²`. -/
theorem dirichlet_form (N : Neighbourhood V) (f : V → ℝ) :
    ⟪f, fun v => -laplacian N f v⟫
    = (1 / 2) * ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v)^2 := by
  -- Expand ⟪f, -Δ f⟫ = -⟪f, Δ f⟫ = -∑_v ∑_{w ∈ N(v)} f(v) · (f(w) - f(v)).
  have expand : ⟪f, fun v => -laplacian N f v⟫
              = - ∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v) := by
    unfold discreteInner laplacian
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [mul_neg, Finset.mul_sum]
  rw [expand]
  -- By `nbhd_sum_swap`, `2 · ∑ f v · (f w - f v) = -∑ (f w - f v)²`.
  have swap_val : ∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v)
                = ∑ v : V, ∑ w ∈ N.nbhd v, f w * (f v - f w) :=
    nbhd_sum_swap N (fun v w => f v * (f w - f v))
  have combine_double :
      2 * (∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v))
    = - ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v)^2 := by
    have step : 2 * (∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v))
              = (∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v))
              + (∑ v : V, ∑ w ∈ N.nbhd v, f w * (f v - f w)) := by
      rw [two_mul, swap_val]
    rw [step]
    -- Write each side as a single double sum.
    have lhs_combine :
        (∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v))
        + (∑ v : V, ∑ w ∈ N.nbhd v, f w * (f v - f w))
        = ∑ v : V, ∑ w ∈ N.nbhd v,
            (f v * (f w - f v) + f w * (f v - f w)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_add_distrib]
    have rhs_combine :
        - ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v)^2
        = ∑ v : V, ∑ w ∈ N.nbhd v, -((f w - f v)^2) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_neg_distrib]
    rw [lhs_combine, rhs_combine]
    apply Finset.sum_congr rfl
    intros v _
    apply Finset.sum_congr rfl
    intros w _
    ring
  linarith

/-- `⟪f, -Δ f⟫ ≥ 0`. -/
theorem laplacian_neg_psd (N : Neighbourhood V) (f : V → ℝ) :
    0 ≤ ⟪f, fun v => -laplacian N f v⟫ := by
  rw [dirichlet_form]
  have hsum_nn : 0 ≤ ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v)^2 := by
    apply Finset.sum_nonneg
    intros v _
    apply Finset.sum_nonneg
    intros w _
    exact sq_nonneg _
  linarith

/-- `∑_v (Δ f)(v) = 0`. -/
theorem laplacian_sum_zero (N : Neighbourhood V) (f : V → ℝ) :
    ∑ v : V, laplacian N f v = 0 := by
  unfold laplacian
  -- swap : ∑_v ∑_{w ∈ N(v)} (f w - f v) = ∑_v ∑_{w ∈ N(v)} (f v - f w).
  have swap := nbhd_sum_swap N (fun v w => f w - f v)
  have key : (∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v))
           + (∑ v : V, ∑ w ∈ N.nbhd v, (f v - f w)) = 0 := by
    rw [← Finset.sum_add_distrib]
    have step : ∀ v : V,
        (∑ w ∈ N.nbhd v, (f w - f v)) + (∑ w ∈ N.nbhd v, (f v - f w))
        = 0 := by
      intro v
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intros w _
      ring
    rw [show (fun v : V =>
              (∑ w ∈ N.nbhd v, (f w - f v)) + (∑ w ∈ N.nbhd v, (f v - f w)))
          = (fun _ : V => (0 : ℝ)) from funext step]
    simp
  -- `key` and `swap` give `2 · ∑ = 0`.
  have := swap
  linarith

end InfraFormalization
