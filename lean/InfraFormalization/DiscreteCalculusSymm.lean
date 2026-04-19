/-
Self-adjointness of the graph Laplacian under a symmetric adjacency.

Proves `⟪Δ f, g⟫ = ⟪f, Δ g⟫` for the graph Laplacian `Δ` and counting
inner product `⟪·,·⟫` defined in `DiscreteCalculus.lean`. The key
ingredient is a double-sum swap: under symmetric adjacency, swapping
the summation order over the edge set is identity on the sum.

The "Dirichlet form" identity that falls out along the way is

  `⟪Δ f, g⟫ = -½ ∑_{(v,w) : v ∼ w} (f(w) − f(v)) (g(w) − g(v))`

which makes the symmetry manifest and is the discrete analog of the
Dirichlet form on a Riemannian manifold.
-/

import InfraFormalization.DiscreteCalculus
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace InfraFormalization

variable {V : Type*} [Fintype V]

/-- **Edge-sum swap lemma.** Under symmetric adjacency, swapping the
roles of the two summation indices in a nested neighbourhood sum is
identity:

  `∑_v ∑_{w ∈ N(v)} F(v, w) = ∑_v ∑_{w ∈ N(v)} F(w, v)`.

The proof rewrites the nested sum as a sum over the full `V × V`
product with an `if` indicator for adjacency, swaps the two `V`-sums
(which is always valid), then uses the symmetry of adjacency to
identify the two forms. -/
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
  -- Swap sums on the LHS.
  rw [Finset.sum_comm]
  -- LHS is now: ∑_w ∑_v, if N.adj v w then F v w else 0.
  -- RHS is:      ∑_v ∑_w, if N.adj v w then F w v else 0.
  -- Rename variables: in LHS, the outer is `w` and inner is `v`; we can
  -- treat the whole sum as a function in which v and w are both bound.
  -- Concretely: ∑_w ∑_v G(v, w) = ∑_v ∑_w G(w, v) (just relabelling).
  apply Finset.sum_congr rfl
  intros v _
  apply Finset.sum_congr rfl
  intros w _
  -- Goal (for the current v, w pair): after the Finset.sum_comm on the LHS,
  -- the summand at outer `v`, inner `w` is:
  --   if N.adj w v then F w v else 0.
  -- On the RHS, the summand at outer `v`, inner `w` is:
  --   if N.adj v w then F w v else 0.
  -- Equality of the two uses N.symm.
  by_cases h : N.adj v w
  · simp [h, N.symm v w h]
  · have : ¬ N.adj w v := fun hh => h (N.symm w v hh)
    simp [h, this]

/-- **Self-adjointness of the graph Laplacian.** Under symmetric
adjacency and the counting inner product,

  `⟪Δ f, g⟫ = ⟪f, Δ g⟫`.

Proof: expand both sides via `discreteInner_laplacian_expand` and
`discreteInner_laplacian_right`, then use `nbhd_sum_swap` on the LHS
to rewrite `(f(w) - f(v)) · g(v)` as `(f(v) - f(w)) · g(w)`. Combine
with `Finset.sum_add_distrib` / algebra to identify with the RHS. -/
theorem laplacian_self_adjoint (N : Neighbourhood V) (f g : V → ℝ) :
    ⟪laplacian N f, g⟫ = ⟪f, laplacian N g⟫ := by
  rw [discreteInner_laplacian_expand, discreteInner_laplacian_right]
  -- LHS: ∑_v ∑_{w ∈ N(v)} (f w - f v) · g v.
  -- RHS: ∑_v ∑_{w ∈ N(v)} f v · (g w - g v).
  -- Strategy: swap the LHS to get (f v - f w) · g w on the summand,
  -- and separately swap RHS to get f w · (g v - g w). Then show both
  -- equal -½ ∑ (f v - f w)(g v - g w) or just combine directly.
  --
  -- Simpler: rewrite both as the SAME sum `∑_{v,w} (f w - f v) (g v - g w)`
  -- via double averaging.
  -- Formally:
  --   2 · LHS = LHS + LHS
  --         = ∑ (f w - f v) · g v + ∑ (f w - f v) · g v
  --         = ∑ (f w - f v) · g v + ∑ (f v - f w) · g w    (by nbhd_sum_swap with F(v,w) = (f w - f v) · g v → F(w,v) = (f v - f w) · g w)
  --         = ∑ [(f w - f v) · g v + (f v - f w) · g w]
  --         = -∑ (f v - f w) · (g v - g w).
  -- Similarly 2 · RHS = -∑ (f v - f w) · (g v - g w).
  -- Divide by 2.
  have swap_lhs : ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v) * g v
                = ∑ v : V, ∑ w ∈ N.nbhd v, (f v - f w) * g w :=
    nbhd_sum_swap N (fun v w => (f w - f v) * g v)
  have swap_rhs : ∑ v : V, ∑ w ∈ N.nbhd v, f v * (g w - g v)
                = ∑ v : V, ∑ w ∈ N.nbhd v, f w * (g v - g w) :=
    nbhd_sum_swap N (fun v w => f v * (g w - g v))
  -- Use: 2·LHS = LHS + swap_lhs.
  -- Use: 2·RHS = RHS + swap_rhs.
  -- Compute LHS + swap_lhs.
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
  -- Note: (f w - f v)·g v + (f v - f w)·g w
  --     = f w·g v - f v·g v + f v·g w - f w·g w
  -- And: f v·(g w - g v) + f w·(g v - g w)
  --     = f v·g w - f v·g v + f w·g v - f w·g w
  -- These are pointwise equal. Verify by ring.
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
  -- Chain: 2 · LHS_orig = LHS_orig + swap_lhs
  --                   = [from lhs_double] = RHS of summand_eq [from double_eq]
  --                   = [from rhs_double] = 2 · RHS_orig.
  -- Therefore LHS_orig = RHS_orig.
  -- Combine: using swap, both 2·LHS_orig and 2·RHS_orig equal the same double sum.
  -- Write `A := ∑ (f w - f v) g v` and `A' := ∑ (f v - f w) g w` (= A by swap_lhs).
  -- Similarly `B := ∑ f v (g w - g v)` and `B' := ∑ f w (g v - g w)` (= B by swap_rhs).
  -- Then A + A' = ∑ ((f w - f v) g v + (f v - f w) g w)  (by lhs_double)
  --            = ∑ (f v (g w - g v) + f w (g v - g w))   (by double_eq via summand_eq)
  --            = B + B'                                  (by rhs_double reversed).
  -- Since A' = A and B' = B, 2·A = 2·B, so A = B.
  set A : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v) * g v with hA
  set A' : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, (f v - f w) * g w with hA'
  set B : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, f v * (g w - g v) with hB
  set B' : ℝ := ∑ v : V, ∑ w ∈ N.nbhd v, f w * (g v - g w) with hB'
  -- Chain the key equality A + A' = B + B'.
  have chain : A + A' = B + B' := by
    rw [hA, hA', hB, hB', lhs_double, rhs_double]
    exact double_eq
  -- A = A' and B = B' from swaps.
  have hAA' : A = A' := swap_lhs
  have hBB' : B = B' := swap_rhs
  linarith

/-- **Dirichlet form identity.** The quadratic form `⟪f, -Δ f⟫` equals
half the sum of squared edge differences:

  `⟪f, -Δ f⟫ = ½ ∑_v ∑_{w ∈ N(v)} (f(w) - f(v))²`.

This is the discrete analog of the Dirichlet energy
`½ ∫_M |∇f|²` on a Riemannian manifold, and makes the
positive-semidefiniteness of `-Δ` manifest. -/
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
  -- Target: - ∑_v ∑_{w ∈ N(v)} f v · (f w - f v) = (1/2) · ∑ (f w - f v)².
  -- Use swap: ∑ f v · (f w - f v) = ∑ f w · (f v - f w) = -∑ f w · (f w - f v).
  -- So 2 · ∑ f v · (f w - f v) = ∑ f v · (f w - f v) - ∑ f w · (f w - f v)
  --                             = ∑ (f v - f w) · (f w - f v)
  --                             = -∑ (f w - f v)².
  have swap_val : ∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v)
                = ∑ v : V, ∑ w ∈ N.nbhd v, f w * (f v - f w) :=
    nbhd_sum_swap N (fun v w => f v * (f w - f v))
  -- Combine.
  have combine_double :
      2 * (∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v))
    = - ∑ v : V, ∑ w ∈ N.nbhd v, (f w - f v)^2 := by
    have step : 2 * (∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v))
              = (∑ v : V, ∑ w ∈ N.nbhd v, f v * (f w - f v))
              + (∑ v : V, ∑ w ∈ N.nbhd v, f w * (f v - f w)) := by
      rw [two_mul, swap_val]
    rw [step]
    -- Goal:
    --   (∑_v ∑_{w ∈ N(v)} f v (f w - f v)) + (∑_v ∑_{w ∈ N(v)} f w (f v - f w))
    --   = -∑_v ∑_{w ∈ N(v)} (f w - f v)^2.
    -- Combine to a single double sum on each side.
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
  -- Now: - ∑ f v · (f w - f v) = (1/2) · ∑ (f w - f v)^2.
  linarith

/-- **Positive semidefiniteness of the (negative) Laplacian.**
`⟪f, -Δ f⟫ ≥ 0` — the discrete Laplacian is a negative operator in the
sense of the counting inner product. -/
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

end InfraFormalization
