/-
A Laplacian on functions on the vertices of a hypergraph.

For `f : V → ℝ`, `Δ_H f(v) = ∑_{e ∈ H.edges} ∑_{w ∈ e.others v} (f(w) − f(v))`, where
`e.others v` is the set of distinct vertices of `e` other than `v`, or empty when `v ∉ e`.
Hyperedges are counted with multiplicity. When every hyperedge has two distinct vertices,
`Δ_H` is the graph Laplacian `A − D` of the multigraph. The module proves linearity,
`Δ_H c = 0` for constants, `∑_v Δ_H f(v) = 0`, `∑_v f(v) Δ_H f(v) ≤ 0`, and
`∑_v f(v) Δ_H g(v) = ∑_v g(v) Δ_H f(v)`.
-/

import InfraFormalization.Hypergraph
import InfraFormalization.DiscreteCalculus
import Mathlib.Data.Multiset.Sum
import Mathlib.Algebra.Order.Chebyshev

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set of distinct vertices of `e` other than `v` when `v ∈ e.verts`, and `∅`
otherwise. For a hyperedge with vertices `v, w`, `v ≠ w`, it is `{w}` at `v`. -/
def Hyperedge.others (e : Hyperedge V) (v : V) : Finset V :=
  if v ∈ e.verts.toFinset then e.verts.toFinset.erase v else ∅

namespace Hypergraph

/-- `Δ_H f(v) = ∑_{e ∈ H.edges} ∑_{w ∈ e.others v} (f(w) − f(v))`, with the outer sum
over the edge multiset. -/
noncomputable def laplacianHyper (H : Hypergraph V) (f : V → ℝ) (v : V) : ℝ :=
  (H.edges.map (fun e => ∑ w ∈ e.others v, (f w - f v))).sum

/-- `Δ_H (f + g)(v) = Δ_H f(v) + Δ_H g(v)`. The proof is by induction on the edge
multiset. -/
theorem laplacianHyper_add (H : Hypergraph V) (f g : V → ℝ) (v : V) :
    laplacianHyper H (fun w => f w + g w) v
    = laplacianHyper H f v + laplacianHyper H g v := by
  unfold laplacianHyper
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have step :
        ∑ w ∈ e.others v, ((fun w => f w + g w) w - (fun w => f w + g w) v)
        = (∑ w ∈ e.others v, (f w - f v))
          + (∑ w ∈ e.others v, (g w - g v)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros w _
      ring
    rw [step, ih]
    ring

/-- `Δ_H (c·f)(v) = c · Δ_H f(v)`. -/
theorem laplacianHyper_smul (H : Hypergraph V) (c : ℝ) (f : V → ℝ) (v : V) :
    laplacianHyper H (fun w => c * f w) v = c * laplacianHyper H f v := by
  unfold laplacianHyper
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have step :
        ∑ w ∈ e.others v, ((fun w => c * f w) w - (fun w => c * f w) v)
        = c * ∑ w ∈ e.others v, (f w - f v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros w _
      ring
    rw [step, ih]
    ring

/-- `Δ_H` of a constant function is `0`. -/
theorem laplacianHyper_const (H : Hypergraph V) (c : ℝ) (v : V) :
    laplacianHyper H (fun _ => c) v = 0 := by
  unfold laplacianHyper
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have step : ∑ w ∈ e.others v, ((fun _ => c) w - (fun _ => c) v) = 0 := by
      apply Finset.sum_eq_zero
      intros w _
      ring
    rw [step, ih]
    ring

/-- For `v ∉ e.verts`, `∑_{w ∈ e.others v} (f(w) − f(v)) = 0`. -/
theorem laplacianHyper_perEdge_zero_of_not_mem (e : Hyperedge V) (f : V → ℝ)
    (v : V) (hv : v ∉ e.verts.toFinset) :
    (∑ w ∈ e.others v, (f w - f v)) = 0 := by
  unfold Hyperedge.others
  rw [if_neg hv]
  simp

/-- For a single hyperedge `e`, `∑_v ∑_{w ∈ e.others v} (f(w) − f(v)) = 0`.

With `S = e.verts.toFinset`, the inner sum is `0` for `v ∉ S` and
`∑_{w ∈ S} f w − |S| · f v` for `v ∈ S`. Summing over `v ∈ S` gives `0`. -/
theorem perEdge_sum_zero (e : Hyperedge V) (f : V → ℝ) :
    ∑ v : V, ∑ w ∈ e.others v, (f w - f v) = 0 := by
  set S : Finset V := e.verts.toFinset with hS
  -- Step 1: restrict outer sum to S; outside S contributions are zero.
  have step1 :
      ∑ v : V, ∑ w ∈ e.others v, (f w - f v)
      = ∑ v ∈ S, ∑ w ∈ S.erase v, (f w - f v) := by
    rw [show (Finset.univ : Finset V) = S ∪ (Finset.univ \ S) from
          (Finset.union_sdiff_of_subset (Finset.subset_univ S)).symm]
    rw [Finset.sum_union Finset.disjoint_sdiff]
    have hzero : (∑ v ∈ Finset.univ \ S, ∑ w ∈ e.others v, (f w - f v)) = 0 := by
      apply Finset.sum_eq_zero
      intros v hv
      rw [Finset.mem_sdiff] at hv
      exact laplacianHyper_perEdge_zero_of_not_mem e f v hv.2
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intros v hv
    unfold Hyperedge.others
    rw [if_pos hv]
  rw [step1]
  -- Step 2: for v ∈ S, evaluate the inner sum to (∑ S f) - |S| · f v.
  have step2 : ∀ v ∈ S,
      ∑ w ∈ S.erase v, (f w - f v) = (∑ w ∈ S, f w) - (S.card : ℝ) * f v := by
    intros v hv
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const]
    have herase_sum : (∑ w ∈ S.erase v, f w) = (∑ w ∈ S, f w) - f v := by
      have := Finset.sum_erase_add S f hv
      linarith
    rw [herase_sum]
    -- (S.erase v).card • f v in ℝ.
    have hcard_erase : ((S.erase v).card : ℝ) = (S.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hv]
      have hScard_pos : 1 ≤ S.card := Finset.Nonempty.card_pos ⟨v, hv⟩
      have : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
        rw [Nat.cast_sub hScard_pos]
        simp
      exact this
    rw [show ((S.erase v).card • f v) = ((S.erase v).card : ℝ) * f v from by
          simp [nsmul_eq_mul]]
    rw [hcard_erase]
    ring
  rw [Finset.sum_congr rfl step2]
  -- Step 3: ∑_{v ∈ S} ((∑ S f) - |S| f v) = |S|·(∑ S f) - |S|·(∑ S f) = 0.
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const]
  rw [show (∑ v ∈ S, (S.card : ℝ) * f v) = (S.card : ℝ) * ∑ v ∈ S, f v from
        (Finset.mul_sum _ _ _).symm]
  push_cast
  ring

/-- `∑_v Δ_H f(v) = 0`. This is the hypergraph version of `laplacian_sum_zero` in
`DiscreteCalculusSymm.lean`. The proof is by induction on the edge multiset using
`perEdge_sum_zero`. -/
theorem laplacianHyper_sum_zero (H : Hypergraph V) (f : V → ℝ) :
    ∑ v : V, laplacianHyper H f v = 0 := by
  unfold laplacianHyper
  -- Induct on the edge multiset.
  induction H.edges using Multiset.induction_on with
  | empty =>
    simp
  | cons e es ih =>
    have step : ∀ v : V,
        ((e ::ₘ es).map (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum
        = (∑ w ∈ e.others v, (f w - f v))
          + (es.map (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum := by
      intro v
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [show (∑ v : V, ((e ::ₘ es).map
                (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum)
          = (∑ v : V, (∑ w ∈ e.others v, (f w - f v)))
          + (∑ v : V, (es.map
                (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum) from ?_]
    · rw [perEdge_sum_zero e f, ih, zero_add]
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros v _
      exact step v

/-! ## Dirichlet form

`D_H(f) = ∑_v f(v) · Δ_H f(v)` is nonpositive, so `Δ_H` is negative semidefinite with
respect to the counting inner product. For an edge `e` with vertex set
`S = e.verts.toFinset`,

  `∑_v f(v) · ∑_{w ∈ e.others v}(f(w) − f(v))
   = (∑_{v ∈ S} f(v))² − |S| · ∑_{v ∈ S} f(v)²  ≤  0`

by `sq_sum_le_card_mul_sum_sq`. Summing over edges gives the result. -/

/-- For a hyperedge `e` and `f : V → ℝ`,
`∑_v f(v) · ∑_{w ∈ e.others v}(f(w) − f(v)) ≤ 0`. -/
theorem perEdge_dirichlet_nonpos (e : Hyperedge V) (f : V → ℝ) :
    (∑ v : V, f v * (∑ w ∈ e.others v, (f w - f v))) ≤ 0 := by
  set S : Finset V := e.verts.toFinset with hS
  -- Step 1: restrict to v ∈ S; outside contributions are zero.
  have step1 :
      (∑ v : V, f v * ∑ w ∈ e.others v, (f w - f v))
      = ∑ v ∈ S, f v * ∑ w ∈ S.erase v, (f w - f v) := by
    rw [show (Finset.univ : Finset V) = S ∪ (Finset.univ \ S) from
          (Finset.union_sdiff_of_subset (Finset.subset_univ S)).symm]
    rw [Finset.sum_union Finset.disjoint_sdiff]
    have hzero :
        (∑ v ∈ Finset.univ \ S, f v * ∑ w ∈ e.others v, (f w - f v)) = 0 := by
      apply Finset.sum_eq_zero
      intros v hv
      rw [Finset.mem_sdiff] at hv
      have := Hypergraph.laplacianHyper_perEdge_zero_of_not_mem e f v hv.2
      rw [this, mul_zero]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intros v hv
    unfold Hyperedge.others
    rw [if_pos hv]
  -- Step 2: on v ∈ S, inner sum = (∑ w ∈ S, f w) - |S| · f v.
  have step2 : ∀ v ∈ S,
      ∑ w ∈ S.erase v, (f w - f v) = (∑ w ∈ S, f w) - (S.card : ℝ) * f v := by
    intros v hv
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    have herase_sum : (∑ w ∈ S.erase v, f w) = (∑ w ∈ S, f w) - f v := by
      have := Finset.sum_erase_add S f hv
      linarith
    rw [herase_sum]
    have hcard_erase : ((S.erase v).card : ℝ) = (S.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hv]
      have hScard_pos : 1 ≤ S.card := Finset.Nonempty.card_pos ⟨v, hv⟩
      have : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
        rw [Nat.cast_sub hScard_pos]
        simp
      exact this
    rw [show ((S.erase v).card • f v) = ((S.erase v).card : ℝ) * f v from by
          simp [nsmul_eq_mul]]
    rw [hcard_erase]
    ring
  rw [step1, Finset.sum_congr rfl (fun v hv => by rw [step2 v hv])]
  -- Step 3: the S-sum collapses to (∑ f)² - |S| · ∑ f².
  have step3 :
      (∑ v ∈ S, f v * ((∑ w ∈ S, f w) - (S.card : ℝ) * f v))
      = (∑ v ∈ S, f v) ^ 2 - (S.card : ℝ) * ∑ v ∈ S, (f v) ^ 2 := by
    have h1 :
        (∑ v ∈ S, f v * ((∑ w ∈ S, f w) - (S.card : ℝ) * f v))
        = (∑ v ∈ S, f v * (∑ w ∈ S, f w))
          - ∑ v ∈ S, (S.card : ℝ) * (f v) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intros v _
      ring
    have h2 : (∑ v ∈ S, f v * (∑ w ∈ S, f w))
            = (∑ v ∈ S, f v) * (∑ w ∈ S, f w) := by
      rw [← Finset.sum_mul]
    have h3 : (∑ v ∈ S, (S.card : ℝ) * (f v) ^ 2)
            = (S.card : ℝ) * ∑ v ∈ S, (f v) ^ 2 := by
      rw [← Finset.mul_sum]
    rw [h1, h2, h3]
    ring
  rw [step3]
  -- Step 4: Cauchy-Schwarz: (∑ f)² ≤ |S| · ∑ f².
  have hcs : (∑ v ∈ S, f v) ^ 2 ≤ (S.card : ℝ) * ∑ v ∈ S, (f v) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := S) (f := f)
    exact_mod_cast this
  linarith

/-! ### Per-edge bilinear form

For `f g : V → ℝ`, the contribution of edge `e` to `∑_v f(v) · Δ_H g(v)` equals
`(∑_{S_e} f)(∑_{S_e} g) − |S_e| · ∑_{S_e} f·g`, which is symmetric in `f` and `g`. -/

/-- `∑_v f(v) · ∑_{w ∈ e.others v} (g(w) − g(v)) = (∑_S f)(∑_S g) − |S| · ∑_S f·g` with
`S = e.verts.toFinset`. -/
theorem perEdge_bilinear_eq (e : Hyperedge V) (f g : V → ℝ) :
    (∑ v : V, f v * (∑ w ∈ e.others v, (g w - g v)))
    = (∑ v ∈ e.verts.toFinset, f v) * (∑ w ∈ e.verts.toFinset, g w)
      - (e.verts.toFinset.card : ℝ) *
        ∑ v ∈ e.verts.toFinset, f v * g v := by
  set S : Finset V := e.verts.toFinset with hS
  have step1 :
      (∑ v : V, f v * ∑ w ∈ e.others v, (g w - g v))
      = ∑ v ∈ S, f v * ∑ w ∈ S.erase v, (g w - g v) := by
    rw [show (Finset.univ : Finset V) = S ∪ (Finset.univ \ S) from
          (Finset.union_sdiff_of_subset (Finset.subset_univ S)).symm]
    rw [Finset.sum_union Finset.disjoint_sdiff]
    have hzero :
        (∑ v ∈ Finset.univ \ S, f v * ∑ w ∈ e.others v, (g w - g v)) = 0 := by
      apply Finset.sum_eq_zero
      intros v hv
      rw [Finset.mem_sdiff] at hv
      have := Hypergraph.laplacianHyper_perEdge_zero_of_not_mem e g v hv.2
      rw [this, mul_zero]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intros v hv
    unfold Hyperedge.others
    rw [if_pos hv]
  have step2 : ∀ v ∈ S,
      ∑ w ∈ S.erase v, (g w - g v) = (∑ w ∈ S, g w) - (S.card : ℝ) * g v := by
    intros v hv
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    have herase_sum : (∑ w ∈ S.erase v, g w) = (∑ w ∈ S, g w) - g v := by
      have := Finset.sum_erase_add S g hv
      linarith
    rw [herase_sum]
    have hcard_erase : ((S.erase v).card : ℝ) = (S.card : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem hv]
      have hScard_pos : 1 ≤ S.card := Finset.Nonempty.card_pos ⟨v, hv⟩
      have : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
        rw [Nat.cast_sub hScard_pos]
        simp
      exact this
    rw [show ((S.erase v).card • g v) = ((S.erase v).card : ℝ) * g v from by
          simp [nsmul_eq_mul]]
    rw [hcard_erase]
    ring
  rw [step1, Finset.sum_congr rfl (fun v hv => by rw [step2 v hv])]
  -- Step 3: collapse the S-sum to (∑ f)(∑ g) − |S| · ∑ f·g.
  have h1 :
      (∑ v ∈ S, f v * ((∑ w ∈ S, g w) - (S.card : ℝ) * g v))
      = (∑ v ∈ S, f v * (∑ w ∈ S, g w))
        - ∑ v ∈ S, (S.card : ℝ) * (f v * g v) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros v _
    ring
  have h2 : (∑ v ∈ S, f v * (∑ w ∈ S, g w))
          = (∑ v ∈ S, f v) * (∑ w ∈ S, g w) := by
    rw [← Finset.sum_mul]
  have h3 : (∑ v ∈ S, (S.card : ℝ) * (f v * g v))
          = (S.card : ℝ) * ∑ v ∈ S, f v * g v := by
    rw [← Finset.mul_sum]
  rw [h1, h2, h3]

/-- The per-edge contribution with `f, g` equals that with `g, f`. The proof uses
`perEdge_bilinear_eq`. -/
theorem perEdge_bilinear_symm (e : Hyperedge V) (f g : V → ℝ) :
    (∑ v : V, f v * (∑ w ∈ e.others v, (g w - g v)))
    = ∑ v : V, g v * (∑ w ∈ e.others v, (f w - f v)) := by
  rw [perEdge_bilinear_eq e f g, perEdge_bilinear_eq e g f]
  have h : ∀ v : V, f v * g v = g v * f v := fun v => mul_comm _ _
  rw [Finset.sum_congr rfl (fun v _ => h v)]
  ring

/-- `∑_v f(v) · Δ_H f(v) ≤ 0`. The proof sums `perEdge_dirichlet_nonpos` over the edge
multiset. -/
theorem laplacianHyper_dirichlet_nonpos
    (H : Hypergraph V) (f : V → ℝ) :
    (∑ v : V, f v * Hypergraph.laplacianHyper H f v) ≤ 0 := by
  unfold Hypergraph.laplacianHyper
  -- Swap ∑_v and ∑_e via Multiset induction, reducing to per-edge.
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    -- Distribute f(v) across (e-term + es-sum); split ∑_v via sum_add.
    have swap :
        (∑ v : V, f v *
          ((e ::ₘ es).map (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum)
        = (∑ v : V, f v * (∑ w ∈ e.others v, (f w - f v)))
          + (∑ v : V, f v *
             (es.map (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros v _
      simp only [Multiset.map_cons, Multiset.sum_cons]
      ring
    rw [swap]
    have hper : (∑ v : V, f v * (∑ w ∈ e.others v, (f w - f v))) ≤ 0 :=
      perEdge_dirichlet_nonpos e f
    linarith

/-- `∑_v f(v) · Δ_H g(v) = ∑_v g(v) · Δ_H f(v)`. The proof sums `perEdge_bilinear_symm`
over the edge multiset. -/
theorem laplacianHyper_self_adjoint (H : Hypergraph V) (f g : V → ℝ) :
    (∑ v : V, f v * Hypergraph.laplacianHyper H g v)
    = ∑ v : V, g v * Hypergraph.laplacianHyper H f v := by
  unfold Hypergraph.laplacianHyper
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    have swap_f_g :
        (∑ v : V, f v *
          ((e ::ₘ es).map (fun e' => ∑ w ∈ e'.others v, (g w - g v))).sum)
        = (∑ v : V, f v * (∑ w ∈ e.others v, (g w - g v)))
          + (∑ v : V, f v *
             (es.map (fun e' => ∑ w ∈ e'.others v, (g w - g v))).sum) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros v _
      simp only [Multiset.map_cons, Multiset.sum_cons]
      ring
    have swap_g_f :
        (∑ v : V, g v *
          ((e ::ₘ es).map (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum)
        = (∑ v : V, g v * (∑ w ∈ e.others v, (f w - f v)))
          + (∑ v : V, g v *
             (es.map (fun e' => ∑ w ∈ e'.others v, (f w - f v))).sum) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros v _
      simp only [Multiset.map_cons, Multiset.sum_cons]
      ring
    rw [swap_f_g, swap_g_f, perEdge_bilinear_symm e f g, ih]

end Hypergraph

end InfraFormalization
