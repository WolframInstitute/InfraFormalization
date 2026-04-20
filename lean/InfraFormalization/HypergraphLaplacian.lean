/-
Laplacian on a directed multi-hypergraph.

**Hypergraph anchor for Rung 1.** Until now, `DiscreteCalculus.lean`
operated on an abstract `Neighbourhood V`. This file ties the
discrete-calculus machinery directly back to our `Hypergraph V` —
the actual data type the Wolfram-model rewriting acts on.

For each directed hyperedge `e` and a vertex `v ∈ e.verts`, every
other vertex `w` in `e` contributes `f(w) − f(v)` to `Δ_H f(v)`.
Summed over all hyperedges:

  `Δ_H f(v) := ∑_{e ∈ H.edges} ∑_{w ∈ e.others v} (f(w) − f(v))`.

For a simple graph (every hyperedge has exactly 2 vertices), this
reduces to the standard graph Laplacian. We prove linearity (under
function addition) and vanishing on constants.

This file makes "Wolfram-model state-as-discrete-calculus-domain"
explicit: the same `Hypergraph V` that carries the rewriting rule's
LHS, RHS, and current state is now equipped with a Laplacian operator,
which under the right scaling is the discrete d'Alembertian (Rung 5)
or the discrete Laplace-Beltrami (Rung 1 → Rung 2).
-/

import InfraFormalization.Hypergraph
import InfraFormalization.DiscreteCalculus
import Mathlib.Data.Multiset.Sum
import Mathlib.Algebra.Order.Chebyshev

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a directed hyperedge `e` and a vertex `v`, the **finset of
other vertices** in `e`. Empty when `v ∉ e.verts` so that vertices
not incident to `e` receive zero contribution. For a simple-graph
edge `{v, w}` this is the singleton `{w}` when `v ∈ {v, w}` and
`∅` otherwise. -/
def Hyperedge.others (e : Hyperedge V) (v : V) : Finset V :=
  if v ∈ e.verts.toFinset then e.verts.toFinset.erase v else ∅

namespace Hypergraph

/-- **Hypergraph Laplacian** on the function space `V → ℝ`. Sums, over
each edge `e` in the multiset, the second-difference contribution
`∑_{w ∈ e.others v} (f(w) − f(v))`. -/
noncomputable def laplacianHyper (H : Hypergraph V) (f : V → ℝ) (v : V) : ℝ :=
  (H.edges.map (fun e => ∑ w ∈ e.others v, (f w - f v))).sum

/-- Linearity (additivity) of the hypergraph Laplacian. Proof by
multiset induction: each edge's contribution decomposes additively
under linearity of the inner `Finset.sum`. -/
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

/-- Hypergraph Laplacian commutes with scalar multiplication. -/
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

/-- Hypergraph Laplacian of a constant is zero. -/
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

/-- **For `v ∉ e.verts`, the per-edge contribution is zero.** A clean
consequence of the corrected `Hyperedge.others` definition. -/
theorem laplacianHyper_perEdge_zero_of_not_mem (e : Hyperedge V) (f : V → ℝ)
    (v : V) (hv : v ∉ e.verts.toFinset) :
    (∑ w ∈ e.others v, (f w - f v)) = 0 := by
  unfold Hyperedge.others
  rw [if_neg hv]
  simp

/-- **Per-edge divergence theorem.** Within a single hyperedge `e`,
summing the Laplacian contribution `∑_{w ∈ e.others v} (f(w) − f(v))`
over all `v : V` yields zero.

The proof: vertices outside `e` contribute zero (others = ∅);
vertices `v ∈ e.verts` contribute `(∑_{w ∈ S} f w) − |S| · f v`
where `S := e.verts.toFinset`; summing over `v ∈ S` gives
`|S| · ∑ f − |S| · ∑ f = 0`. This is the discrete divergence
theorem `∑ Δf = 0` localised to a single hyperedge. -/
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

/-- **Discrete divergence theorem for the hypergraph Laplacian.**
`∑_v Δ_H f(v) = 0`. The hypergraph analog of `laplacian_sum_zero`
from `DiscreteCalculusSymm.lean`. Sets up mass conservation for the
discrete heat equation on `Hypergraph V`.

Proof: by induction on the multiset of edges. For the empty edge set,
the Laplacian is identically 0. For `cons e es`, the sum decomposes
as the `e`-contribution plus the `es`-contribution; we swap `∑_v`
inside the cons via pointwise additivity, use `perEdge_sum_zero` on
the head `e`, and apply the inductive hypothesis. -/
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

/-! ## Dirichlet form non-positivity

The **Dirichlet form** `D_H(f) := ∑_v f(v) * Δ_H f(v)` is
non-positive. This is the finite-dimensional incarnation of the
statement that the Laplacian is negative semidefinite (in the
`Δ = A − D` sign convention used here), and it is what makes the
discrete heat equation `u' = Δ_H u` dissipative.

Per-edge analysis: for an edge `e` with vertex-set `S = e.verts.toFinset`,

  `∑_v f(v) · ∑_{w ∈ e.others v}(f(w) − f(v))
   = (∑_{v ∈ S} f(v))² − |S| · ∑_{v ∈ S} f(v)²  ≤  0`

by the Cauchy-Schwarz / Chebyshev inequality
`sq_sum_le_card_mul_sum_sq`. Summing over edges preserves the
inequality. -/

/-- **Per-edge contribution to the Dirichlet form is ≤ 0.**
For any hyperedge `e` and any `f : V → ℝ`,
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

/-- **Dirichlet form non-positivity** for the hypergraph Laplacian:
`∑_v f(v) · Δ_H f(v) ≤ 0`. Equivalently, `Δ_H` is negative
semidefinite in the `Δ = A − D` sign convention.

Per-edge contribution is `(∑_{v ∈ S_e} f(v))² − |S_e| · ∑ f²`, which
is ≤ 0 by Cauchy-Schwarz. Summing over edges preserves the
inequality. -/
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

end Hypergraph

end InfraFormalization
