/-
Discrete gradient and divergence on a directed hypergraph, with summation by parts.

For a hyperedge `e = (v₁, …, vₖ)` this module sets `src e = v₁` and `dst e = vₖ`; intermediate vertices are not used. It defines `hyperedgeGradient f e = f(dst e) − f(src e)` and `hypergraphDiv H g v`, the sum of `g e` over edges with `dst e = v` minus the sum over edges with `src e = v`. It proves linearity of both operators and the identity `∑_v f(v) · hypergraphDiv H g v = ∑_{e ∈ H.edges} g(e) · hyperedgeGradient f e`. On 2-vertex edges these are the usual graph gradient and divergence.
-/

import InfraFormalization.Hypergraph
import InfraFormalization.DiscreteCalculus
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Multiset.Sum

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Hyperedge

/-- The first vertex of a hyperedge. -/
def src (e : Hyperedge V) : V :=
  e.verts.head e.nonempty

/-- The last vertex of a hyperedge. -/
def dst (e : Hyperedge V) : V :=
  e.verts.getLast e.nonempty

end Hyperedge

/-- `hyperedgeGradient f e = f(dst e) − f(src e)`. -/
def hyperedgeGradient (f : V → ℝ) (e : Hyperedge V) : ℝ :=
  f e.dst - f e.src

/-- `hypergraphDiv H g v = ∑_{e : dst e = v} g e − ∑_{e : src e = v} g e`, summed over the edge multiset. An edge with `src e = dst e` contributes `0`. -/
noncomputable def hypergraphDiv (H : Hypergraph V) (g : Hyperedge V → ℝ)
    (v : V) : ℝ :=
  (H.edges.map (fun e =>
    (if e.dst = v then g e else 0) - (if e.src = v then g e else 0))).sum

/-! ## Linearity of gradient -/

theorem hyperedgeGradient_add (f g : V → ℝ) (e : Hyperedge V) :
    hyperedgeGradient (fun v => f v + g v) e
    = hyperedgeGradient f e + hyperedgeGradient g e := by
  unfold hyperedgeGradient
  simp [Pi.add_apply]
  ring

theorem hyperedgeGradient_smul (c : ℝ) (f : V → ℝ) (e : Hyperedge V) :
    hyperedgeGradient (fun v => c * f v) e = c * hyperedgeGradient f e := by
  unfold hyperedgeGradient
  ring

theorem hyperedgeGradient_const (c : ℝ) (e : Hyperedge V) :
    hyperedgeGradient (fun _ => c) e = 0 := by
  unfold hyperedgeGradient
  ring

/-! ## Linearity of divergence -/

theorem hypergraphDiv_add (H : Hypergraph V) (g h : Hyperedge V → ℝ) (v : V) :
    hypergraphDiv H (fun e => g e + h e) v
    = hypergraphDiv H g v + hypergraphDiv H h v := by
  unfold hypergraphDiv
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih]
    by_cases h_dst : e.dst = v <;> by_cases h_src : e.src = v <;>
      simp [h_dst, h_src] <;> try ring

theorem hypergraphDiv_smul (H : Hypergraph V) (c : ℝ)
    (g : Hyperedge V → ℝ) (v : V) :
    hypergraphDiv H (fun e => c * g e) v = c * hypergraphDiv H g v := by
  unfold hypergraphDiv
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih]
    by_cases h_dst : e.dst = v <;> by_cases h_src : e.src = v <;>
      simp [h_dst, h_src] <;> try ring

theorem hypergraphDiv_zero (H : Hypergraph V) (v : V) :
    hypergraphDiv H (fun _ => 0) v = 0 := by
  unfold hypergraphDiv
  induction H.edges using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih]
    simp

/-! ## Summation by parts

The sum of `f(v) · div(g)(v)` over vertices equals the sum of `g(e) · grad(f)(e)` over edges. -/

/-- For one edge `e`, `∑_v f(v) · ((if dst e = v then g e else 0) − (if src e = v then g e else 0)) = g e · hyperedgeGradient f e`. -/
theorem perEdge_sum_fv_div (e : Hyperedge V) (f : V → ℝ)
    (g : Hyperedge V → ℝ) :
    (∑ v : V, f v *
      ((if e.dst = v then g e else 0) - (if e.src = v then g e else 0)))
    = g e * hyperedgeGradient f e := by
  -- Expand the difference and split into two sums.
  have step : ∀ v : V,
      f v * ((if e.dst = v then g e else 0) - (if e.src = v then g e else 0))
      = f v * (if e.dst = v then g e else 0)
        - f v * (if e.src = v then g e else 0) := by
    intros v; ring
  rw [Finset.sum_congr rfl (fun v _ => step v)]
  rw [Finset.sum_sub_distrib]
  -- The dst-sum collapses to f(dst) · g(e); the src-sum to f(src) · g(e).
  have h_dst_sum : (∑ v : V, f v * (if e.dst = v then g e else 0))
                 = f e.dst * g e := by
    rw [Finset.sum_eq_single e.dst]
    · simp
    · intros v _ hv
      have : e.dst ≠ v := Ne.symm hv
      simp [this]
    · intro hne
      exact absurd (Finset.mem_univ _) hne
  have h_src_sum : (∑ v : V, f v * (if e.src = v then g e else 0))
                 = f e.src * g e := by
    rw [Finset.sum_eq_single e.src]
    · simp
    · intros v _ hv
      have : e.src ≠ v := Ne.symm hv
      simp [this]
    · intro hne
      exact absurd (Finset.mem_univ _) hne
  rw [h_dst_sum, h_src_sum]
  unfold hyperedgeGradient
  ring

/-- Summation by parts for an arbitrary multiset `s` of edges. -/
theorem summation_by_parts_multiset (s : Multiset (Hyperedge V))
    (f : V → ℝ) (g : Hyperedge V → ℝ) :
    (∑ v : V, f v *
      (s.map (fun e =>
        (if e.dst = v then g e else 0) - (if e.src = v then g e else 0))).sum)
    = (s.map (fun e => g e * hyperedgeGradient f e)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons e es ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    -- Distribute f(v) · (e-term + es-sum) and split ∑_v.
    have distrib : ∀ v : V,
        f v * (((if e.dst = v then g e else 0) - (if e.src = v then g e else 0))
                + (es.map (fun e' =>
                    (if e'.dst = v then g e' else 0)
                    - (if e'.src = v then g e' else 0))).sum)
        = f v * ((if e.dst = v then g e else 0) - (if e.src = v then g e else 0))
          + f v * (es.map (fun e' =>
                    (if e'.dst = v then g e' else 0)
                    - (if e'.src = v then g e' else 0))).sum := by
      intros v; ring
    rw [Finset.sum_congr rfl (fun v _ => distrib v)]
    rw [Finset.sum_add_distrib]
    rw [perEdge_sum_fv_div e f g, ih]

/-- `∑_v f(v) · hypergraphDiv H g v = ∑_{e ∈ H.edges} g(e) · hyperedgeGradient f e`. -/
theorem summation_by_parts (H : Hypergraph V) (f : V → ℝ)
    (g : Hyperedge V → ℝ) :
    (∑ v : V, f v * hypergraphDiv H g v)
    = (H.edges.map (fun e => g e * hyperedgeGradient f e)).sum := by
  unfold hypergraphDiv
  exact summation_by_parts_multiset H.edges f g

/-! ## Relation to `laplacianHyper`

No identity between `laplacianHyper` and `hypergraphDiv ∘ hyperedgeGradient` is proved in this module. `laplacianHyper` uses every vertex pair in an edge, while `hyperedgeGradient` uses only `src` and `dst`.
-/

end InfraFormalization
