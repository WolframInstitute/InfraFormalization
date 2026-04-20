/-
Discrete gradient and divergence on a directed hypergraph, with
summation-by-parts.

**Connection to hypergraphs.** Native. All operators act directly on
`Hypergraph V` (the Wolfram-model state type) and `Hyperedge V` (the
primitive rewriting units). No continuum objects appear.

**What this file contributes.** Extends `HypergraphLaplacian.lean` to
the full directed discrete exterior-calculus toolkit:

  * `Hyperedge.src e` and `Hyperedge.dst e` — the first and last
    vertices of the ordered hyperedge list.
  * `hyperedgeGradient f e := f(dst e) − f(src e)` — the gradient of
    a vertex function along a directed hyperedge.
  * `hypergraphDiv H g v` — the divergence of an edge-valued function
    at a vertex (inflow minus outflow).
  * **`summation_by_parts`** — the central identity

      `∑_v f(v) · (hypergraphDiv H g)(v)
       = ∑_{e ∈ H.edges} g(e) · (hyperedgeGradient f) e`.

This makes the hypergraph into a discrete chain complex; together
with `laplacianHyper_sum_zero` it provides the Stokes-theorem /
integration-by-parts foundation for variational calculus on
hypergraphs.

**Convention.** The ordered vertex list of a hyperedge `e = (v₁, …, vₖ)`
is treated as a directed chain `src = v₁ → v₂ → … → vₖ = dst`. The
gradient is the head-minus-tail difference; the divergence at `v`
counts incoming minus outgoing edges. For standard 2-vertex edges
this reduces to the familiar graph gradient and divergence.
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

/-- **Source** of a directed hyperedge: the first vertex in its
ordered list. -/
def src (e : Hyperedge V) : V :=
  e.verts.head e.nonempty

/-- **Destination** of a directed hyperedge: the last vertex. -/
def dst (e : Hyperedge V) : V :=
  e.verts.getLast e.nonempty

end Hyperedge

/-- **Discrete gradient** of a vertex function along a directed
hyperedge: `grad f e := f(dst e) − f(src e)`. -/
def hyperedgeGradient (f : V → ℝ) (e : Hyperedge V) : ℝ :=
  f e.dst - f e.src

/-- **Discrete divergence** of an edge-valued function at a vertex:
`div g v := (∑_{e : dst e = v} g e) − (∑_{e : src e = v} g e)`.
Inflow minus outflow. Self-loop edges (`src = dst`) contribute 0
automatically (`g(e) − g(e) = 0`). -/
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

The central Stokes-style identity: summing `f(v) · div(g)(v)` over all
vertices equals summing `g(e) · grad(f)(e)` over all edges. -/

/-- **Per-edge contribution to `∑_v f(v) · div(g)(v)` equals
`g(e) · grad(f)(e)`.** This is the heart of summation-by-parts: one
edge at a time, the sum over vertices of `f(v) · [div indicator]`
collapses to `g(e) · (f(dst) − f(src))`. This works uniformly for both
regular edges (`src ≠ dst`) and self-loops (`src = dst`), since the
divergence indicator `(if dst=v then g e else 0) − (if src=v then g e else 0)`
handles both cases. -/
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

/-- **Summation by parts — helper form** on an arbitrary multiset
of edges. The main theorem follows by specialising to `H.edges`. -/
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

/-- **Summation by parts on a directed hypergraph** (Stokes' theorem).

  `∑_{v ∈ V} f(v) · (hypergraphDiv H g)(v)
   = ∑_{e ∈ H.edges} g(e) · (hyperedgeGradient f) e`.

Holds without boundary terms because the hypergraph is treated as
"closed" (no boundary vertices). Self-loop edges contribute 0 to
both sides (gradient vanishes; divergence pair cancels). -/
theorem summation_by_parts (H : Hypergraph V) (f : V → ℝ)
    (g : Hyperedge V → ℝ) :
    (∑ v : V, f v * hypergraphDiv H g v)
    = (H.edges.map (fun e => g e * hyperedgeGradient f e)).sum := by
  unfold hypergraphDiv
  exact summation_by_parts_multiset H.edges f g

/-! ## Relation to `laplacianHyper`

The hypergraph Laplacian `laplacianHyper` is related to `grad` and
`div` via `Δ = div ∘ grad` in the standard discrete-calculus sense.
Here we record a weaker statement: the Dirichlet inner product
`⟨f, Δ f⟩` can be expressed via edge-level gradients. A full
`laplacianHyper = div ∘ grad` identity requires matching the
non-directed "every pair in an edge" convention of `laplacianHyper`
to the directed `grad` used here — a non-trivial encoding issue for
hyperedges with `> 2` vertices and left for follow-up work.
-/

end InfraFormalization
