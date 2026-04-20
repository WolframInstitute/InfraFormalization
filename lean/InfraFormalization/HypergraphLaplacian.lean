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

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a directed hyperedge `e` and a vertex `v`, the **finset of
other vertices** in `e`. For a simple-graph edge `{v, w}` this is the
singleton `{w}`. -/
def Hyperedge.others (e : Hyperedge V) (v : V) : Finset V :=
  e.verts.toFinset.erase v

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

end Hypergraph

end InfraFormalization
