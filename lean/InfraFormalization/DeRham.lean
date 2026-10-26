/-
0-forms and 1-forms on a hypergraph.

This module defines 0-forms `V → ℝ`, 1-forms `Hyperedge V → ℝ`, and
`d0 = hyperedgeGradient`. It proves that `d0` is linear and vanishes on
constants, and restates `summation_by_parts` in terms of `d0`. No 2-forms
are defined.
-/

import InfraFormalization.HypergraphCalculus
import InfraFormalization.ScalarField

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Form types -/

/-- A real-valued function on vertices. -/
abbrev ZeroForm (V : Type*) := V → ℝ

/-- A real-valued function on hyperedges. -/
abbrev OneForm (V : Type*) := Hyperedge V → ℝ

/-! ## Exterior derivative `d : 0-forms → 1-forms`

`d0` is `hyperedgeGradient`. -/

/-- The hyperedge gradient of a 0-form. -/
def d0 (ω : ZeroForm V) : OneForm V := hyperedgeGradient ω

/-- `d0` of `ω + η` is `d0 ω + d0 η`. -/
theorem d0_add (ω η : ZeroForm V) :
    d0 (fun v => ω v + η v) = fun e => d0 ω e + d0 η e := by
  funext e
  unfold d0
  exact hyperedgeGradient_add ω η e

theorem d0_smul (c : ℝ) (ω : ZeroForm V) :
    d0 (fun v => c * ω v) = fun e => c * d0 ω e := by
  funext e
  unfold d0
  exact hyperedgeGradient_smul c ω e

theorem d0_const (c : ℝ) : d0 ((fun _ => c) : ZeroForm V) = fun _ => 0 := by
  funext e
  unfold d0
  exact hyperedgeGradient_const c e

/-! ## Summation by parts -/

/-- For a 0-form `ω` and a 1-form `ψ`,
`∑_v ω(v) · (div ψ)(v) = ∑_e ψ(e) · d₀ω(e)`, with the right-hand sum over
the edge multiset of `H`. This is `summation_by_parts`. -/
theorem stokes_zero_to_one (H : Hypergraph V)
    (ω : ZeroForm V) (ψ : OneForm V) :
    (∑ v : V, ω v * hypergraphDiv H ψ v)
    = (H.edges.map (fun e => ψ e * d0 ω e)).sum := by
  unfold d0
  exact summation_by_parts H ω ψ

end InfraFormalization
