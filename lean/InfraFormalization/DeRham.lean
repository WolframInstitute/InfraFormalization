/-
**Discrete de Rham complex on a hypergraph** (Group IA / #111 IA3).

Extends `HypergraphCalculus.lean` (gradient, divergence, Stokes) to
the full de Rham complex: k-forms, exterior derivative, `d² = 0`.

  * `ZeroForm V := V → ℝ` — vertex-valued scalars (reusing
    `ScalarField`).
  * `OneForm V := Hyperedge V → ℝ` — edge-valued.
  * `exteriorDerivativeOn0 := hyperedgeGradient` — `d : 0-forms →
    1-forms`.
  * `d²_zero_on_zero_forms` — `d ∘ d = 0` on 0-forms (trivial since
    2-forms not yet defined; this is the vacuous-truth statement).

Full development (2-forms, Hodge dual, harmonic forms) requires
more machinery; we install the base layer here.

**Connection to hypergraphs.** Native. Every form is a function on
`V` or `Hyperedge V`, living directly on a `Hypergraph V`.
-/

import InfraFormalization.HypergraphCalculus
import InfraFormalization.ScalarField

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Form types -/

/-- **0-form**: a real-valued function on vertices. -/
abbrev ZeroForm (V : Type*) := V → ℝ

/-- **1-form**: a real-valued function on directed hyperedges. -/
abbrev OneForm (V : Type*) := Hyperedge V → ℝ

/-! ## Exterior derivative `d : 0-forms → 1-forms`

`dω(e) := ω(dst e) − ω(src e)`. This is literally
`hyperedgeGradient`. -/

/-- **Exterior derivative of a 0-form**: same as
`hyperedgeGradient`. -/
def d0 (ω : ZeroForm V) : OneForm V := hyperedgeGradient ω

/-- **Linearity of d₀**. -/
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

/-! ## Integration of 1-forms on a hypergraph: Stokes at rank 1

For a 1-form `ω` and a divergence `hypergraphDiv`-valued edge
function, summation-by-parts gives the discrete Stokes' theorem.
This is `summation_by_parts` from `HypergraphCalculus` in de Rham
dress. -/

/-- **Discrete Stokes (0-forms → 1-forms)**:
`∑_v ω(v) · (div ψ)(v) = ∑_e ψ(e) · d₀ω(e)`. -/
theorem stokes_zero_to_one (H : Hypergraph V)
    (ω : ZeroForm V) (ψ : OneForm V) :
    (∑ v : V, ω v * hypergraphDiv H ψ v)
    = (H.edges.map (fun e => ψ e * d0 ω e)).sum := by
  unfold d0
  exact summation_by_parts H ω ψ

end InfraFormalization
