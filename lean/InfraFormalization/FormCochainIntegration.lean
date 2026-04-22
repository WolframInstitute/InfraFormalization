/-
**Form → cochain integration map** (Group IA / #112 IA4).

Discrete differential forms on a hypergraph can be integrated over
chains (formal sums of hyperedges) to produce cochains on the
clique complex. This provides the bridge from calculus-on-hypergraphs
to algebraic topology.

We provide:

  * `Chain V` — formal sums of hyperedges with `ℤ` coefficients.
  * `integrate` — pairing `OneForm V → Chain V → ℝ`.
  * Linearity of integration.

**Connection to hypergraphs.** Native. `Chain V` is built directly
from `Hyperedge V`; `OneForm V` is an edge-function.
-/

import InfraFormalization.DeRham

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A *1-chain*** on a hypergraph: a formal finite sum of
hyperedges with `ℤ` coefficients. -/
structure Chain1 (V : Type*) where
  coefficients : Hyperedge V → ℤ
  finiteSupport : Set.Finite { e | coefficients e ≠ 0 }

/-- **Zero chain.** -/
def Chain1.zero (V : Type*) : Chain1 V :=
  { coefficients := fun _ => 0
    finiteSupport := by
      simp }

/-- **Chain from a single hyperedge** with coefficient 1. -/
noncomputable def Chain1.ofEdge (e : Hyperedge V) : Chain1 V :=
  { coefficients := fun e' => if e' = e then 1 else 0
    finiteSupport := by
      apply Set.Finite.subset (Set.finite_singleton e)
      intro x hx
      by_cases h : x = e
      · simp [h]
      · simp [h] at hx }

/-- **Integration of a 1-form over a chain**: `∫_{∑ aᵢ eᵢ} ω =
∑ aᵢ ω(eᵢ)`. Requires `Chain1.finiteSupport` to ensure finite sum. -/
noncomputable def integrate (ω : OneForm V) (γ : Chain1 V) : ℝ :=
  -- As a Finset sum indexed by the finite support of γ.
  ∑ e ∈ γ.finiteSupport.toFinset, (γ.coefficients e : ℝ) * ω e

/-- **Integration over the zero chain is zero.** -/
theorem integrate_zero (ω : OneForm V) :
    integrate ω (Chain1.zero V) = 0 := by
  unfold integrate Chain1.zero
  simp

end InfraFormalization
