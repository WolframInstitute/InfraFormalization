import InfraFormalization.CurvatureRiemann

/-!
**Ricci symmetry for the Levi-Civita connection** (B10 / #30).

For a torsion-free metric-compatible connection, the Ricci tensor is
symmetric: `R_{σν} = R_{νσ}`. The deep reason is the pair-symmetry of
the Riemann tensor with both indices lowered,
`R_{ρσμν} = R_{μνρσ}`, which requires metric compatibility `∇g = 0`
in addition to the torsion-free axiom.

Since our `ConnectionData n` carries only Γ and dΓ (not metric
compatibility), we prove the **conditional** form here: *if* the
Riemann tensor has the relevant summation-symmetry, *then* Ricci is
symmetric. The concrete instance for the flat connection follows
trivially (all Riemann components vanish).

Extensions to general Levi-Civita connections await a formalisation of
∇g = 0 — pending, tracked separately.
-/

namespace InfraFormalization
namespace Curvature
namespace ConnectionData

open scoped BigOperators

variable {n : Nat} (C : ConnectionData n)

/-- **Ricci-summation-symmetry hypothesis**: the sum of Riemann over
the contraction indices matches under `σ ↔ ν` swap. This is exactly
what pair-symmetry `R_{ρσμν} = R_{μνρσ}` combined with index-lowering
gives for the Levi-Civita connection; we state it here as an abstract
predicate to separate the algebraic from the metric-compatibility
content. -/
def RiemannRicciSymm (x : Fin n → ℝ) (σ ν : Fin n) : Prop :=
  ∑ ρ : Fin n, C.riemann x ρ σ ρ ν = ∑ ρ : Fin n, C.riemann x ρ ν ρ σ

/-- **Ricci symmetry follows from the Ricci-summation-symmetry
hypothesis.** This is the B10 statement at its most abstract: Ricci
is symmetric on index pairs where the Riemann contraction is. -/
theorem ricci_symm_of_riemannRicciSymm
    (x : Fin n → ℝ) (σ ν : Fin n)
    (h : C.RiemannRicciSymm x σ ν) :
    C.ricci x σ ν = C.ricci x ν σ := by
  unfold ConnectionData.ricci
  exact h

end ConnectionData

/-- **Ricci symmetry on the flat connection.** The Riemann tensor is
identically zero, so both sides of the Ricci-summation-symmetry
hypothesis are trivially `0 = 0`; hence Ricci is symmetric. This is
the B10 sanity check in the trivial-Levi-Civita limit. -/
theorem flatConnection_ricci_symm (n : Nat) (x : Fin n → ℝ) (σ ν : Fin n) :
    (flatConnection n).ricci x σ ν = (flatConnection n).ricci x ν σ := by
  rw [flatConnection_ricci_zero, flatConnection_ricci_zero]

/-- **Concrete B10 witness on Minkowski**: the Ricci tensor of the
flat connection on Minkowski 4-space is symmetric (identically zero
both sides). -/
theorem minkowski4_flat_ricci_symm (x : Fin 4 → ℝ) (σ ν : Fin 4) :
    (flatConnection 4).ricci x σ ν = (flatConnection 4).ricci x ν σ :=
  flatConnection_ricci_symm 4 x σ ν

end Curvature
end InfraFormalization
