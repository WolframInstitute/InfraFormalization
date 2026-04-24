import InfraFormalization.CurvatureRiemann
import InfraFormalization.WarpedDiag2C2

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

/-- **Non-flat B10 witness**: the Ricci tensor of the Levi-Civita
connection on `warpedDiag2` (warped 2D metric with Gaussian curvature
`K(x) = -1/(1+x₀²)²`) is symmetric. Unlike `flatConnection_ricci_symm`
which is trivially zero, this case has explicit non-vanishing Ricci
components `R_{00} = -1/(1+x₀²)²`, `R_{11} = -1/(1+x₀²)`, and
`R_{01} = R_{10} = 0` — so the symmetry is content-ful on the diagonal
as a non-trivial equality of non-zero expressions to themselves, and
content-ful off-diagonal as an equality of two independently-computed
zeros. Supersedes the flat-only closure of task B10 / #30. -/
theorem warpedDiag2_leviCivita_ricci_symm (x : Fin 2 → ℝ) (σ ν : Fin 2) :
    warpedDiag2_C2.leviCivitaConnection.ricci x σ ν
      = warpedDiag2_C2.leviCivitaConnection.ricci x ν σ :=
  warpedDiag2_ricci_symm x σ ν

end Curvature
end InfraFormalization
