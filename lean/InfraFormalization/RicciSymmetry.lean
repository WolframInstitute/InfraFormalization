import InfraFormalization.CurvatureRiemann
import InfraFormalization.WarpedDiag2C2

/-!
Symmetry of the Ricci tensor.

`ConnectionData n` carries Γ and dΓ and no metric. This module proves that
the Ricci tensor is symmetric at the index pairs where the contracted
Riemann sums agree (`RiemannRicciSymm`), that the Ricci tensor of the flat
connection is symmetric, and that the Ricci tensor of the Levi-Civita
connection of `warpedDiag2_C2` is symmetric.
-/

namespace InfraFormalization
namespace Curvature
namespace ConnectionData

open scoped BigOperators

variable {n : Nat} (C : ConnectionData n)

/-- The contracted Riemann sums `∑ ρ, R^ρ_{σρν}` and `∑ ρ, R^ρ_{νρσ}` are
equal at `x`. -/
def RiemannRicciSymm (x : Fin n → ℝ) (σ ν : Fin n) : Prop :=
  ∑ ρ : Fin n, C.riemann x ρ σ ρ ν = ∑ ρ : Fin n, C.riemann x ρ ν ρ σ

/-- If `RiemannRicciSymm x σ ν` holds, then `ricci x σ ν = ricci x ν σ`.
The hypothesis is the conclusion with `ricci` unfolded. -/
theorem ricci_symm_of_riemannRicciSymm
    (x : Fin n → ℝ) (σ ν : Fin n)
    (h : C.RiemannRicciSymm x σ ν) :
    C.ricci x σ ν = C.ricci x ν σ := by
  unfold ConnectionData.ricci
  exact h

end ConnectionData

/-- The Ricci tensor of the flat connection is symmetric; both sides are 0
by `flatConnection_ricci_zero`. -/
theorem flatConnection_ricci_symm (n : Nat) (x : Fin n → ℝ) (σ ν : Fin n) :
    (flatConnection n).ricci x σ ν = (flatConnection n).ricci x ν σ := by
  rw [flatConnection_ricci_zero, flatConnection_ricci_zero]

/-- The case `n = 4` of `flatConnection_ricci_symm`. -/
theorem minkowski4_flat_ricci_symm (x : Fin 4 → ℝ) (σ ν : Fin 4) :
    (flatConnection 4).ricci x σ ν = (flatConnection 4).ricci x ν σ :=
  flatConnection_ricci_symm 4 x σ ν

/-- The Ricci tensor of the Levi-Civita connection of `warpedDiag2_C2` is
symmetric. Its components are `R_{00} = -1/(1+x₀²)²`, `R_{11} = -1/(1+x₀²)`
and `R_{01} = R_{10} = 0` (`WarpedDiag2C2.lean`). -/
theorem warpedDiag2_leviCivita_ricci_symm (x : Fin 2 → ℝ) (σ ν : Fin 2) :
    warpedDiag2_C2.leviCivitaConnection.ricci x σ ν
      = warpedDiag2_C2.leviCivitaConnection.ricci x ν σ :=
  warpedDiag2_ricci_symm x σ ν

end Curvature
end InfraFormalization
