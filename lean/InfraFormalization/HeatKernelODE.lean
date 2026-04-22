/-
**Heat kernel ↔ ODE heat equation identification** (task T1).

Unifies the two heat-equation definitions in the project:

  * `HeatSolution H u` (from `HeatEquation.lean`, D1):
    `∀ t v, HasDerivAt (fun s => u s v) (laplacianHyper H (u t) v) t`.
  * `heatKernel H t := exp (t • laplacianMatrix H)` (from `LaplacianMatrix.lean`,
    R2/D3): the matrix exponential propagator.

The link: `t ↦ (heatKernel H t).mulVec u₀` solves the heat ODE with
initial data `u₀`. Proved via `hasDerivAt_exp_smul_const` +
`Matrix.mulVec` as a continuous linear map in the matrix argument +
commutativity of `heatKernel H t` with `laplacianMatrix H`
(via `Commute.exp_left` since scalar multiples of a matrix commute).
-/

import InfraFormalization.LaplacianMatrix
import InfraFormalization.HeatEquation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Operator

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Matrix-level time derivative of the heat kernel**:
`d/dt heatKernel H t = heatKernel H t · laplacianMatrix H`. -/
theorem hasDerivAt_heatKernel (H : Hypergraph V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernel H s)
      (heatKernel H t * laplacianMatrix H) t := by
  unfold heatKernel
  exact hasDerivAt_exp_smul_const (laplacianMatrix H) t

/-- **Heat kernel commutes with the Laplacian matrix**: `Commute` for the
underlying matrices. Follows from `Commute.exp_left` since `t • Δ` commutes
with `Δ` (scalar multiples of a matrix commute with the matrix itself). -/
theorem heatKernel_commute_laplacianMatrix (H : Hypergraph V) (t : ℝ) :
    Commute (heatKernel H t) (laplacianMatrix H) := by
  unfold heatKernel
  exact (Commute.smul_left (Commute.refl (laplacianMatrix H)) t).exp_left

/-- **`Matrix.mulVec` evaluated at a fixed vector and fixed output index
is a continuous linear map on the matrix.** For `u : V → ℝ` and `v : V`:
`(fun M : Matrix V V ℝ => M.mulVec u v) : Matrix V V ℝ →L[ℝ] ℝ`. -/
noncomputable def mulVecEvalCLM (u : V → ℝ) (v : V) :
    Matrix V V ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.mulVec u v
      map_add' := by
        intro M N
        simp [Matrix.add_mulVec, Pi.add_apply]
      map_smul' := by
        intro c M
        show (c • M).mulVec u v = c • M.mulVec u v
        rw [Matrix.smul_mulVec]
        rfl }

@[simp] lemma mulVecEvalCLM_apply (u : V → ℝ) (v : V) (M : Matrix V V ℝ) :
    mulVecEvalCLM u v M = M.mulVec u v := rfl

/-- **Entry-wise time derivative**: for any initial data `u₀ : V → ℝ` and
any vertex `v : V`,
`d/dt (heatKernel H t).mulVec u₀ v = (heatKernel H t · Δ).mulVec u₀ v`. -/
theorem hasDerivAt_heatKernel_mulVec (H : Hypergraph V) (u₀ : V → ℝ)
    (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (heatKernel H s).mulVec u₀ v)
      ((heatKernel H t * laplacianMatrix H).mulVec u₀ v) t := by
  have h_mat := hasDerivAt_heatKernel H t
  have h_clm := (mulVecEvalCLM u₀ v).hasFDerivAt (x := heatKernel H t)
  have := h_clm.comp_hasDerivAt t h_mat
  simpa using this

/-- **Heat kernel solves the discrete heat equation.**

For any finite-vertex hypergraph `H`, the map
`t ↦ (heatKernel H t).mulVec u₀` is a solution of the discrete heat
equation `∂_t u = Δ_H u` with initial data `u₀`. Closes T1 — the ODE
predicate `HeatSolution H` and the matrix propagator `heatKernel H`
are unified. -/
theorem heatKernel_isHeatSolution (H : Hypergraph V) (u₀ : V → ℝ) :
    HeatSolution H (fun t v => (heatKernel H t).mulVec u₀ v) := by
  intro t v
  have h_deriv := hasDerivAt_heatKernel_mulVec H u₀ v t
  -- Target: HasDerivAt (fun s => (heatKernel H s).mulVec u₀ v)
  --         (laplacianHyper H (fun w => (heatKernel H t).mulVec u₀ w) v) t
  -- We have: derivative = (heatKernel H t * Δ).mulVec u₀ v.
  -- Commute: heatKernel H t * Δ = Δ * heatKernel H t.
  have h_commute : heatKernel H t * laplacianMatrix H
                 = laplacianMatrix H * heatKernel H t :=
    heatKernel_commute_laplacianMatrix H t
  rw [h_commute] at h_deriv
  -- Now derivative = (Δ * heatKernel H t).mulVec u₀ v
  --                = Δ.mulVec (heatKernel H t .mulVec u₀) v (Matrix.mulVec_mulVec)
  --                = laplacianHyper H (heatKernel H t .mulVec u₀) v
  rw [← Matrix.mulVec_mulVec, laplacianMatrix_mulVec] at h_deriv
  exact h_deriv

end Hypergraph
end InfraFormalization
