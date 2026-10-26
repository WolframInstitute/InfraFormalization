/-
The matrix heat kernel solves the discrete heat equation.

`heatKernel H t = exp (t • laplacianMatrix H)` is defined in `LaplacianMatrix.lean` and `HeatSolution` in `HeatEquation.lean`. This module proves that `t ↦ (heatKernel H t).mulVec u₀` satisfies `HeatSolution H`. The proof uses `hasDerivAt_exp_smul_const`, the continuity of `M ↦ M.mulVec u v`, and the commutation of `heatKernel H t` with `laplacianMatrix H`.
-/

import InfraFormalization.LaplacianMatrix
import InfraFormalization.HeatEquation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Operator

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `d/dt heatKernel H t = heatKernel H t * laplacianMatrix H`. -/
theorem hasDerivAt_heatKernel (H : Hypergraph V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatKernel H s)
      (heatKernel H t * laplacianMatrix H) t := by
  unfold heatKernel
  exact hasDerivAt_exp_smul_const (laplacianMatrix H) t

/-- `heatKernel H t` commutes with `laplacianMatrix H`. The proof applies `Commute.exp_left` to the commutation of `t • Δ` with `Δ`. -/
theorem heatKernel_commute_laplacianMatrix (H : Hypergraph V) (t : ℝ) :
    Commute (heatKernel H t) (laplacianMatrix H) := by
  unfold heatKernel
  exact (Commute.smul_left (Commute.refl (laplacianMatrix H)) t).exp_left

/-- For `u : V → ℝ` and `v : V`, the map `M ↦ M.mulVec u v` as a continuous linear map `Matrix V V ℝ →L[ℝ] ℝ`. -/
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

/-- For `u₀ : V → ℝ` and `v : V`, `d/dt (heatKernel H t).mulVec u₀ v = (heatKernel H t * laplacianMatrix H).mulVec u₀ v`. -/
theorem hasDerivAt_heatKernel_mulVec (H : Hypergraph V) (u₀ : V → ℝ)
    (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (heatKernel H s).mulVec u₀ v)
      ((heatKernel H t * laplacianMatrix H).mulVec u₀ v) t := by
  have h_mat := hasDerivAt_heatKernel H t
  have h_clm := (mulVecEvalCLM u₀ v).hasFDerivAt (x := heatKernel H t)
  have := h_clm.comp_hasDerivAt t h_mat
  simpa using this

/-- For a hypergraph `H` on a finite vertex type and any `u₀`, the map `t ↦ (heatKernel H t).mulVec u₀` satisfies `HeatSolution H`. -/
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
