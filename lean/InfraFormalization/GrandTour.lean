/-
**Grand Tour** — the single-file tour of what's formalised.

Gathers the headline theorems into one file, one claim per line,
with a pointer to the defining module. Useful as a "what's in the
box" sheet for anyone new to the project.

Organised by the bridge-ladder rungs + infrageometry groups.
-/

import InfraFormalization.CycleEigenLimit
import InfraFormalization.CycleMatrixSpectrum
import InfraFormalization.HeatKernelDecay
import InfraFormalization.ContinuumLimitStatement
import InfraFormalization.RemainingObligations
import InfraFormalization.EinsteinEquations
import InfraFormalization.LorentzianManifold
import InfraFormalization.CausalFoliation
import InfraFormalization.PathHypergraph
import InfraFormalization.CurvedRicciBridge
import InfraFormalization.GRMetricsDemo
import InfraFormalization.WolframPhysicsBridgeDemo
import InfraFormalization.ContinuumBridgeDemo

namespace InfraFormalization
namespace GrandTour

/-! ## Operator convergence (Rung 2)

Cycle Laplacian spectrum converges to continuum circle Laplacian. -/

example (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ)^2 * cycleEigenvalue n k)
      Filter.atTop (nhds (-(2 * Real.pi * k)^2)) :=
  cycleEigenvalue_scaled_tendsto k

/-! ## Four-PDE spectrum bridge (D7 + wave + Schrödinger + KG)

The heat, wave, Schrödinger, and Klein-Gordon spectral convergences
for the cycle → circle bridge are unified in one place. -/

example (k : ℕ) : DiscreteWaveToContinuumWave :=
  discreteWaveToContinuumWave_holds

example (k : ℕ) : DiscreteSchrodingerToContinuumSchrodinger :=
  discreteSchrodingerToContinuumSchrodinger_holds

example (k : ℕ) (m : ℝ) : DiscreteKleinGordonSpectrum m :=
  discreteKleinGordonSpectrum_holds m

/-! ## D6 multi-mode heat convergence

Heat flow of any finite eigen-combination tends to the constant mode. -/

example {n : ℕ} [NeZero n] (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k ∧ k < n) (c : ℝ) (d : ℕ → ℝ) (i : Fin n) :
    Filter.Tendsto
      (fun t : ℝ => ((Hypergraph.heatKernel (cycleHypergraph n) t).mulVec
        (c • cycleEigenvector n 0 + ∑ k ∈ S, d k • cycleEigenvector n k)) i)
      Filter.atTop (nhds (c * cycleEigenvector n 0 i)) :=
  heatKernel_cycleHypergraph_multi_mode_tendsto hn S hS c d i

/-! ## T6 infrageometry obligations

Five of seven obligations fully proved. -/

example : FubiniStudyLimitObligation := fubiniStudyBhattacharyya_bound

example : LatschevObligation := latschevObligation_holds

example : ScaleTrichotomyObligation := scaleTrichotomyObligation_holds

example : EMEPersistenceObligation ∧ PathIntegralObligation := no_stub_obligations_remain

/-! ## F3 Einstein equations with Λ

Minkowski+flat vacuum solves vacuum EFE with Λ=0; Λ≠0 is excluded. -/

example (κ : ℝ) (x : Fin 4 → ℝ) :
    EinsteinEqLambda Curvature.minkowski4 (Curvature.flatConnection 4) 0 κ
      StressEnergyTensor.zero x :=
  minkowski4_satisfies_EFE_zero_lambda κ x

example (Λ κ : ℝ) (x : Fin 4 → ℝ)
    (h : EinsteinEqLambda Curvature.minkowski4 (Curvature.flatConnection 4)
           Λ κ StressEnergyTensor.zero x) : Λ = 0 :=
  minkowski4_flat_vacuum_forces_lambda_zero Λ κ x h

/-! ## E1 Lorentzian manifold + E5 Cauchy foliation

Minkowski is a DiagLorentzianManifold; every stably causal DAG admits
a discrete Cauchy foliation. -/

example : Curvature.DiagLorentzianMetric Curvature.minkowski4 :=
  Curvature.minkowski4_diagLorentzian

example {V : Type*} [Fintype V] [DecidableEq V] {G : CausalGraph V}
    (h : G.StablyCausal) : ∃ f : ℕ → Finset V, G.IsFoliation f :=
  CausalGraph.stablyCausal_hasFoliation G h

/-! ## GR metric zoo

Six exact solutions formalised. -/

example : ∃ _ : Curvature.DiagLorentzianManifold 4, True :=
  ⟨Curvature.minkowski4Manifold, trivial⟩

noncomputable example (a da : ℝ → ℝ) : Curvature.PartialMetricData 4 :=
  Curvature.flrwPartial a da

noncomputable example (M : ℝ) : Curvature.PartialMetricData 4 :=
  Curvature.schwarzschildPartial M

/-! ## Wolfram-physics bridges

Heat → continuum on cycle, QM framework from rewriting, PDE spectrum
bridge, curved Ricci non-flat witness. -/

example (k : ℕ) : Filter.Tendsto
    (fun n : ℕ => (n : ℝ)^2 * cycleEigenvalue n k)
    Filter.atTop (nhds (-(2 * Real.pi * k)^2))
  ∧ Filter.Tendsto
    (fun n : ℕ => (n : ℝ) * (2 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ))))
    Filter.atTop (nhds (2 * Real.pi * k))
  ∧ Filter.Tendsto
    (fun n : ℕ => (n : ℝ)^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2))
    Filter.atTop (nhds ((2 * Real.pi * k)^2)) :=
  pde_spectrum_bridge_summary k

example : ∃ (M : Curvature.MetricData 2) (x : Fin 2 → ℝ) (μ ν ρ : Fin 2),
    M.christoffel x ρ μ ν ≠ 0 :=
  curvedRicciBridgeObligation

end GrandTour
end InfraFormalization
