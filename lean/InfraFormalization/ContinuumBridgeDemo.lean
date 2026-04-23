/-
**PDE continuum-limit bridge** — centrepiece theorem.

Given any integer wavenumber `k`, the `k`-th eigenmode of the
discrete-cycle Laplacian scales correctly to the continuum circle
Laplacian eigenvalue across all three standard PDEs:

  * heat equation: spectral decay rate `n² · (−4 sin²(πk/n)) → −(2πk)²` (A4)
  * wave equation: dispersion frequency `n · 2 sin(πk/n) → 2πk`
  * Schrödinger equation: Hamiltonian eigenvalue `n² · 4 sin²(πk/n) → (2πk)²`

This file assembles all three convergence theorems into a single
`pde_spectrum_bridge_summary` — the formal analog of "rescaled cycle
propagators converge to continuum circle propagators at the spectral
level" across the three flagship PDEs.

Full operator/propagator convergence requires a unitary / semigroup
convergence theorem that composes these eigenvalue convergences; the
spectral bridge is the foundational ingredient.
-/

import InfraFormalization.CycleEigenLimit
import InfraFormalization.ContinuumLimitStatement

namespace InfraFormalization

open Filter Topology Real

/-- **PDE spectrum bridge** — triple summary.

For every wavenumber `k ∈ ℕ`, as `n → ∞`:
  * `n² · cycleEigenvalue n k → −(2πk)²`  (A4, heat/Schrödinger Hamiltonian)
  * `n · 2 sin(πk/n) → 2πk`                (wave dispersion frequency)
  * `n² · 4 sin²(πk/n) → (2πk)²`           (Schrödinger Hamiltonian magnitude)

All three are the `k`-th circle-Laplacian eigenvalue content, in the
three spectral forms that feed the three flagship PDE propagators. -/
theorem pde_spectrum_bridge_summary (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 * cycleEigenvalue n k) atTop
        (𝓝 (-(2 * π * k)^2))
    ∧ Tendsto (fun n : ℕ =>
        (n : ℝ) * (2 * Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))) atTop
        (𝓝 (2 * Real.pi * k))
    ∧ Tendsto (fun n : ℕ =>
        (n : ℝ)^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2)) atTop
        (𝓝 ((2 * Real.pi * k)^2)) := by
  refine ⟨cycleEigenvalue_scaled_tendsto k, ?_, ?_⟩
  · exact discreteWaveToContinuumWave_holds k
  · exact discreteSchrodingerToContinuumSchrodinger_holds k

/-- **Four-PDE spectrum bridge including Klein-Gordon** — summary with
massive KG added. For every `k ∈ ℕ` and mass `m ∈ ℝ`, the lattice KG
dispersion `n² · 4 sin²(πk/n) + m²` converges to the continuum KG
Hamiltonian eigenvalue `(2πk)² + m²`. -/
theorem pde_spectrum_bridge_summary_with_mass (k : ℕ) (m : ℝ) :
    Tendsto (fun n : ℕ =>
      (n : ℝ)^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2) + m^2)
      atTop (𝓝 ((2 * Real.pi * k)^2 + m^2)) :=
  discreteKleinGordonSpectrum_holds m k

end InfraFormalization
