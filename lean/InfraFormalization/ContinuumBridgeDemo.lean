/-
Scaled cycle eigenvalue limits.

For each `k : ℕ`, this module collects three limits as `n → ∞`:
`n² · (−4 sin²(πk/n)) → −(2πk)²`, `n · 2 sin(πk/n) → 2πk`, and
`n² · 4 sin²(πk/n) → (2πk)²`, together with the same limit shifted by `m²`.
These are limits of real sequences. No statement about operators or
propagators is made.
-/

import InfraFormalization.CycleEigenLimit
import InfraFormalization.ContinuumLimitStatement

namespace InfraFormalization

open Filter Topology Real

/-- For every `k : ℕ`, as `n → ∞`:
`n² · cycleEigenvalue n k → −(2πk)²`, `n · 2 sin(πk/n) → 2πk`, and
`n² · 4 sin²(πk/n) → (2πk)²`. -/
theorem cycle_scaled_eigenvalue_limits (k : ℕ) :
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

/-- For every `k : ℕ` and `m : ℝ`, `n² · 4 sin²(πk/n) + m² → (2πk)² + m²`
as `n → ∞`. -/
theorem cycle_scaled_kleinGordon_eigenvalue_limit (k : ℕ) (m : ℝ) :
    Tendsto (fun n : ℕ =>
      (n : ℝ)^2 * (4 * (Real.sin (Real.pi * (k : ℝ) / (n : ℝ)))^2) + m^2)
      atTop (𝓝 ((2 * Real.pi * k)^2 + m^2)) :=
  discreteKleinGordonSpectrum_holds m k

end InfraFormalization
