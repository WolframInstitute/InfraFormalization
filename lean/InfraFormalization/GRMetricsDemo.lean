/-
**GR metric zoo — centrepiece bundling.**

Collects the GR metric exact solutions formalised in this project
into a single existence statement, demonstrating the breadth of the
continuum-target side of the bridge ladder.

All of these live as `PartialMetricData 4` (or `PartialMetricData 2`
for the 2-sphere) with appropriate validity predicates. Pairing them
with hypergraph rules via convergence bridges is the open programme.

**Metrics formalised:**
  * Minkowski (trivially; `MetricData 4`, no validity predicate).
  * FLRW — expanding universe.
  * Schwarzschild — uncharged, non-rotating black hole.
  * Reissner-Nordström — charged, non-rotating black hole.
  * de Sitter — vacuum with positive cosmological constant.
  * 2-sphere — positively-curved Riemannian target.

**Connection to hypergraphs.** None of these is *produced* by a
hypergraph rule in this project. That's the open direction (and the
Gorard claim under critique). The formalisation here says: *when*
someone produces a rule, this is the concrete formal target they
must converge to.
-/

import InfraFormalization.Schwarzschild
import InfraFormalization.ReissnerNordstrom
import InfraFormalization.DeSitter
import InfraFormalization.FLRW
import InfraFormalization.TwoSphere
import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- **GR metric zoo**: five exact solutions are formalised as
accessible types in this project. Each can serve as a continuum
target for a hypergraph bridge theorem.

This statement packages the existence of all five; it's a status
marker for the scope of formalised target geometry. -/
theorem gr_metric_zoo :
    -- Minkowski as a full MetricData 4.
    (∃ M : MetricData 4, ∀ x μ ν, M.g x μ ν = minkowski4.g x μ ν)
    -- FLRW for every scale-factor pair.
    ∧ (∀ a da : ℝ → ℝ, ∃ P : PartialMetricData 4,
        ∀ x μ ν, P.g x μ ν = flrwG a x μ ν)
    -- Schwarzschild for every mass.
    ∧ (∀ M : ℝ, ∃ P : PartialMetricData 4,
        ∀ x μ ν, P.g x μ ν = sgg M x μ ν)
    -- Reissner-Nordström for every (M, Q).
    ∧ (∀ M Q : ℝ, ∃ g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ,
        ∀ x μ ν, g x μ ν = rnG M Q x μ ν)
    -- de Sitter for every Λ.
    ∧ (∀ Λ : ℝ, ∃ g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ,
        ∀ x μ ν, g x μ ν = dsG Λ x μ ν)
    -- 2-sphere — a curved Riemannian target.
    ∧ (∃ P : PartialMetricData 2, ∀ x μ ν, P.g x μ ν = sphereG x μ ν) := by
  refine ⟨⟨minkowski4, fun _ _ _ => rfl⟩, ?_, ?_, ?_, ?_, ⟨spherePartial, fun _ _ _ => rfl⟩⟩
  · intros a da
    exact ⟨flrwPartial a da, fun _ _ _ => rfl⟩
  · intro M
    exact ⟨schwarzschildPartial M, fun _ _ _ => rfl⟩
  · intros M Q
    exact ⟨rnG M Q, fun _ _ _ => rfl⟩
  · intro Λ
    exact ⟨dsG Λ, fun _ _ _ => rfl⟩

end Curvature
end InfraFormalization
