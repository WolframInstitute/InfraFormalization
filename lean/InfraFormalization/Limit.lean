/-
Framework for continuum limits of hypergraphs.

We frame a continuum-limit theorem as follows:

  Given a sequence `(H_n, ε_n) : ℕ → ScaledHypergraph V` with
  `ε_n → 0` (and a marking / basepoint choice), the induced sequence of
  pseudo-metric spaces is claimed to converge (in a specified sense —
  pointed Gromov–Hausdorff, spectral, or Lorentzian GH) to a limiting
  metric-measure space `(M, d, μ)`. If the limit is a smooth Riemannian
  manifold and the sequence satisfies certain regularity, we can lift
  discrete geometric invariants (dimension, Ollivier–Ricci curvature)
  to their continuum analogues (topological dimension, Ricci curvature
  tensor).

This file defines sequences of scaled hypergraphs and metric-measure
targets. It states no convergence theorem.

Mathlib's relevant pieces:
* `Metric.HausdorffDist` and friends (Gromov–Hausdorff).
* `MeasureTheory.Measure` (measure-space convergence).
* `GromovHausdorff` namespace (pointed GH is still partially
  developed at the time of writing).
* `Manifold.IsManifold` (smooth structure for limit targets).

For the Lorentzian case (causal graphs → pseudo-Riemannian manifolds),
Mathlib does not yet have a sufficiently rich API; we state the
corresponding claim with a placeholder and leave the upgrade for when
the Lorentzian-GH Mathlib PR lands (tracked at mathlib4#...).
-/

import InfraFormalization.GraphMetric
import InfraFormalization.Rule
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace InfraFormalization

open Hypergraph

variable {V : Type*} [DecidableEq V]

/-- A **sequence of scaled hypergraphs** for continuum-limit analysis. -/
structure HypergraphSequence (V : Type*) where
  graph : ℕ → Hypergraph V
  ε : ℕ → ℝ
  ε_pos : ∀ n, 0 < ε n
  ε_to_zero : Filter.Tendsto ε Filter.atTop (nhds 0)

/-- Abstract convergence target: a metric-measure space. -/
structure MetricMeasureTarget where
  carrier : Type*
  [metric : PseudoMetricSpace carrier]
  [measurable : MeasurableSpace carrier]
  μ : MeasureTheory.Measure carrier

attribute [instance] MetricMeasureTarget.metric MetricMeasureTarget.measurable

end InfraFormalization
