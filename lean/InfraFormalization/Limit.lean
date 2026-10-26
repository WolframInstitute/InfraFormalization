/-
Sequences of scaled hypergraphs and metric-measure targets.

A continuum-limit statement concerns a sequence of hypergraphs `H_n` with scales `ε_n → 0` and the
convergence, in a specified sense (pointed Gromov–Hausdorff, spectral, or Lorentzian), of the
associated metric spaces to a metric-measure space `(M, d, μ)`. This module defines the structure
`HypergraphSequence` of hypergraphs with positive scales tending to 0, and the structure
`MetricMeasureTarget` of a pseudo-metric space with a measure. It states no convergence theorem.
-/

import InfraFormalization.GraphMetric
import InfraFormalization.Rule
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace InfraFormalization

open Hypergraph

variable {V : Type*} [DecidableEq V]

/-- A sequence of hypergraphs `graph n` with scales `ε n > 0` that tend to 0. -/
structure HypergraphSequence (V : Type*) where
  graph : ℕ → Hypergraph V
  ε : ℕ → ℝ
  ε_pos : ∀ n, 0 < ε n
  ε_to_zero : Filter.Tendsto ε Filter.atTop (nhds 0)

/-- A pseudo-metric space with a measurable structure and a measure. -/
structure MetricMeasureTarget where
  carrier : Type*
  [metric : PseudoMetricSpace carrier]
  [measurable : MeasurableSpace carrier]
  μ : MeasureTheory.Measure carrier

attribute [instance] MetricMeasureTarget.metric MetricMeasureTarget.measurable

end InfraFormalization
