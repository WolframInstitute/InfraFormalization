/-
Top-level module of the `InfraFormalization` Lean library.

**Purpose.** Formalize the mechanics of directed hypergraph rewriting
in a way that supports proving continuum-limit theorems — and use that
machinery to formally state, where possible, refutations of Gorard's
2004.14810 / 2102.09363 / 2303.07282 claims that survive the
project's multi-rail verification (see ../README.md).

Layout:
  * `Hypergraph.lean`  — directed multi-hypergraphs on an abstract
                         vertex type.
  * `Rule.lean`        — pattern-level rewriting rules; conservativity
                         predicate.
  * `Application.lean` — application of a rule at a binding; produced
                         / consumed hyperedges.
  * `Conservation.lean`— Theorem A: conservative rules preserve state
                         size.
  * `GraphMetric.lean` — graph metric and scaled hypergraphs (the
                         latter makes hypergraphs live in a metric
                         space compatible with Mathlib's GH API).
  * `Growth.lean`      — ball / cone counting, growth-exponent
                         predicate, and the linear-cone / no-higher-
                         dim CLAIM theorems.
  * `Limit.lean`       — type-level scaffolding for continuum limits
                         (Gromov–Hausdorff, metric-measure convergence).
  * `Causal.lean`      — causal graph construction from a trajectory.
  * `Branchial.lean`   — placeholder for branchial structure.
  * `Multiway.lean`    — abstract rewriting systems and confluence.

Everything above `Conservation.lean` is a definition; the theorems in
`Conservation.lean` and `Growth.lean` are the first formally-stated
results of the project, with `Conservation.lean` containing an actually-
proved result.
-/

import InfraFormalization.Hypergraph
import InfraFormalization.Rule
import InfraFormalization.Application
import InfraFormalization.Conservation
import InfraFormalization.GraphMetric
import InfraFormalization.Growth
import InfraFormalization.Limit
import InfraFormalization.Causal
import InfraFormalization.Branchial
import InfraFormalization.Multiway
import InfraFormalization.ParallelSchedule
import InfraFormalization.Demo
