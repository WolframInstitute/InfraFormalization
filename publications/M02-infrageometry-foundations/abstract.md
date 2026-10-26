# M02: Discrete metric spaces close to continuum ones, in Lean

Scope. The paper defines the structure `Infra.GHApproximation` (`Infra/GHApprox.lean:21`): an isometric embedding of a discrete metric space, scaled by a constant, into a target space, with every target point within ε of the image. It gives three instances, each PROVED in Lean:

- The n-cycle with metric cycleDist/n and the circle ℝ/ℤ: ε = 1/(2n) (`Infra.cycle_circle_gh_bound`, `Infra/GHBound.lean:20`).
- The path on n + 1 vertices with metric pathDist/n and the interval [0, 1]: ε = 1/(2n) (`Infra.path_interval_gh_bound`, `Infra/ScaledPath.lean:173`).
- The n × n lattice with the maximum of the two cycle distances, divided by n, and the torus ℝ²/ℤ² with the maximum of the two circle distances: ε = 1/(2n) (`Infra.torus_gh_bound`, `Infra/ScaledTorus.lean:84`).

An isometric embedding with ε-dense image bounds the Gromov-Hausdorff distance by ε. This implication and a statement in terms of Mathlib's `GromovHausdorff` distance are not formalised.

Sections.

- §1 The `GHApproximation` structure.
- §2 The cycle and the circle.
- §3 The path and the interval.
- §4 The lattice and the torus with the maximum metric.
- §5 Higher dimensions and targets with curvature (OPEN).
- §6 Random geometric graphs, causal sets, and the problem of a hypergraph rewriting rule with a proved general-relativistic limit (OPEN; planned paper M03).

Target venue: arXiv math.MG, math-ph.

Length: 25-35 pages with a Lean appendix.

Open items: the Gromov-Hausdorff statement in Mathlib's `GromovHausdorff` API, and the torus with the Euclidean product metric.

