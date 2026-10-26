# I02: The scaled n-cycle and the unit circle in Lean

Result. For n > 0, the map φ_n(i) = i/n from the n-cycle with metric cycleDist/n to the circle ℝ/ℤ with metric circleDist, represented on [0, 1), is an isometric embedding, and every point of [0, 1) lies within circle distance 1/(2n) of its image (PROVED: `Infra.cycle_circle_gh_bound`, `Infra/GHBound.lean:20`, from `Infra.latticeEmbed_isometry` and `Infra.latticeEmbed_covers` in `Infra/Circle.lean`). An isometric embedding with ε-dense image bounds the Gromov-Hausdorff distance by ε, so the Gromov-Hausdorff distance between the scaled n-cycle and the circle is at most 1/(2n). This last implication is not formalised: the Lean statement is the embedding and the density bound, and it does not use Mathlib's `GromovHausdorff` distance.

The structure `Infra.GHApproximation` (`Infra/GHApprox.lean:21`
) records an isometric embedding with a scale and a density bound ε. The path and torus cases (I03, I04) are instances of it.

Target venue: arXiv math.MG, math-ph.

Length: 10-15 pages with the Lean listings.

Open items before drafting: a statement of the bound in terms of Mathlib's `GromovHausdorff.ghDist`.
