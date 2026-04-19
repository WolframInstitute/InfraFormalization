# M02 — Foundations of Infrageometry: Machine-Checked Discrete-to-Continuum Convergence

**Thesis.** We lay down the foundations of *infrageometry* — the programme of rigorously reframing traditional continuous geometric notions (metric, curvature, volume, differential operators) in terms of discrete structures (graphs, hypergraphs, causal sets) and proving convergence theorems between the two. We define a common abstract `GHApproximation` structure capturing discrete-to-continuum Gromov–Hausdorff convergence, and instantiate it for three concrete continuum-limit theorems: the scaled $n$-cycle converging to the unit circle, the scaled path graph converging to the unit interval, and the scaled $n \times n$ lattice converging to the flat 2-torus. All theorems are machine-verified in Lean 4 + Mathlib 4.29.1, axiom-clean.

**Significance.** This paper is the positive counterpart to the audit paper M01. Where M01 catalogues what has been incorrectly claimed, M02 shows what can be correctly proved in the same general direction. It is the first installment in what we expect to become a systematic library of machine-checked infrageometric results.

**Content.**
- §1 — The `GHApproximation` structure and its properties.
- §2 — Example: scaled cycle to unit circle. Full proof outline.
- §3 — Example: scaled path to unit interval.
- §4 — Example: scaled 2D lattice to flat 2-torus.
- §5 — Toward higher dimensions and non-trivial target curvature.
- §6 — Extensions: random-geometric-graph samples, causal-set samples, and the open research problem of finding hypergraph-rewriting rules with provable GR limits (→ future paper M03).

**Target venue.** arXiv math.MG + math-ph + formal-methods.

**Sufficient Lean support.** The full Phase-3 library plus the `GHApproximation` abstraction: T8–T26, T40.

**Length target.** 25–35 pages including Lean appendix.

**Dependencies on research not yet done.** Strengthenable by formally proving ε-density ⇒ GH-convergence against Mathlib's full `GromovHausdorff` API; not required for the paper to stand.
