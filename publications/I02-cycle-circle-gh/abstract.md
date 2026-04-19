# I02 — Formally-Verified Cycle-to-Circle Gromov–Hausdorff Convergence

**Thesis.** The sequence of scaled $n$-cycle metric spaces $(C_n, \mathrm{cycleDist}/n)$ converges in the Gromov–Hausdorff sense to the unit circle $(\mathbb{R}/\mathbb{Z}, \mathrm{circleDist})$ as $n \to \infty$. Specifically,
$$\mathrm{GH\_dist}\bigl((C_n, \mathrm{cycleDist}/n), (\mathbb{R}/\mathbb{Z}, \mathrm{circleDist})\bigr) \le \frac{1}{2n},$$
witnessed by the lattice embedding $\varphi_n(i) = i/n$, which is exactly isometric and whose image is $(1/(2n))$-Hausdorff-dense in $[0, 1)$. The full chain — $\mathrm{cycleDist}$ is a metric; $\mathrm{circleDist}$ is a metric; $\varphi_n$ is an isometric embedding; the image is $(1/(2n))$-dense — is machine-verified in Lean 4 + Mathlib 4.29.1, all 15 supporting theorems axiom-clean.

**Significance.** This is, to our knowledge, the first formally-verified Gromov–Hausdorff convergence theorem in the infrageometry programme. It provides a concrete, reusable template (`GHApproximation`) for subsequent discrete-to-continuum convergence results — including the path-to-interval and lattice-to-torus variants presented in companion papers I03 and I04.

**Target venue.** arXiv math.MG + math-ph + formal-methods.

**Sufficient Lean support.** T8–T26, especially T19 (`latticeEmbed_covers`), T20 (`latticeEmbed_isometry`), T21 (`cycle_circle_gh_bound`), T26 (`GHApproximation`).

**Length target.** 10–15 pages including the Lean code listings.

**Dependencies on research not yet done.** None. Draftable now.
