# Bridge machinery: hypergraph rewriting ↔ continuous mathematical physics

What Lean infrastructure is needed to connect the Wolfram-model rewriting side (causal graphs, branchial structure, discrete events) to continuous mathematical physics (Riemannian/Lorentzian manifolds, ODEs, PDEs, fields, gauge theory). This is a map — the rungs of the ladder, with explicit scope honesty about what Mathlib has and what we (or Mathlib contributors) must still build.

## Rung 1 — Discrete calculus on graphs

**Goal.** Transfer the basic operations of calculus to the graph-theoretic setting, as the first ingredient of a "graph as a discrete manifold" correspondence.

**What we need:**
- Graph / hypergraph Laplacian: `Δf(v) := ∑_{w ∼ v} (f(w) − f(v))`.
- Discrete gradient `(∇f)(e) := f(head(e)) − f(tail(e))` on directed edges.
- Discrete divergence, compatible with gradient via summation by parts.
- Discrete inner product `⟨f, g⟩ := ∑_v f(v) g(v)` (or with a measure weight).
- Self-adjointness of the graph Laplacian under the uniform measure.
- Heat semigroup `e^{−tΔ}` on the finite graph — a discrete ODE system.

**Status.** None of these is in our Lean corpus. The theory is elementary but requires writing. Most parts are formalisable in ~200 lines each. Mathlib has `SimpleGraph` but not the Laplacian as a linear operator.

**Actionable first step:** formalise the graph Laplacian on a `Hypergraph V` with `[Fintype V]`, prove linearity and self-adjointness. (Started in `lean/InfraFormalization/DiscreteCalculus.lean`.)

## Rung 2 — Convergence to continuous operators

**Goal.** Show discrete operators on a scaled lattice converge to continuous operators on the GH-limit manifold.

**Canonical result:** scaled cycle's graph Laplacian → `d²/dx²` on the circle, acting on smooth periodic test functions.

  `n² · Δ_{C_n}(f∘φ_n) (i) → f''(i/n)` as `n → ∞`, for `f ∈ C²(S¹)`.

**What we need:**
- Scaled graph Laplacian `n² · Δ` (to match the `1/n²` scaling of double differences).
- Notion of "discrete test function" obtained by restricting a smooth function to lattice points.
- Pointwise convergence theorem.
- Uniform convergence on `C^k` compacts (later).

**Status.** All pieces are doable with Mathlib's `Real.Deriv` and `Polynomial` / `Continuous.deriv` infrastructure, which is in place. The convergence theorems haven't been written but involve no open mathematics — they are textbook numerical analysis.

**Actionable first step:** formalise the `n → ∞` limit of `n² · (f((i+1)/n) − 2 f(i/n) + f((i-1)/n))` → `f''(i/n)` for `f ∈ C²([0, 1])`, then lift to the circle.

## Rung 3 — Measure-theoretic limits

**Goal.** Convert metric-space convergence (GH) to metric-measure-space convergence (mGH). This is needed for anything involving integrals or probability in the limit.

**What we need:**
- `MetricMeasureSpace` structure (pseudometric + finite measure, possibly normalised).
- Wasserstein distance `W_p` between probability measures on a metric space. *Mathlib has this* in `Mathlib.MeasureTheory.Measure.WassersteinDistance`.
- Gromov–Hausdorff–Prokhorov distance (`d_GHP`). *Mathlib does not have this*.
- Convergence of counting measures on lattice points to Lebesgue measure on the limit manifold.

**Status.** Wasserstein is in place. The GH-Prokhorov construction isn't. It's ~500 lines of formalisation of Villani's textbook. For our rule-search use case, we can often bypass it by working directly with counting measures.

**Actionable first step:** define `CountingMeasure` on a finite `Hypergraph` and prove it converges weakly to Lebesgue measure on the GH-limit manifold in specific cases (cycle → circle).

## Rung 4 — Connections and parallel transport

**Goal.** Formalise the Levi-Civita connection on a Riemannian manifold, as the prerequisite for curvature.

**What we need:**
- Riemannian metric as a smooth section of `Sym²(T*M)`. Mathlib has `Bundle.Section`, but the smooth Riemannian metric bundle is not a first-class object.
- Torsion-free condition on a connection.
- Metric compatibility condition.
- **Existence and uniqueness of the Levi-Civita connection** (Koszul formula).
- Christoffel symbols in local coordinates.

**Status.** Mathlib has:
- `Mathlib.Geometry.Manifold.ContMDiff` — smooth maps.
- `Mathlib.Geometry.Manifold.VectorBundle.*` — vector bundles.
- `Mathlib.Geometry.Manifold.Algebra.Monoid` etc. — group structure on manifolds.

Mathlib does *not* have:
- Smooth Riemannian metric as a structure.
- Levi-Civita connection.
- Covariant derivative as an operator on smooth vector fields.

This rung is the first major formalisation effort. Each item is ~500–1000 lines. The full Levi-Civita existence-uniqueness theorem is a substantial project.

**Actionable first step:** define `RiemannianMetric M` as a smooth section of `Sym²(T*M)` with positivity. Then `def LeviCivita (g : RiemannianMetric M) : Connection M` with the Koszul formula as the construction. A partial Mathlib PR could ship just the local-coordinate (Christoffel symbols) form as a numerical object on `ℝⁿ`, leaving the bundle-theoretic formulation for a later PR.

## Rung 5 — Riemann, Ricci, scalar curvature

**Goal.** Machine-checkable definitions of the curvature tensors needed to state Einstein's equations.

**What we need:**
- `RiemannTensor g`: `(X, Y, Z) ↦ ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`.
- `RicciTensor g`: trace of the Riemann tensor over the first and third indices.
- `ScalarCurvature g`: trace of Ricci against the inverse metric.
- Einstein tensor `G_{ab} := R_{ab} − ½ R g_{ab}`.
- Bianchi identities (second-order invariants).

**Status.** All of this depends on Rung 4. The definitions themselves are mechanical once the connection is formalised; the theorems (Bianchi, symmetry of Ricci, etc.) are textbook and doable.

**Actionable plan.** The minimum viable formalisation would be:
1. Define Riemann, Ricci, scalar curvature *in local coordinates* on a chart, given Christoffel symbols as input. This avoids the bundle machinery.
2. Prove the coordinate-change formula (tensor transformation).
3. Later, lift to coordinate-free definitions once Rung 4 is in place.

This coordinate-chart approach is the pragmatic route: it gives us usable curvature objects for explicit metrics (Minkowski, Schwarzschild in Schwarzschild coords, FLRW) without waiting for full bundle machinery.

## Rung 6 — ODEs and PDEs

**Goal.** Formalise the differential equations that mathematical physics actually uses — ODE existence-uniqueness, PDE well-posedness.

**What we need:**
- Basic ODE theory: `Picard–Lindelöf` existence-uniqueness. *Mathlib has partial forms in `Mathlib.Analysis.ODE`.*
- Cauchy problem for hyperbolic PDEs: wave equation, Klein–Gordon. Not in Mathlib.
- Cauchy problem for Einstein's equations. Not in Mathlib; this is research-level (Choquet-Bruhat 1952, et seq.).
- Discretisation error analysis: finite-difference schemes, convergence rates.

**Status.** Classical ODE theory is partially formalised; PDE theory is minimal.

**Actionable first step:** formalise the discrete heat equation on a finite graph (`u'(t) = −Δ u(t)`) as a concrete ODE in `Mathlib.Analysis.ODE`. Prove existence-uniqueness trivially (finite dimension). Then show convergence to the continuous heat equation on the GH-limit manifold (hard but doable for the cycle case).

## Rung 7 — Fields, gauge theory

**Goal.** Formalise field theories — scalar fields, gauge fields, tensor fields — as smooth sections of appropriate bundles.

**What we need:**
- Sections of vector bundles (Mathlib has pieces).
- Yang–Mills connections (principal bundles, curvature).
- Lagrangian density as a functional on the section space.
- Euler–Lagrange equations as the critical-point condition.

**Status.** Far away. This is the territory of [HepLean](https://heplean.com/) and similar projects. Pieces exist; a coherent framework doesn't.

## Rung 8 — Lorentzian geometry, causal theory

**Goal.** Formalise the causal-theoretic framework in which general relativity lives.

**What we need:**
- Lorentzian metric as a non-degenerate symmetric bilinear form of signature `(−, +, +, +)`.
- Chronological and causal relations, forward/backward cones.
- Causality, strong causality, global hyperbolicity.
- Cauchy surfaces, foliations, ADM decomposition.
- Penrose diagrams / conformal completions.

**Status.** Our `Infra/LorentzLattice.lean` + `Infra/Minkowski.lean` gives the L∞-metric discrete version. Continuum Lorentzian geometry in Mathlib is minimal — this is a major open formalisation task.

## Rung 9 — Einstein's equations

**Goal.** State and (for specific cases) prove `G_{ab} = 8π T_{ab}`.

**What we need:**
- Rungs 4, 5, 8 fully in place.
- Stress-energy tensor as a section.
- Energy conditions (weak, strong, dominant).
- Specific solutions: Schwarzschild, Kerr, FLRW.

**Status.** Not achievable short-term. The pragmatic route is to state EFE in coordinate form on explicit charts, verify specific solutions symbolically.

## Rung 10 — Hypergraph → continuous bridges

**Goal.** The actual research payoff — show that specific hypergraph rewriting rules' causal graphs converge to specific continuum solutions of rungs 5, 6, 8, 9.

**What we need:** everything above, plus:
- Scaling analysis: how do time/space coordinates scale with trajectory length and hypergraph size?
- Convergence theorems: GH (Rung 3), weak operator convergence (Rung 2), spectral convergence.
- Matching theorems: discrete Ricci-like quantity (Ollivier, Forman) → continuum Ricci.

**Status.** This is where our current cycle→circle, torus→torus results live. Extending to curved targets requires Rungs 4–5 on the continuum side and a discrete curvature definition on the hypergraph side (Ollivier, Forman, BD-action — we have statement-only forms).

---

## Summary table — realistic near-term targets

| Rung | Mathlib status | Our status | Actionable now? |
|---|---|---|---|
| 1. Discrete calculus | Partial | **Done**: Laplacian + self-adjoint + Dirichlet form + PSD + cycle instance. | ✓ shipped. |
| 2. Op. convergence | Infrastructure in place | **Started**: polynomial case exact (`SecondDifference.lean`); `C²` Taylor remainder pending. | **Yes** — Taylor case next. |
| 3. Measure limits | Wasserstein present | Not started | Partial — bypass Prokhorov by using counting measures directly. |
| 4. Connections | Missing | Not started | Needs design; 500+ lines minimum for local-coord form. |
| 5. Curvature tensors | Missing | Statement-only | Start with local-coord (Christoffel) form — doable. |
| 6. ODE/PDE | ODE partial, PDE missing | Not started | ODE for finite graphs: easy. PDE: hard. |
| 7. Fields / gauge | Minimal | Not started | Long-term via HepLean. |
| 8. Lorentzian | Minimal in Mathlib | Discrete version done (us) | Continuum Lorentzian in Lean: major gap. |
| 9. EFE | Impossible without 4-5, 8 | Impossible | Not soon. |
| 10. Bridges | — | `dTorus_gh_bound`, `lorentzIntEmbed` | Flat-target bridges done; curved needs rung 5. |

## Priority order (what to grind next)

1. **Rung 1** — graph Laplacian on `Hypergraph V` + self-adjointness + basic spectral facts.
2. **Rung 2** — scaled cycle Laplacian → continuous `d²/dx²` on circle, as the prototype convergence.
3. **Rung 5 (local-coord route)** — Riemann/Ricci tensors in charts, given Christoffel symbols. Skip bundles.
4. **Rung 6 (ODE route)** — discrete heat equation as an ODE, continuity-limit theorem.
5. **Rung 8 (continuum Lorentzian)** — extend `Infra/Minkowski.lean` toward curved Lorentzian charts (Schwarzschild in explicit coords).

The first two are immediate; the third is the first real curvature rung that's doable without waiting for Mathlib.
