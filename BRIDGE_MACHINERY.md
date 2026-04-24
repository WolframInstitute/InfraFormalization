# Bridge machinery: hypergraph rewriting → continuous mathematical physics

What Lean infrastructure is needed to connect the Wolfram-model rewriting side (causal graphs, branchial structure, discrete events) to continuous mathematical physics (Riemannian/Lorentzian manifolds, ODEs, PDEs, fields, gauge theory).

## Grounding principle (non-negotiable)

**Every continuous structure in this corpus must be reachable from hypergraph rewriting** via a continuum-limit theorem or a discrete-approximation construction. We do not import or define continuous mathematical objects as standalone islands. Each rung of the ladder either:

1. Is itself a *discrete* structure on a hypergraph / causal graph / trajectory, or
2. Is the *limit* of such a discrete structure under a specified scaling, or
3. Is the *target* of an explicit discrete approximation, with the approximation operator + convergence theorem also formalised.

This is what differentiates the present work from Gorard's: he wrote `g_{ab}, R, R_{μν}, ∫ d⁴x √(−g) R, G_{ab} = 0` symbolically, bundled with prose claims of derivation from Wolfram-model dynamics, but never closed the loop. Our job is to close the loop. **Every continuous object below is required to carry, or to lead toward, an explicit hypergraph origin.**

## Rung 1 — Discrete calculus on graphs

**Connection to hypergraphs.** Native: this rung *is* hypergraph calculus, as the graph Laplacian / inner product / Dirichlet form are all defined directly on `Neighbourhood V` over a `Fintype V`. The hypergraph case (replace adjacency with a directed-hyperedge incidence relation) reuses the same machinery.

**Goal.** Transfer the basic operations of calculus to the graph-theoretic setting, as the first ingredient of a "graph as a discrete manifold" correspondence.

**Decomposition:**
- ✓ Graph Laplacian: `Δf(v) := ∑_{w ∼ v} (f(w) − f(v))`. (`DiscreteCalculus.lean`)
- ✓ Discrete inner product `⟨f, g⟩ := ∑_v f(v) g(v)`. (`DiscreteCalculus.lean`)
- ✓ Self-adjointness `⟨Δ f, g⟩ = ⟨f, Δ g⟩`. (`DiscreteCalculusSymm.lean`)
- ✓ Dirichlet form `⟨f, −Δ f⟩ = ½ ∑ (f(w) − f(v))²`. (`DiscreteCalculusSymm.lean`)
- ✓ Positive semidefiniteness of `−Δ`. (`DiscreteCalculusSymm.lean`)
- ✓ Discrete divergence theorem `∑ Δf = 0`. (`DiscreteCalculusSymm.lean`)
- ✓ Laplacian as `LinearMap`. (`DiscreteCalculus.lean`)
- ✓ Cycle graph instance with `cycleLaplacian = secondDifference`. (`CycleGraph.lean`)
- [ ] Discrete gradient on directed hyperedges `(∇f)(e) := f(head e) − f(tail e)`.
- [ ] Discrete divergence on a hyperedge multiset, compatible with `∇` via summation by parts.
- ✓ **Hypergraph Laplacian** (`HypergraphLaplacian.lean`): defined on `Hypergraph V` directly, linearity proven. The "Wolfram-model state IS a discrete-calculus domain" anchor.
- ✓ **Hypergraph Laplacian as a matrix** (`LaplacianMatrix.lean`): `laplacianMatrix H : Matrix V V ℝ`; `laplacianMatrix_mulVec = laplacianHyper`; symmetric; row-sum zero; kills constants.
- ✓ **Heat kernel via `Matrix.exp`** (`LaplacianMatrix.lean`): `heatKernel H t := exp(t · laplacianMatrix H)`; `heatKernel_zero = 1`, `heatKernel_add` (semigroup); `heatTrace` defined, `heatTrace_zero = |V|`. Closes R2 / D3.

## Rung 2 — Convergence of discrete operators to continuous ones

**Connection to hypergraphs.** This rung *is* the bridge: scaled discrete operators on `Fin n` (or in general on a finite vertex set indexed by a scale parameter) converge pointwise to differential operators on the GH-limit manifold. No standalone continuous calculus — every continuous derivative we use is the limit of a discrete operator we've already constructed.

**Canonical result:** scaled cycle's graph Laplacian → `d²/dx²` on the circle, acting on smooth periodic test functions.
  `n² · Δ_{C_n}(f∘φ_n) (i) → f''(i/n)` as `n → ∞`, for `f ∈ C²(S¹)`.

**Decomposition:**
- ✓ Central second difference `Δ²_h f(x) := f(x+h) − 2 f(x) + f(x−h)`. (`SecondDifference.lean`)
- ✓ Polynomial-case exact identity: for any quadratic, `Δ²_h f(x) = f''(x) · h²`. (`SecondDifference.lean`)
- ✓ `cycleLaplacian` is the second difference. (`SecondDifference.lean`)
- ✓ **`C²` Taylor-remainder version**: `Δ²_h f(x) / h² → f''(x)` for any `ContDiff ℝ 2 f` (`CTwoTaylor.lean`, `scaledSecondDiff_tendsto_iteratedDeriv`), via Mathlib's `Real.taylor_tendsto` (Peano remainder). Closes R1 / A2.
- ✓ **Sequence-along-integers version**: `scaledSecondDiff f n x → iteratedDeriv 2 f x` as `n → ∞` for any C² f (`ScaledDiffC2Bridge.lean`, `scaledSecondDiff_tendsto_iteratedDeriv_C2`).
- ✓ **Hypergraph-anchored scaled Laplacian** = `scaledSecondDiff` at interior indices (`ScaledDiffC2Bridge.lean`, `hypergraph_scaled_laplacian_eq_scaledSecondDiff`). Closes A3.
- [ ] Uniform convergence on `C^k` compacts (weaker than pointwise; work follow-up).
- ✓ **Cycle Laplacian spectrum closed form**: `cycleEigenvector n k (j) = cos(2πkj/n)`, `cycleEigenvalue n k = −4 sin²(πk/n)`, satisfying the eigenvalue equation at all indices including boundary (`CycleSpectrum.lean`, `cycleLaplacian_eigen`). Closes R5.
- ✓ **Eigenvalue convergence**: `n² · cycleEigenvalue n k → −(2πk)²` (`CycleEigenLimit.lean`, `cycleEigenvalue_scaled_tendsto`). Closes A4.
- ✓ **Matrix-level eigenvalue equation** (`CycleMatrixSpectrum.lean`, `laplacianMatrix_cycleHypergraph_eigen`): the cycle eigenvectors are genuine matrix eigenvectors of `laplacianMatrix (cycleHypergraph n)`.
- ✓ **Mathlib `HasEigenvalue` form** (`CycleHasEigenvalue.lean`, `laplacianMatrix_cycleHypergraph_hasEigenvalue`, T4): connects to Mathlib's spectral-theory API.
- ✓ **Matrix exp fixes eigenvectors** (`ExpEigenvector.lean`, `exp_mulVec_of_eigenvector`, T2): general operator fact; in particular `heatKernel_mulVec_const` shows heat kernel fixes constants.
- [ ] Generalisation: scaled torus / lattice Laplacians → continuous Laplace-Beltrami on the limit torus.

## Rung 3 — Measure-theoretic limits

**Connection to hypergraphs.** Native: counting measure on a finite hypergraph (uniform on vertices) is the discrete object; weak / Wasserstein convergence to Lebesgue measure on the GH-limit manifold is the bridge.

**Decomposition:**
- ✓ Wasserstein distance is in Mathlib (`MeasureTheory.Measure.WassersteinDistance`).
- ✓ **`countingMeasure H : Measure V`** — finite uniform measure on the vertex set (`HypergraphMeasure.lean`, A5). `countingMeasure_univ = |V|`.
- ✓ **`uniformProbability H`** — normalised probability measure on V. `uniformProbability_univ = 1` for `Nonempty V`.
- ✓ **`pushforwardCounting`, `pushforwardUniform`** — push forward under any embedding `V → X` via `Measure.map`.
- [ ] **Weak convergence**: counting measure on `Fin n` (uniform) under `latticeEmbed n` converges weakly to Lebesgue on `[0, 1)` as `n → ∞`.
- [ ] Wasserstein-1 convergence rate: `W₁(counting_n, Lebesgue) ≤ C/n`.
- [ ] Lift to (d+1)-torus.
- [ ] Gromov-Hausdorff-Prokhorov distance (full machinery; ~500 lines of Villani).

## Rung 4 — Connections, parallel transport, Levi-Civita (bundle-theoretic)

**Connection to hypergraphs.** This rung needs an explicit bridge: a *discrete connection* on a hypergraph (parallel-transport along edges) whose continuum limit is the Levi-Civita connection of the GH-limit Riemannian manifold. We do **not** treat Mathlib's smooth bundles as a pre-existing target unconnected to our work — we build both the discrete connection and the limit theorem.

**Decomposition (was previously punted; now an explicit roadmap):**

### 4.1 Bundle infrastructure
- [ ] `RiemannianMetric M` for `M` a smooth manifold: smooth section of `Sym²(T*M)` with positive-definiteness.
- [ ] Inverse metric as a smooth section.
- [ ] Tangent-bundle frames; orthonormal frames.

### 4.2 Connections (general)
- [ ] `Connection (E : VectorBundle B)`: covariant derivative `∇ : Γ(E) → Γ(T*B ⊗ E)` on smooth sections.
- [ ] Christoffel symbols of a connection in local coordinates (recovering our `CurvatureLocalCoord.christoffel`).
- [ ] Torsion: `T(X, Y) := ∇_X Y − ∇_Y X − [X, Y]`.
- [ ] Curvature operator: `R(X, Y) Z := ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`.

### 4.3 Levi-Civita
- [ ] Existence + uniqueness theorem (Koszul formula): given a Riemannian metric, there is a unique torsion-free metric-compatible connection.
- [ ] Christoffel symbols from the metric: `Γ^ρ_{μν} = ½ g^{ρσ} (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})` (matching local-coord version).
- [ ] Coordinate-change formula (tensor transformation law).

### 4.4 Discrete connection on hypergraphs (the hypergraph anchor)
- [ ] **`DiscreteConnection (H : Hypergraph V)`**: parallel-transport map from each `v` to each neighbour `w`; an element of `Aut(F_v → F_w)` for some discrete fibre.
- [ ] **Forman-Ricci** as a curvature invariant of the discrete connection.
- [ ] **Convergence theorem**: scaled discrete connection on lattice graphs converges to the Levi-Civita connection of the limit manifold (rate analysis).
- [ ] Cyclic-lattice example with explicit computation.

This rung is large, but every sub-task is a concrete formalisation target — no waving.

## Rung 5 — Riemann, Ricci, scalar curvature, Einstein tensor

**Connection to hypergraphs.** The local-coord versions in `CurvatureLocalCoord.lean`, `CurvatureRiemann.lean` are *useful as targets* but must be reachable from hypergraphs. The bridge is via:
- Discrete Ricci (Ollivier or Forman; we have Ollivier statement-only) → continuum Ricci, by appropriate scaling.
- This is the "Wolfram model curvature" target.

**Decomposition:**
- ✓ `MetricData n` (g, g⁻¹, ∂g + axioms). (`CurvatureLocalCoord.lean`)
- ✓ Christoffel symbols `Γ^ρ_{μν} = ½ g^{ρσ} (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})`. (`CurvatureLocalCoord.lean`)
- ✓ `christoffel_symm`. (`CurvatureLocalCoord.lean`)
- ✓ Minkowski instance with `Γ ≡ 0`. (`CurvatureLocalCoord.lean`)
- ✓ `ConnectionData n` (Γ + ∂Γ + symmetries). (`CurvatureRiemann.lean`)
- ✓ Riemann tensor; `riemann_antisymm`. (`CurvatureRiemann.lean`)
- ✓ **First Bianchi identity** `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0`. (`CurvatureRiemann.lean`)
- ✓ Ricci tensor; scalar curvature; Einstein tensor. (`CurvatureRiemann.lean`)
- ✓ Flat connection + `minkowski4_satisfies_vacuum_EFE`. (`CurvatureRiemann.lean`)
- [ ] Schwarzschild metric instance with explicit derivatives.
- [ ] Levi-Civita derivation: `leviCivita : MetricDataC2 n → ConnectionData n` from the Christoffel formula.
- [ ] Schwarzschild Christoffel computation.
- [ ] Schwarzschild Ricci ≡ 0 (vacuum solution verification).
- [ ] FLRW metric instance + non-zero Ricci computation.
- [ ] Bianchi identity for ∇G^μν = 0 (needs covariant derivative).
- ✓ **Forman-Ricci on a graph** (`DiscreteRicci.lean`): edge curvature `4 − deg(v) − deg(w)`, vertex aggregation, total scalar.
- ✓ **First explicit bridge** (`RicciBridge.lean`): Forman-Ricci on 2-regular graph (e.g., cycle) = continuum Ricci on circle (= 0); `circleMetric : MetricData 1`; `forman_ricci_matches_continuum_on_cycle`. The grounding-principle obligation is met for the cycle/circle case.
- [ ] **Discrete Ricci → continuum Ricci convergence (general)**: extend beyond trivially-flat to non-flat targets (sphere → positive Ricci).
- [ ] Ollivier-Ricci with full proof (currently statement-only).

## Rung 6 — ODEs and PDEs on graphs and their continuum limits

**Connection to hypergraphs.** A `Trajectory sys init` is a discrete dynamical system; the discrete heat equation on a finite graph is a finite-dim ODE; its continuum limit on the GH-limit manifold is a PDE. Both ends and the bridge in our scope.

**Decomposition:**
- [ ] **Discrete heat equation** as a finite-dim linear ODE: `u'(t) = −Δ u(t)` on `(Fin n → ℝ)`.
- [ ] Existence + uniqueness via finite-dim Cauchy-Lipschitz.
- [ ] Heat-kernel matrix exponential `e^{-tΔ}`.
- [ ] **Conservation of total mass** `d/dt ∑ u(t) = 0` (uses `laplacian_sum_zero`).
- [ ] **L² decay** `‖u(t)‖² ≤ ‖u(0)‖²` (uses PSD).
- [ ] **Convergence to uniform** as `t → ∞` (uses spectral gap once we have it).
- [ ] **Continuum limit**: scaled discrete heat equation → continuous heat equation on the GH-limit manifold (combines Rungs 1, 2, 3, 6).
- [ ] **Wave equation** `u'' = Δu` similarly on the cycle.
- [ ] **Schrödinger equation** `i ψ' = −Δ ψ` (QM bridge).
- [ ] **Cauchy problem for Einstein equations**: very long-term, follows Choquet-Bruhat 1952.

## Rung 7 — Fields, Lagrangians, gauge theory

**Connection to hypergraphs.** Fields on a hypergraph are functions `V → V_field`; gauge fields are connections (Rung 4); Lagrangian density is a function on the section space; Euler-Lagrange equations specialise to discrete update rules.

**Decomposition:**
- [ ] Discrete scalar field `φ : V → ℝ`.
- [ ] Discrete gauge field as Rung 4 connection on a fibred-graph (G-bundle).
- [ ] Discrete Lagrangian density `L(φ, ∇φ)`.
- [ ] Discrete Euler-Lagrange equation as a stationary-action condition.
- [ ] Continuous limits — Yang-Mills, Klein-Gordon, etc.
- [ ] HepLean integration.

## Rung 8 — Lorentzian geometry, causal theory

**Connection to hypergraphs.** The `Trajectory`'s causal DAG IS the discrete causal structure; `LorentzLattice.lean` is its lattice analog; `Minkowski.lean` is the continuum target; `lorentzIntEmbed` and `causallyPrecedes_gives_continuum` are the bridge.

**Decomposition:**
- ✓ Discrete causal precedence `CausalPrecedes` on cubic lattice. (`Infra/LorentzLattice.lean`)
- ✓ Trichotomy Timelike / Null / Spacelike, signed Minkowski interval. (`Infra/LorentzLattice.lean`)
- ✓ Continuum Minkowski with same trichotomy. (`Infra/Minkowski.lean`)
- ✓ Int-to-ℝ embedding `lorentzIntEmbed` preserves causal structure. (`Infra/ScaledLorentz.lean`)
- ✓ Trajectory → Minkowski end-to-end bridge. (`Infra/FullBridge.lean`)
- [ ] Continuum Lorentzian metric (general signature `(−, +, ..., +)`). Specialise our `MetricData` framework.
- [ ] Causal future / past as filters.
- [ ] Strong causality, global hyperbolicity.
- [ ] Cauchy surfaces, foliations, ADM decomposition.
- [ ] Lorentzian Gromov-Hausdorff (Noldus-Suhr / Bao-Miao machinery).
- [ ] **Discrete-causal-DAG → continuum Lorentzian convergence**: lift `lorentzIntEmbed`'s exact preservation to a scaled-density convergence theorem.

## Rung 9 — Einstein's equations

**Connection to hypergraphs.** The end goal: a Wolfram-model rule whose causal graph (under appropriate scaling) GH-converges to a Lorentzian manifold satisfying the vacuum Einstein equations. We have all the parts in place to *state* this; satisfying it is open research.

**Decomposition:**
- [ ] State `vacuumEFE : ConnectionData n → MetricData n → Prop` (already implicit in `einsteinTensor = 0`).
- [ ] Stress-energy tensor `T_{μν}` as data.
- [ ] Full EFE `G_{μν} = 8πG T_{μν}` with sign conventions.
- [ ] Energy conditions: WEC, SEC, DEC.
- [ ] Schwarzschild as vacuum solution verification.
- [ ] FLRW as solution with perfect-fluid `T`.
- [ ] **Hypergraph anchor**: candidate-rule verification interface — given a rule + spatial embedding, check whether the resulting causal DAG's continuum limit satisfies EFE. Uses Rungs 4, 5, 6, 8.

## Rung 10 — Specific hypergraph → GR bridges

**Connection to hypergraphs.** Native: every theorem here takes a hypergraph rewriting rule as input.

**Decomposition:**
- ✓ Cycle → circle GH bound. (`Infra/GHBound.lean`)
- ✓ Path → interval. (`Infra/ScaledPath.lean`)
- ✓ 2D lattice → 2-torus. (`Infra/ScaledTorus.lean`)
- ✓ (d+1)D lattice → (d+1)-torus. (`Infra/ScaledTorusD.lean`)
- ✓ Discrete-Lorentz-lattice → continuum Minkowski (forward direction). (`Infra/ScaledLorentz.lean`)
- ✓ Trajectory causal DAG → continuum Minkowski. (`Infra/FullBridge.lean`)
- [ ] Curved-target bridges (need Rungs 4–5 connections on hypergraphs).
- [ ] BBH hypergraph evolution (very long-term).

## Branchial / QM track (cross-cutting)

**Connection to hypergraphs.** Native: branchial structure IS a hypergraph-rewriting structure (states sharing a single-step predecessor in a multiway evolution graph).

**Decomposition:**
- ✓ `BranchialRelated`, `NStep`, `BranchialSlice`. (`Branchial.lean`)
- ✓ Finite-slice condition (`BranchialFinite.lean`, I1).
- ✓ Branchial measure: `branchialUniformWeight` (`BranchialHilbert.lean`, I2).
- ✓ Branchial amplitudes: `BranchialAmplitude S := BranchialHilbert S` + Born rule `bornProbability` (`BranchialHilbert.lean`, I3).
- ✓ Branchial Hilbert space: `BranchialHilbert S := EuclideanSpace ℂ S` with ℂ-linear adjacency `branchialAdjLM` and self-adjointness `branchialAdjLM_inner` (`BranchialHilbert.lean`, I4 / R3 partial).
- ✓ Branchial evolution as unitary: `branchialSchrodinger_unitary_evolution` in `BranchialSchrodinger.lean` (I5 / I9). Total probability conserved via self-adjointness of the adjacency operator.
- ✓ **Grounding**: `BranchialCanonical.lean` — `branchialSliceHamiltonian sys s₀ n h` is the canonical rewriting-system-grounded Hamiltonian on the concrete slice. `branchial_qm_is_rewriting_grounded`: every QM feature (Hilbert space, Hermitian observable, Schrödinger evolution, Born-rule measurement) derives from `(sys, s₀, n)` alone; no continuous structure is imposed.
- ✓ Observables as Hermitian operators: `BranchialObservable S` + `branchialAdjObservable` (`BranchialHilbert.lean`, I6).
- ✓ Expectation values + Born rule on observables: `expectationValue`, `expectationValue_re_of_symm`, `expectationValue_eigenvector` (`BranchialHilbert.lean`, I7).
- ✓ Fubini-Study/Bhattacharyya bound: `fubiniStudyBhattacharyya_bound` (`RemainingObligations.lean`, IQ6 upgraded + proved).
- [ ] Continuum limit: branchial graph → quantum-mechanical Hilbert space (I8 pending).
- [ ] Path-integral formulation (I10 pending).

## Refutation track (cross-cutting)

These complement the constructive bridge: they pin down which Gorard claims fail and why. Already done; tracked in `MAJOR_FLAWS.md`.

- ✓ F1: no canonical hypergraph metric.
- ✓ F2: fiat orthonormality non-canonical.
- ✓ F3: dim-preservation tautology.
- ✓ F4: causal invariance ⇔ general covariance tautology.
- ✓ F5: ill-defined "becomes integral".
- F6, F7, F8: documented; F7 has empirical refutation.

## Summary table — current status

| Rung | What we have | Hypergraph anchor | Open sub-tasks |
|---|---|---|---|
| 1 | Δ + self-adj + Dirichlet + PSD + div-thm + linmap + cycle | Native | hyperedge ∇/div, hypergraph Laplacian |
| 2 | Δ²_h polynomial case | via cycle Δ | Taylor-remainder for `C²`, eigenvalue conv |
| 3 | Wasserstein in Mathlib | counting measure on `Hypergraph V` | weak conv to Lebesgue, GHP |
| 4 | (formerly punted; now decomposed) | discrete connection on hypergraph | bundle Riemannian metric, Levi-Civita, discrete connection convergence |
| 5 | Christoffel + Riemann + Ricci + scalar + Einstein + Bianchi I + flat-EFE | via Ollivier-Ricci → continuum Ricci | Schwarzschild, FLRW, Levi-Civita derivation, discrete Ricci convergence |
| 6 | (planned) | discrete heat equation as finite ODE | conservation, L² decay, continuum limit |
| 7 | (planned) | discrete fields & Lagrangians | gauge fields via Rung 4 |
| 8 | full discrete-Lorentzian + continuum Minkowski + bridge | full chain done | curved Lorentzian, Lorentzian GH |
| 9 | (planned via 4, 5, 8) | EFE-checking interface for candidate rules | Schwarzschild verification |
| 10 | flat-target bridges done | every theorem takes a rule as input | curved-target bridges |
| QM | Branchial skeleton | native | measure → amplitudes → Hilbert |

**Priority order** (what to grind next):

**Current focus: discrete d'Alembertian (Benincasa-Dowker-style) on the trajectory causal DAG.**
This is the operator Gorard's 2102.09363 circular derivation hinged on. We have all the discrete-causal scaffolding already (`Trajectory`, `causallyPrecedes`, `isCausalPred`, `level`). Formalise: (a) `intervalSize τ j i` — cardinality of open causal interval; (b) `layer τ k i` — events with exactly `k` intermediates; (c) `discreteDAlembertian4 τ φ i := -φ i + ∑ L_0 φ - 9·∑ L_1 φ + 16·∑ L_2 φ - 8·∑ L_3 φ`; (d) linearity + structural theorems; (e) explicit statement of the Benincasa-Dowker convergence conjecture as an open `Prop`, connected to F6. Ships as `DiscreteDAlembertian.lean`.

**Next after that:**
1. **Schwarzschild as `MetricData 4`** (Rung 5 curved-metric sanity check): all components, all partial derivatives, Christoffel computation, vacuum-EFE verification. A concrete "Gorard tried and failed to formalise, we did" deliverable.
2. **Discrete heat equation as linear ODE on `Hypergraph V`** (Rung 6 entry): uses `laplacianHyper` + `laplacian_sum_zero`; ties Rungs 1 + 6.
3. Discrete connection on a hypergraph (Rung 4.4 — anchor for Levi-Civita).
4. `C²` Taylor-remainder (Rung 2 completion).
5. Branchial measure (QM entry).

**All three (d'Alembertian, Schwarzschild, heat ODE) are in the plan** and decomposed by sub-tasks. The d'Alembertian is the immediate focus; Schwarzschild and heat-ODE are next.

**Operating principle reminder.** No rung produces "isolated continuum mathematics". Every rung's continuum object is paired with a hypergraph-side object plus a convergence/approximation theorem.
