# Milestones — infrageometry research programme

Canonical progress tracker for the whole programme. All tasks have explicit checkboxes: `[x]` = done, `[ ]` = pending, `[~]` = in flight / partial, `[!]` = blocked by external dependency.

Grouped by phase (see [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md)). Each milestone either ships something verifiable (a Lean theorem, a numerical experiment, a written analytical refutation) or is broken into sub-milestones that do.

---

## Phase 0 — Audit of the Gorard corpus

- [x] G1 (2004.14810) close-reading ([notes/2004.14810_close_reading.md](notes/2004.14810_close_reading.md))
- [x] G2 (2011.12174) partial close-reading (cross-paper audit)
- [x] G3 (2102.09363) close-reading ([notes/2102.09363_close_reading.md](notes/2102.09363_close_reading.md))
- [x] G4 (2303.07282) close-reading ([notes/2303.07282_close_reading.md](notes/2303.07282_close_reading.md))
- [x] Full 184-row claims catalog for G1 ([notes/claims_catalog.md](notes/claims_catalog.md))
- [x] Cross-paper map of repeated errors ([notes/corpus_audit.md](notes/corpus_audit.md))
- [x] Severity taxonomy S1–S6 ([notes/severity_taxonomy.md](notes/severity_taxonomy.md))
- [x] Continuum-limit claims catalog ([notes/continuum_limit_claims.md](notes/continuum_limit_claims.md))
- [x] Major-structural-flaws index F1–F8 ([MAJOR_FLAWS.md](MAJOR_FLAWS.md))
- [x] Overclaim-or-hunch synthesis ([notes/claim_assessment.md](notes/claim_assessment.md))
- [x] Empirical refutation of the named "EFE rule" ([notes/empirical_refutation.md](notes/empirical_refutation.md))
- [x] Independent Python rewriter confirming SetReplace agreement ([results/phase1_selfaudit/](results/phase1_selfaudit/))
- [ ] Structured external comment PDF (to circulate / submit to arXiv)

## Phase 1 — Wolfram-model structural theorems (Lean)

### Edge conservation and degree sums
- [x] Edge conservation theorem (T1 `size_result_of_conservative`)
- [x] Trajectory-level extension (T2)
- [x] In-degree = |LHS| theorem (T5)
- [x] Out-degree = |RHS| theorem (T6)
- [x] Per-event balance (T7)
- [x] Sum of in-degrees = M·k (T8)
- [x] Sum of out-degrees = M·k (T9)
- [x] Sum equality for conservative rules (T10)

### Causal level function
- [x] Level defined via well-founded recursion (T11)
- [x] Level unfolding equation (T12)
- [x] **Level monotonicity** — causal edge ⇒ level grows by ≥ 1 (T13)
- [x] Same-level antichain property, forward direction (T14, T15)
- [ ] Trajectory-structure lemma: consumed expressions have earlier creators
- [ ] Same-level antichain in both directions (requires above)

### Parallel-layer bound
- [ ] State-size invariant across a parallel schedule
- [ ] Layer-cardinality bound `|layer_s| ≤ N/k` (the full parallel-layer bound, a.k.a. Theorem B)
- [ ] Linear BFS-cone bound for specific rule + specific seed

### Structural impossibilities (refute the major flaws)
- [x] F1: no canonical discrete metric tensor on a hypergraph (`Refutations/F1NoMetric.lean`)
- [x] F2: fiat orthonormality of non-parallel hyperedges is non-canonical (`Refutations/F2Orthonormality.lean`)
- [x] F3: "asymptotic dim preservation ⇒ Einstein eqn" is definitionally unfolded (`Refutations/F3Tautology.lean`)
- [x] F4: "causal invariance ⇔ general covariance" is a definition-equality (`Refutations/F4Tautology.lean`; axiom-free)
- [x] F5: "becomes" under-determined — two natural convergence notions disagree (`Refutations/F5Illdefined.lean`)
- [ ] F5': concrete counterexample — a rule whose discrete sum demonstrably does not GH-converge to an EH-style integral (stretch goal)

### Higher-dim continuum limits
- [x] 1D cycle → circle GH bound (`Infra/ScaledCycle.lean`, `Infra/GHBound.lean`)
- [x] 1D path → interval GH bound (`Infra/ScaledPath.lean`)
- [x] 2D lattice → 2-torus GH bound (`Infra/ScaledTorus.lean`)
- [x] (d+1)D lattice → (d+1)-torus GH bound, arbitrary `d ≥ 0` (`Infra/ScaledTorusD.lean`)
- [x] **Continuum Minkowski `ℝ^{1,d}`** (`Infra/Minkowski.lean`): `continuumSpaceDist`, `ContinuumCausalPrecedes`, Timelike/Null/Spacelike, signed interval, trichotomy.
- [x] **Int-to-ℝ forward embedding** (`Infra/ScaledLorentz.lean`): `lorentzIntEmbed` preserves `CausalPrecedes` and `Timelike` into their continuum counterparts. (Full scaled isometry-plus-density — the Lorentzian analog of `dTorus_gh_bound` — remains open; requires Lorentzian-GH machinery not in Mathlib.)
- [x] **End-to-end bridge** (`Infra/FullBridge.lean`): `causallyPrecedes_gives_continuum` — under `LightConeCompatible τ φ`, the trajectory's causal order is faithful in continuum Minkowski. Strict-interior version via `causallyPrecedes_gives_continuum_timelike` under `StrictlyTimelikeCompatible`.

### Discrete calculus (Rung 1 of the bridge ladder)
- [x] Graph Laplacian, discrete inner product (`DiscreteCalculus.lean`).
- [x] Laplacian linearity (`laplacian_add`, `laplacian_smul`, `laplacian_const`).
- [x] Inner product symmetry, bilinearity.
- [x] **`laplacianLinear`**: graph Laplacian as a `LinearMap`, opening Mathlib's linear-algebra / spectral API to discrete operators.
- [x] `nbhd_sum_swap` — edge-sum swap lemma under symmetric adjacency.
- [x] **`laplacian_self_adjoint`** — `⟪Δ f, g⟫ = ⟪f, Δ g⟫` (`DiscreteCalculusSymm.lean`).
- [x] Positivity of `-Δ`: **`dirichlet_form`** + **`laplacian_neg_psd`** — `⟪f, -Δ f⟫ = ½ ∑ (f(w) - f(v))² ≥ 0`.
- [x] **`laplacian_sum_zero`**: ∑ Δf = 0 (discrete divergence theorem; conservation of total mass under heat equation).
- [x] **Cycle graph concrete instance** (`CycleGraph.lean`): `cycleLaplacian` defined as `f(i+1) + f(i-1) - 2 f(i)`. Linearity, vanishing on constants, and the Dirichlet form `∑ f i · (-Δ f i) = ∑ (f(i+1) - f(i))²` plus its non-negativity, all axiom-clean. Sets up the Rung-2 Taylor-expansion convergence theorem.
- [x] **Central second difference (Rung 2 entry)** (`SecondDifference.lean`): `secondDifference f x h := f(x+h) − 2 f(x) + f(x−h)`, linearity. Polynomial-case exact identity: for any quadratic `a x² + b x + c`, `secondDifference = 2 a h² = f''(x) · h²` (no error term). Identifies the cycle Laplacian with this operator. General `C²` Taylor-remainder convergence is the next step.

### Rung 5 — Riemann/Ricci/scalar curvature (local-coordinate route)
- [x] **`MetricData n`** (`CurvatureLocalCoord.lean`): metric components, inverse, first partial derivatives, symmetry + inverse axioms. Avoids bundle machinery.
- [x] **Christoffel symbols** `Γ^ρ_{μν} = ½ g^{ρσ} (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})` as explicit formula.
- [x] **`christoffel_symm`**: lower-index symmetry `Γ^ρ_{μν} = Γ^ρ_{νμ}`.
- [x] **Minkowski instance** on ℝ⁴ with signature `(−, +, +, +)`; `minkowski4_christoffel_zero` confirms all Christoffel symbols vanish.
- [x] **Riemann tensor** `R^ρ_{σμν}` (`CurvatureRiemann.lean`) via `ConnectionData n` carrying `Γ + ∂Γ` as data; `riemann_antisymm` in last two indices.
- [x] **Ricci tensor** `R_{σν} = Σ_ρ R^ρ_{σρν}` and **scalar curvature** `R = g^{σν} R_{σν}` and **Einstein tensor** `G_{μν} = R_{μν} − ½ R g_{μν}`.
- [x] `flatConnection`: `Γ ≡ 0`, with `flatConnection_riemann_zero`, `_ricci_zero`, `_scalar_zero`, `_einstein_zero`.
- [x] **`minkowski4_satisfies_vacuum_EFE`**: `G_{μν} = 0` on Minkowski with the flat connection — the trivial flat-space EFE sanity check.
- [ ] Schwarzschild instance with non-trivial Christoffel symbols (next concrete sanity check; tests the formalism on a curved metric).
- [ ] Bianchi identity `∇_μ G^{μν} = 0` (formal consequence; needs covariant derivative).
- [ ] Heat semigroup on a finite graph as a finite-dim ODE.
- [ ] Scaled cycle Laplacian → 1D `d²/dx²` (Rung 2 entry).

### Discrete Lorentzian structure (first ingredient of GR bridge)
- [x] Event type `Fin (d+1) → ℤ` on cubic lattice (`Infra/LorentzLattice.lean`)
- [x] Spatial L∞ distance `spaceDist`; self, symm, triangle
- [x] `CausalPrecedes p q`: forward-light-cone relation
- [x] Reflexivity, transitivity, antisymmetry-in-time
- [x] Timelike / Null / Spacelike classification; `causal_or_spacelike` trichotomy
- [x] `spacelike_of_equal_time`: simultaneous distinct events are spacelike
- [x] `timelike_trans`: timelike relations compose
- [x] `forwardCone` definition + upward-closure + `self_mem_forwardCone`
- [x] **Signed Minkowski interval** `minkowskiIntervalSq := (Δt)² − (spaceDist)²`
- [x] `minkowskiIntervalSq_pos_of_timelike` / `_zero_of_null` / `_neg_of_spacelike`
- [x] **Bridging theorems** (`Infra/TrajectoryLorentz.lean`): `trajectoryToEvent τ` maps causal-DAG events to `Event 0` via the level function.
  - `trajectoryToEvent_preserves_causal`: `isCausalPred τ j i → CausalPrecedes 0 …`
  - `causallyPrecedes_iff_isCausalPred`: wiring Prop ↔ Bool causal relations (in `CausalLevel.lean`)
  - `causallyPrecedes_implies_minkowski`: full chain `causallyPrecedes → CausalPrecedes`
  - `causallyPrecedes_implies_timelike`: strengthened — gives `Timelike` (strict interior)
  - `trajectoryToEvent_lossy`: same-level events collapse; lossiness is F1/F2-style
- [x] **d-dim bridging, conditional on a chosen spatial embedding** (`Infra/TrajectoryLorentzD.lean`):
  - `SpatialEmbedding d := ℕ → Fin d → ℤ` — the F1-missing data as an explicit parameter.
  - `fullEmbed τ φ i`: full spacetime embedding (time = level, space = φ).
  - `LightConeCompatible τ φ`: the per-rule, per-embedding compatibility hypothesis.
  - `fullEmbed_preserves_causal`: conditional d-dim bridging — under compatibility, `causallyPrecedes → CausalPrecedes d`.
  - `StrictlyTimelikeCompatible τ φ`, `fullEmbed_timelike`: strict-interior version.
  - `same_level_spacelike_of_spatial_distinct`: same-level events that are spatially distinct under φ become `Spacelike` in the Lorentz lattice — overcoming the 1+0-dim lossiness.
- [ ] Conformal limit to continuum Minkowski (Phase 5 research)
- [ ] Discrete light-cone growth rate → `c = 1` (Phase 5)

### Branchial / multiway skeleton (QM bridge groundwork)
- [x] `BranchialRelated sys s₁ s₂`: shared predecessor relation (`Branchial.lean`)
- [x] Symmetry of `BranchialRelated`
- [x] `NStep sys n a b`: iterated single-step reachability
- [x] `BranchialSlice sys s₀ n`: the depth-`n` slice
- [x] Slice recursion: depth-0 = `{s₀}`, depth-(n+1) = successors of depth-n
- [ ] Finite-slice cardinality bound when the rewriting system is finite and hypergraph is finite
- [ ] Branchial measure: a probability assignment on each slice
- [ ] Amplitudes / branchial weights toward a Hilbert-space limit

## Phase 2 — Corrected continuum identities (Lean)

### Stated correctly (statement-only, no Mathlib Ricci yet)
- [x] Correct Ollivier identity as `OllivierIdentityLeading` (T27)
- [x] Gorard's form and coincidence condition (T28)
- [x] Correct Gray tube formula as `GrayTubeLeading` (T29)
- [x] Concrete disagreement on $S^2$: 1/6 ≠ 1/3 (T30)
- [x] Concrete disagreement on $S^3$: 1/3 ≠ 2 (T31)

### Fully proved (requires Mathlib Riemannian + OT infrastructure)
- [ ] Ollivier's theorem: $\kappa_\varepsilon(p,q) = \varepsilon^2\mathrm{Ric}(v,v)/(2(d+2)) + O(\varepsilon^3)$
- [ ] Gray's tube formula
- [ ] Convergence of discrete Ollivier–Ricci to directional Ricci under random-geometric-graph sampling (Trillos–Slepčev-style, but for $\kappa$)

## Phase 3 — Continuum-limit theorems (Lean)

### Basic templates
- [x] Cycle → circle GH bound (T21 `cycle_circle_gh_bound`)
- [x] ε-density corollary (T22)
- [x] Path → interval GH bound (T25 `path_interval_gh_bound`)
- [x] Scaled 2D lattice → flat 2-torus (T40 `torus_gh_bound`)
- [x] Common `GHApproximation` abstraction (T26)

### Extensions
- [ ] Scaled $d$-dim lattice → flat $d$-torus, any $d$
- [ ] Scaled Cayley graph of a finitely-generated group → its asymptotic cone
- [ ] Random geometric graph on a Riemannian manifold → the manifold (the positive analogue of Gorard's §3)
- [ ] Causal-set Poisson sample of a Lorentzian spacetime → the spacetime (Lorentzian-GH, contingent on Mathlib infrastructure)

## Phase 4 — Discrete geometric structures library (Lean)

- [ ] `DirectedHypergraph` as a metric-measure space (graph distance + vertex counting measure)
- [ ] Pseudo-metric axioms proved for `graphDist` on a hypergraph
- [ ] Ollivier–Ricci on directed hyperedges, following Eidi–Jost 2019
- [ ] Benincasa–Dowker discrete d'Alembertian on a causal graph
- [ ] Convergence results connecting discrete to continuum (random-geometric-graph, Poisson)

## Phase 5 — Wolfram-specific convergence theorems (Lean)

- [ ] Identify a rule family with a provable GR limit. **Research-level; open problem.** Candidates:
  - [ ] Rules producing Poisson-sampled causal sets (needs BD conjecture)
  - [ ] Rules mimicking random geometric graphs (needs Phase 4 convergence)
  - [ ] CDT-inspired rules (Lorentzian simplicial approximations)
- [ ] Prove: a chosen rule's causal graph GH-converges to a specific Lorentzian manifold
- [ ] Compare the converged metric against the claimed Einstein-equation solution
- [ ] **[Aspirational]** Hypergraph representation of binary-black-hole initial data
- [ ] **[Aspirational]** Evolution of BBH initial data under the chosen rule, with convergence to a merger spacetime
- [ ] **[Aspirational]** Discrete Ψ₄ extraction from the causal graph, compared to analytical BBH ringdown

## Phase 6 — Causal-set infrageometry (Lean)

- [ ] Causal-set type class (locally finite, transitive, antisymmetric relation)
- [ ] Benincasa–Dowker discrete d'Alembertian (already partly in Phase 4; unify)
- [ ] Poisson sampling of a Lorentzian spacetime into a causal set
- [ ] Expected-value convergence $\langle B^{(d)}_\rho \phi\rangle \to \Box \phi - \tfrac12 R\phi$ (Sorkin–BD conjecture, open in the literature)
- [ ] $\langle S_{\mathrm{BD}}\rangle \to S_{\mathrm{EH}}$ (open in the literature)

## Phase 7 — Quantum-mechanical bridge (multiway / branchial)

Gorard's companion program (arXiv:2004.14808 and related) claims that the *branchial* structure of the multiway evolution graph recovers quantum mechanics. This is its own research line and has not been adequately audited yet; included here because quantum-mechanical content is the *only* plausible first-principles bridge between Wolfram rewriting and observed physics (since GR emerges only statistically / in the continuum limit).

- [ ] Audit Gorard's QM paper with same S1–S6 methodology
- [ ] Define `MultiwayEvolution` in Lean (states = hypergraphs, edges = applications; full branching tree, not the single-way Trajectory)
- [ ] Define `BranchialGraph` (states at a common evolution depth with shared ancestry)
- [ ] Integrate with `../efficient_rewriting_final/` multi-way engine for concrete examples
- [ ] Define a measure / amplitude on branchial paths
- [ ] State: branchial-measure evolution satisfies a discrete Schrödinger-like equation (if provable)

## Multi-way engine integration

The `../efficient_rewriting_final/` repo is a high-performance C++ multi-way hypergraph-rewriting engine with a Mathematica paclet interface. Single-way SetReplace cannot verify causal invariance or explore branchial structure; this engine can.

- [ ] Wrap paclet for headless invocation from our Python test harness
- [ ] Re-run empirical refutation of the named rule with multi-way evolution (confirm 1D cone across all branches)
- [ ] Test causal invariance of simple rules (is any family provably causal-invariant?)
- [ ] Collect branchial-graph data for Phase 7 quantum-mechanical thread
- [ ] Use as a probe for candidate GR-recovering rules (Phase 5 search)

## Lean physics conventions to adopt

- [ ] Survey existing Lean physics projects for conventions (HepLean / particle physics; Mathlib's `Geometry.Manifold`, `MeasureTheory`, `Topology.MetricSpace`; smaller efforts in classical mechanics, quantum theory)
- [ ] Align `DirectedHypergraph` namespace and type conventions with Mathlib's `Geometry.Manifold`-style idioms
- [ ] Adopt Mathlib Lorentzian infrastructure when it lands; contribute if slower than we need

## Output targets (see also [`PUBLISHABLE.md`](PUBLISHABLE.md))

- [ ] Publishable audit note: the Gorard-corpus refutation with Lean backing
- [ ] Publishable constructive note: correct Ollivier + Gray identities formalised
- [ ] Publishable infrageometry paper: our Phase-3 continuum-limit theorems + abstraction
- [ ] Publishable research paper: the first provable Wolfram-to-GR rule (Phase 5 milestone)
- [ ] Publishable joint paper: quantum-mechanical content via branchial structure (Phase 7 milestone)

---

**Maintenance.** Every Lean commit adds one or more `[x]` above. Every research decision updates the ordering and dependencies. Open this file at the start of each working block to re-anchor.
