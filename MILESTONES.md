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

### Discrete Lorentzian structure (first ingredient of GR bridge)
- [x] Event type `Fin (d+1) → ℤ` on cubic lattice (`Infra/LorentzLattice.lean`)
- [x] Spatial L∞ distance `spaceDist`; self, symm, triangle
- [x] `CausalPrecedes p q`: forward-light-cone relation
- [x] Reflexivity, transitivity, antisymmetry-in-time
- [x] Timelike / spacelike classification; `causal_or_spacelike` trichotomy
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
