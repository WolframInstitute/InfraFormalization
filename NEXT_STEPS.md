# Next steps — what's done, in flight, and waiting

Lives next to [`README.md`](README.md) / [`INDEX.md`](INDEX.md) / [`FINDINGS.md`](FINDINGS.md) / [`COVERAGE_MAP.md`](COVERAGE_MAP.md). Curated by hand.

## Recently shipped (selected highlights)

- **D2 / Heat equation existence + forward uniqueness** (`HeatEquationUniqueness.lean`): `heat_exists` (via heatKernel T1), `heat_unique_forward` (via L² antitone applied to difference of solutions), `heat_exists_unique_forward`. Closes D2 modulo two-sided uniqueness (fails generically — heat equation is irreversible).
- **T4 / Cycle spectrum in `HasEigenvalue` form** (`CycleHasEigenvalue.lean`): `laplacianMatrix_cycleHypergraph_hasEigenvalue` — `Module.End.HasEigenvalue (Matrix.toLin' (laplacianMatrix (cycleHypergraph n))) (cycleEigenvalue n k)`. Connects pointwise eigenvalue theorem to Mathlib's spectral API.
- **T2 / Matrix exp fixes eigenvectors** (`ExpEigenvector.lean`): `exp_mulVec_of_eigenvector` — if `A.mulVec v = λ • v`, then `(NormedSpace.exp A).mulVec v = Real.exp λ • v`. Proved via `exp_eq_tsum_rat` (series definition) + `ContinuousLinearMap.map_tsum` + inductive `matrix_pow_mulVec_of_eigenvector` + `Real.summable_pow_div_factorial`. General operator fact; underpins T4 + ID7.
- **T1 / Heat kernel ODE identification** (`HeatKernelODE.lean`): `heatKernel_isHeatSolution` — the matrix propagator `exp(t · Δ_H)` applied to initial data `u₀` satisfies the `HeatSolution H` ODE predicate. Proved via `hasDerivAt_exp_smul_const` composed with a continuous linear map (`mulVecEvalCLM`) and the commutativity of `heatKernel H t` with `laplacianMatrix H` (`heatKernel_commute_laplacianMatrix`). The two heat-equation definitions are now linked.
- **T3 / Hypergraph.dist triangle inequality** (`HypergraphDistance.lean`): `dist_triangle` (via `Connected` hypothesis) + `dist_triangle_of_reachable_{left,right}` (conditional forms). `cycleHypergraph_connected` for n ≥ 2, giving unconditional triangle inequality on cycles. Pseudo-metric axioms now all in hand; measure-theoretic work (A5/A6/A7/A8) unblocked.
- **R5 / full cycle spectrum** (`CycleSpectrum.lean`): `cycleEigenvector n k (j) = cos(2πkj/n)` and `cycleEigenvalue n k = −4 sin²(πk/n)` satisfy the eigenvalue equation at **all** indices (interior + wrap-around boundary).
- **R1 / A2 / A3** (`CTwoTaylor.lean`, `ScaledDiffC2Bridge.lean`): **C² Taylor convergence** of the scaled central second difference, via Mathlib's `Real.taylor_tendsto`. The Rung-2 discrete-to-continuum bridge now covers *all* C² functions, not just polynomials.
- **A4** (`CycleEigenLimit.lean`): scaled cycle eigenvalue `n² · (−4 sin²(πk/n)) → −(2πk)²`. First concrete **spectral convergence** to continuum circle Laplacian eigenvalues.
- **R2 / D3** (`LaplacianMatrix.lean`): hypergraph Laplacian as a Mathlib matrix, **heat kernel via `Matrix.exp`**, semigroup property, symmetric matrix, row-sum zero, `heatTrace`.
- **B1 complete** (`Schwarzschild.lean`): **all 8** Schwarzschild Christoffel entries computed in the exterior — the first fully-computed non-trivial curved-metric connection in the corpus.
- **Infrageometry program (57 tasks / 9 groups)**: IA full (5/5), IG 10/11, IC full (8/8), IT 3 proved + 3 obligation, ID 5 + 2 obligation, IB 5/6, IQ 1 + 3 obligation, IS full (3/3), IR 6 + 1 obligation. Full coverage in `COVERAGE_MAP.md §8`.
- **Refutations F1–F5** (`Refutations/F*`): machine-checked; F6 (BD conjecture) flagged as an explicit `Prop` obligation (`DiscreteDAlembertian.lean`).
- **Discrete Schrödinger unitarity** (`SchrodingerEquation.lean`, D10), **discrete Klein-Gordon energy conservation** (`KleinGordon.lean`, D9), **discrete wave energy conservation** (`WaveEquation.lean`, D8), **discrete heat mass / L² decay** (`HeatEquation.lean`, D1/D4/D5).

Every theorem above depends only on `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no custom axioms. Verified by `AxiomCheck.lean`.

## In flight 🛠 (in_progress tasks)

- **IR7 #165** — Reverse-engineer rule from target signature.
- **IT5 #137** — Latschev theorem (as Prop obligation; proof for cycles).
- **IT6 #138** — Scale-dependence trichotomy theorem.
- **ID6 #144** — Compatibility theorem: all dimension notions agree on regular lattices.
- **ID7 #145** — Spectral dimension via heat-kernel trace (heat trace now defined; small-`t` asymptotics pending).
- **IB2 #147** — Causal-branchial-trivial commutator theorem.
- **IQ6 #153** — Fubini-Study as limit of Fisher under refinement.
- **IQ8 #154** — EME persistence as branchial observable.
- **IQ9 #155** — Path integral over singleway causal graphs.

## Ready to pick up

### Near-term (Rung-1/Rung-2 follow-ons — the machinery is in hand)

- [ ] **R3 #178** — `ℓ²(BranchialSlice)` as Hilbert space with branchial adjacency operator. Real-QM bridge: finite-dim Hilbert space from `branchialSliceFinite_of_successors_finite`.
- [ ] **R4 #179** — Curved discrete-Ricci convergence beyond flat. First non-zero Forman-Ricci convergence case.
- [ ] **A5 #16** — Counting measure on `Hypergraph V` + pushforward (groundwork for A6 / weak convergence, A7 / Wasserstein).
- [ ] **A7 #18** — Wasserstein-1 convergence rate `O(1/n)` for counting measures.
- [ ] **D6 #47** — Long-time convergence of heat solution to uniform (spectral-gap argument using `cycleEigenvalue` lower bound).
- [ ] **D7 #48** — Scaled discrete heat → continuous heat on GH-limit.

### Schwarzschild follow-ons (B-group)

- [ ] **B2 #21** — Schwarzschild Riemann tensor components.
- [ ] **B3 #22** — Schwarzschild `Ric ≡ 0`.
- [ ] **B4 #23** — `schwarzschild_satisfies_vacuum_EFE`.
- [ ] **B5 #25** — Schwarzschild as `PartialMetricData` on exterior.

### Curved-metric families

- [ ] **B6–B9** — FLRW, Reissner-Nordström, Kerr metric components + curvature.

### Bundle machinery (C-group; Mathlib gap)

- [ ] **C1–C8** — Riemannian / Lorentzian bundle structure, vector-bundle connections, discrete-connection ↔ Levi-Civita convergence.

### Branchial / QM (I-group)

- [ ] **I2 #85** — Branchial measure (uniform on finite slice).
- [ ] **I3 #86** — Branchial amplitudes (ℂ-valued).
- [ ] **I4 #87** — `ℓ²(slice)` Hilbert space (= R3).
- [ ] **I5 #88** — Branchial evolution as unitary.

### Einstein / stress-energy (F-group)

- [ ] F-group all open (F1–F8): stress-energy tensor, energy conditions, full Einstein equations with Λ, Schwarzschild as explicit vacuum solution, FLRW explicit, Kerr, Penrose singularity theorem, Raychaudhuri equation.

### Lorentzian-manifold (E-group)

- [ ] E-group all open: `LorentzianManifold`, chronological relations, light cones, causality conditions, Cauchy surfaces / ADM, Lorentzian GH, discrete-causal-DAG → continuum Lorentzian convergence.

### BBH-numerics (H-group)

- [ ] H-group all open: candidate rules catalog, empirical dimensional signatures pipeline, screening tests, curved-target RicciBridge extensions, BBH initial data, BBH evolution, discrete Ψ₄ extraction, BBH merger convergence.

### Paper drafts (K-group)

- [ ] K1 — P1 audit paper.
- [ ] K2 — P2 corrected identities paper.
- [ ] K3 — P3 infrageometry continuum-limits paper (first candidate given R1 + R2 + R5 now closed).
- [ ] K4–K9 — P4 structural library, P5 Wolfram→GR, P6 branchial QM audit, P7 BBH, P8 discrete d'Alembertian + BD flag, P9 refutation-chain paper.

### Colleague-work integration (M-group)

- [ ] M1 — Ioana Milea gauge-intern coordination.
- [ ] M2 — Van Le Fisher → Fubini-Study bridge.
- [ ] M3 — Hubert Kolcz Lie-Poisson MBQC.
- [ ] M4 — Jan Pullman IBL-∞ / BV formalism.
- [ ] M5 — Zapata + Ahmed axiomatic-relativity paper.
- [ ] M6 — Pokorny Infrageometry paclet parity.
- [ ] M7 — Ahmed EME-tracking community post.
- [ ] M8 — Pokorny diffusion-geometry bridge.
- [ ] M9 — Tropical-geometry synthetic infrageometry.
- [ ] M10 — 3BP / dynamical-systems dimension signature.

### Support (X-group)

- [ ] X1 — `PartialMetricData` refactor with domain predicate.
- [ ] X2 — Covariant derivative `∇` on `ConnectionData`.
- [ ] X3 — Mathlib Taylor integration (partly used by R1; full uniform-`C^k` version still open).
- [ ] X4 — Multi-way engine integration from `efficient_rewriting_final`.

## External communication

- [ ] Structured external comment PDF (audit + refutation chain); to circulate to the Wolfram Institute / submit to arXiv.
- [ ] Publishable infrageometry paper: Phase-3 continuum-limit theorems + the Rung-1/2/3 bridge story (R1 + R2 + R5 + A3 + A4 are the technical core).

## Grounding principle (non-negotiable)

Every continuous structure in this repository must have an explicit hypergraph anchor or be the target of an explicit convergence theorem. See [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md). No silent assumptions; every open obligation is either a `∧ False`-guarded `Prop` (`ContinuumLimitStatement.lean`, `RemainingObligations.lean`) or an explicit pending task above.
