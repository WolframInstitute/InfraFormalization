# Next steps — what's done, in flight, and waiting

Lives next to [`README.md`](README.md) / [`INDEX.md`](INDEX.md) / [`FINDINGS.md`](FINDINGS.md) / [`COVERAGE_MAP.md`](COVERAGE_MAP.md). Curated by hand.

## Recently shipped (selected highlights)

- **Klein-Gordon continuum spectrum PROVED** (`ContinuumLimitStatement.lean`): `DiscreteKleinGordonSpectrum m` — lattice KG dispersion `n² · 4 sin²(πk/n) + m²` converges to `(2πk)² + m²` for every `m ∈ ℝ` and `k`. Proved via Schrödinger bridge + `Filter.Tendsto.add tendsto_const_nhds`. `pde_spectrum_bridge_summary_with_mass` in `ContinuumBridgeDemo.lean` extends the PDE bridge summary to include the massive KG case. Axiom-clean.
- **Lorentzian vacuum EFE bridge**: `minkowski4Manifold_satisfies_vacuum_EFE` — ties E1 + F3 into a single theorem; Minkowski-as-Lorentzian-manifold + flat connection solves vacuum EFE. Axiom-clean.
- **E1 / DiagLorentzianMetric + DiagLorentzianManifold** (`LorentzianManifold.lean`, #53): signature predicate asserting `g_{00} < 0`, `g_{ii} > 0` for `i ≥ 1`, off-diagonal zero. Bundled `DiagLorentzianManifold n = MetricData + Lorentzian witness`. `minkowski4_diagLorentzian` + `minkowski4Manifold` exhibit Minkowski 4-space as a Lorentzian manifold. Accessors `g_00_neg`, `g_ii_pos`, `g_off_diag`, `g_00_ne_zero`. Axiom-clean.
- **X2 / Covariant derivative on ConnectionData** (`CovariantDerivative.lean`, #31): `nabla_scalar`, `nabla_vector` (`∂_μ V^ν + Γ^ν_{μρ} V^ρ`), `nabla_covector` (`∂_μ ω_ν − Γ^ρ_{μν} ω_ρ`). Flat-connection cases collapse to partials. ℝ-linearity `nabla_{vector,covector}_add`. Axiom-clean.
- **Second Bianchi (flat vacuum case)** (`EinsteinEquations.lean`): `flatConnection_einstein_divergence_zero` — for the flat connection with vanishing partials of G, the divergence vanishes. The vacuous form of `∇_μ G^{μν} = 0`; Levi-Civita full Bianchi needs metric compatibility. Axiom-clean.
- **E5 / Discrete Cauchy foliation existence PROVED** (`CausalFoliation.lean`, #57): `time_monotone_causallyPrecedes` + `time_strict_monotone_strictCausallyPrecedes` give monotonicity of time functions. `timeLevelSet G tf n := {v : τ v = n}`. `timeLevelSet_isAntichain` + `timeLevelSet_disjoint` + `timeLevelSet_covers` prove the three conditions for `IsFoliation`. **`timeFunction_foliation`**: every `TimeFunction` yields a foliation. **`stablyCausal_hasFoliation`**: every stably causal DAG admits a foliation — the discrete analog of Cauchy foliation existence. Full ADM lapse-shift decomposition needs continuum Lorentzian. Axiom-clean.
- **F3 / Einstein equations with Λ** (`EinsteinEquations.lean`, #62): `EinsteinEqLambda M C Λ κ T x` predicate for `G_{μν} + Λ·g_{μν} = κ·T_{μν}` in 4 dimensions. `minkowski4_satisfies_EFE_zero_lambda` (Minkowski + flat solves EFE with Λ=0 + zero SE). `einsteinEqLambda_vacuum_iff` reduces vacuum case. **`minkowski4_flat_vacuum_forces_lambda_zero`**: at μ=ν=1, `-Λ·g_{11} = -Λ`, so flat vacuum EFE forces Λ=0 — de Sitter/anti-de Sitter cannot live on Minkowski+flat. Axiom-clean.
- **T5 / Path Laplacian annihilates constant mode** (`PathHypergraph.lean`): `pathEigenvector_zero_eq_one` — `pathEigenvector n 0 j = 1` (constant). `pathLaplacian_eigen_zero` — `laplacianHyper (pathHypergraph n) (pathEigenvector n 0) v = 0`. The `k=0` case of the path-Laplacian eigenvalue equation. Axiom-clean.
- **Cycle ball-volume at large radius covers everything** (`HypergraphDistance.lean`): `cycleHypergraph_ballVolume_large` — for `n ≥ 2` and `r ≥ n`, `geodesicBallVolume v r = n`. Complement of `cycleHypergraph_ballVolume_zero_exact` (r=0 → 1). Axiom-clean.
- **pde_spectrum_bridge_summary** (`ContinuumBridgeDemo.lean`): single bundled theorem exhibiting the full three-PDE spectral convergence from cycle to circle for any wavenumber `k`. Heat / wave / Schrödinger eigenvalue scalings all match. Analog of `wolfram_physics_bridge_summary` for PDE-to-PDE bridges. Axiom-clean.
- **DiscreteWave / DiscreteSchrödinger continuum-limit spectra PROVED** (`ContinuumLimitStatement.lean`): both `DiscreteWaveToContinuumWave` and `DiscreteSchrodingerToContinuumSchrodinger` (previously `True` stubs) upgraded to concrete spectral-convergence claims and proved. Wave: `n · 2 sin(πk/n) → 2πk` via `n_sin_pi_k_div_n_tendsto`. Schrödinger: `n² · 4 sin²(πk/n) → (2πk)²` as the negative of A4 (`cycleEigenvalue_scaled_tendsto`). The dispersion-relation / Hamiltonian-eigenvalue bridges for both PDEs now match the pattern of A4 (Laplacian spectral bridge). Full propagator-level convergence still needs unitary-convergence infrastructure. Axiom-clean.
- **ID6 partial / Cycle ball-volume formula, base cases** (`HypergraphDistance.lean` + `RemainingObligations.lean`): `cycleHypergraph_ballVolume_zero_exact` — on a connected cycle with `n ≥ 2`, `geodesicBallVolume v 0 = 1`. `dimensionCompatibilityObligation_base_cases` bundles this with the existing `cycleHypergraph_ballVolume_one_exact` (= 3) to close the `r ∈ {0, 1}` cases of the full `r ≤ n/2` ball-volume formula. Full version needs a general cycle-distance characterisation. Axiom-clean.
- **T6 / All seven infrageometry obligations upgraded + baseline cases PROVED** (`RemainingObligations.lean`, #186 COMPLETE): the last two remaining stubs — IQ8 `EMEPersistenceObligation` and IQ9 `PathIntegralObligation` — are upgraded to concrete existence claims (baseline ψ = 0 / α = 0 witnesses). `no_stub_obligations_remain` proves both. T6 final tally: **7/7 upgraded, 5 proved** (IQ6 Fubini-Study/Bhattacharyya, IT5 Latschev connectivity, IT6 scale-trichotomy endpoints, IQ8 EME baseline, IQ9 path-integral baseline); **2 open** (ID6 ball-volume formula, IR7 reverse-engineering existence) — the open ones are real claims with substantive content. No `True ∧ False` stubs remain anywhere.
- **IT6 / Scale trichotomy obligation PROVED (cycle endpoints)** (`RemainingObligations.lean`, #138): upgraded `ScaleTrichotomyObligation` from `True ∧ False` to a concrete claim about the cycle hypergraph: at `ε = 0` no non-trivial VR 1-simplex exists (distinct vertices have `dist > 0` — quantum regime endpoint), at `ε = n` every pair is a VR 1-simplex (complete — coarse regime endpoint). `scaleTrichotomyObligation_holds` closes both endpoints via `Reachable.pos_dist_of_ne` + `SimpleGraph.Walk.IsPath.length_lt`.
- **IT5 / Latschev obligation PROVED (connectivity form)** (`RemainingObligations.lean`, #137): `latschevObligation_holds` proves `LatschevObligation` — for every `n ≥ 2` and every `u, v : Fin n`, `(cycleHypergraph n).dist u v < (n : ℝ) + 1`. Proof uses `SimpleGraph.Walk.IsPath.length_lt` (shortest path on a finite graph has length `< Fintype.card V = n`) in the reachable branch, and `dist = 0 < n + 1` in the unreachable branch. This closes the discrete-connectivity form of the Latschev obligation; the full GH-homotopy-equivalence form still needs Mathlib's `Gromov_Hausdorff` + `HomotopyEquiv` composed, which remains future work. Axiom-clean.
- **R4 (partial) / Curved discrete-Ricci bridge — non-flat witness** (`CurvedRicciBridge.lean`, #179): `warpedDiag2 : MetricData 2` is a warped 2-D metric with `g₁₁ = 1 + x₀²`. `warpedDiag2_christoffel_nonzero` proves `Γ¹_{01} ≠ 0` whenever `x 0 ≠ 0`. `curvedRicciBridgeObligation` is the existence statement of a non-flat continuum target (witnessed by `warpedDiag2` at `x = (1,0)`). `threeRegular_formanRicci_nonzero`: on any 3-regular graph the Forman-Ricci is `−2`, giving the discrete-side non-flat signature. Full R4 (Forman → continuum Ricci convergence) still needs scaling + convergence; the non-flat-witness half is now formalised. Axiom-clean.
- **T5 (partial) / Path hypergraph type + free-path spectrum sentinel + spectral gap** (`PathHypergraph.lean`, #185): `pathEdge n i = {i, i+1}` builds `pathHypergraph n` on `Fin n` with `n−1` edges. `pathHypergraph_edges_card_le` (|E| ≤ n−1). **Corrected to free-path formula**: `pathEigenvalue n k = −4 sin²(kπ/(2n))` and `pathEigenvector n k j = cos(kπ(2j+1)/(2n))` — these match the actual (no-boundary-condition) Laplacian on `pathHypergraph n`, not the Dirichlet spectrum. `pathEigenvalue_nonpos` (non-positivity), `pathEigenvalue_ground_zero` (k=0 mode vanishes), `pathEigenvalue_one_neg` (first non-constant mode strictly negative for n ≥ 2 — path spectral gap). Axiom-clean. Path is the open-chain analog of `cycleHypergraph`; together they are the 1-D atomic factors for d-torus products.
- **Branchial quantum-mechanics bridge closed (I2/I3/I4/I5/I6/I7/I9, R3)** (`BranchialHilbert.lean`, `BranchialSchrodinger.lean`): `BranchialHilbert S := EuclideanSpace ℂ S` (finite-dim ℂ-Hilbert alias) with ℂ-linear adjacency operator `branchialAdjLM` and Hermitian self-adjointness `branchialAdjLM_inner` for symmetric adj. `BranchialAmplitude` + Born rule `bornProbability` with `sum_bornProbability = ‖ψ‖²`. Uniform branchial measure `branchialUniformWeight` summing to 1. Full Schrödinger evolution `BranchialSchrodinger adj u v` with proven unitarity `branchialSchrodinger_unitary_evolution` (total probability conserved via self-adjointness). `BranchialObservable S` structure + `branchialAdjObservable`. `expectationValue A ψ := ⟨ψ, A ψ⟩` with real-valuedness for Hermitian operators. `branchialSliceFintype` + `branchialSliceHilbert` bridge to concrete branchial slice. 8/10 I-series tasks done.
- **Heat-kernel decay + eigenvector orthogonality (D6 partial)** (`HeatKernelDecay.lean`, `SymmEigenOrthogonal.lean`): `heatKernel_cycleHypergraph_firstMode_tendsto_zero` and `heatKernel_cycleHypergraph_nonzero_mode_tendsto_zero` prove pointwise decay of every non-constant mode. `heatKernel_cycleHypergraph_constMode_invariant` proves the constant mode is preserved. `heatKernel_cycleHypergraph_const_plus_mode_tendsto` shows linear combinations converge to the constant component. `symm_eigenvectors_orthogonal` + `cycleEigenvector_orthogonal` + `cycleEigenvector_const_orthogonal_nonzero` + `cycleEigenvector_first_half_orthogonal` establish orthogonality of eigenvectors with distinct eigenvalues, closing the spectral-theorem step. `cycleEigenvalue_strict_mono_first_half` + `cycleEigenvalue_ne_first_half` prove pairwise distinctness of first-half eigenvalues.
- **IT3 (Pavel Hajek): Hodge Laplacian spectrum baseline** (`HodgeLaplacianSpectrum.lean`): `vrHodge0_add`, `vrHodge0_smul` (ℝ-linearity), `vrHodge0_has_zero_eigenvalue` (constants are in the kernel — 0-form Hodge cohomology). Spectral foundation for IT3 closed.
- **IQ6: Fubini-Study/Bhattacharyya bound, upgraded to real content + proved** (`RemainingObligations.lean`): `FubiniStudyLimitObligation` now states `‖⟨ψ, φ⟩‖ ≤ ∑ s, ‖ψ s‖ · ‖φ s‖` (Cauchy-Schwarz / Bhattacharyya bound on branchial amplitudes). Proved as `fubiniStudyBhattacharyya_bound` via `PiLp.inner_apply` + `norm_sum_le` + `norm_mul` + `Complex.norm_conj`. T6 progress: 3/7 obligations upgraded.
- **T6 partial / Upgrade obligations to real content** (`RemainingObligations.lean`, #186): IR7 `ReverseEngineeringObligation`, ID6 `DimensionCompatibilityObligation`, and IQ6 `FubiniStudyLimitObligation` now carry real Lean content. Four others (Latschev IT5, scale trichotomy IT6, EME persistence IQ8, path integral IQ9) remain `True ∧ False` pending additional Mathlib infrastructure.
- **A5 / Counting measure on Hypergraph V + pushforward** (`HypergraphMeasure.lean`): `countingMeasure`, `uniformProbability`, `pushforwardCounting`, `pushforwardUniform`. Unblocks A6/A7.
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

- [x] **R3 #178 (partial)** — `ℓ²(BranchialSlice)` as Hilbert space with branchial adjacency operator. `BranchialHilbert.lean` defines `BranchialHilbert S := EuclideanSpace ℂ S` (finite-dim ℂ-Hilbert alias); `branchialAdjLM` is the ℂ-linear adjacency operator; `branchialAdjLM_inner` proves Hermitian self-adjointness for symmetric `adj` (spectral-theorem prerequisite for real spectrum). Remaining: I2 uniform measure, I3 amplitudes, I5 unitary evolution (`exp (i t A)`).
- [ ] **R4 #179** — Curved discrete-Ricci convergence beyond flat. First non-zero Forman-Ricci convergence case.
- [ ] **A5 #16** — Counting measure on `Hypergraph V` + pushforward (groundwork for A6 / weak convergence, A7 / Wasserstein).
- [ ] **A7 #18** — Wasserstein-1 convergence rate `O(1/n)` for counting measures.
- [~] **D6 #47 (partial)** — Long-time convergence of heat solution to uniform. `HeatKernelDecay.lean` proves each non-constant eigenmode (`1 ≤ k < n`) tends to `0` coordinate-wise under heat flow: `heatKernel_cycleHypergraph_firstMode_tendsto_zero` (k=1 spectral gap), `heatKernel_cycleHypergraph_nonzero_mode_tendsto_zero` (all non-zero modes), `heatKernel_cycleHypergraph_const_plus_mode_tendsto` (linear combinations of constant + one non-constant mode converge to the constant-mode component). `SymmEigenOrthogonal.lean` adds the classical spectral-theorem step `cycleEigenvector_orthogonal` — cycle eigenvectors with distinct eigenvalues are orthogonal. Remaining: verification that all `n` cycle eigenvalues are distinct (so they span), plus Parseval-style decomposition of arbitrary `ψ : Fin n → ℝ`.
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

- [x] **I2 #85** — Branchial measure (uniform on finite slice). `BranchialHilbert.lean` defines `branchialUniformWeight` with `sum = 1` when the slice is nonempty.
- [x] **I3 #86** — Branchial amplitudes (ℂ-valued). `BranchialHilbert.lean` defines `BranchialAmplitude S := BranchialHilbert S` + Born-rule probability `bornProbability ψ s := Complex.normSq (ψ s)` with `sum = ‖ψ‖²`.
- [x] **I4 #87** — `ℓ²(slice)` Hilbert space (= R3 partial; `BranchialHilbert.lean`).
- [x] **I5 #88** — Branchial evolution as unitary. `BranchialSchrodinger.lean` proves `branchialSchrodinger_unitary_evolution` — Schrödinger `i∂_tψ = Aψ` with adjacency `A` preserves total probability `∑(u² + v²)` on real/imaginary decomposition. Closes the Stone-type unitarity claim for the finite-dim branchial slice.
- [x] **I7 #90** — Expectation values + Born rule. `BranchialHilbert.lean` defines `expectationValue A ψ := ⟨ψ, A ψ⟩` with `expectationValue_re_of_symm` (real for Hermitian A) and `expectationValue_eigenvector` (eigenvalue · ‖ψ‖² for eigenvectors).
- [x] **I6 #89** — Observables as Hermitian operators. `BranchialHilbert.lean` defines `BranchialObservable S` as a ℂ-linear self-adjoint operator structure; `branchialAdjObservable` packages the adjacency operator as an observable; `expectationValue_real` derives reality of the measurement outcome.
- [x] **I9 #92** — Schrödinger on branchial graph. Closed by `BranchialSchrodinger.lean` (= I5). The `BranchialSchrodinger adj u v` structure IS the Schrödinger equation on the branchial slice with adjacency Hamiltonian.

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
