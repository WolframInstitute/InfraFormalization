# Next steps — what's done, in flight, and waiting

Lives next to [`README.md`](README.md) / [`INDEX.md`](INDEX.md) / [`FINDINGS.md`](FINDINGS.md) / [`COVERAGE_MAP.md`](COVERAGE_MAP.md). Curated by hand.

## Recently shipped (selected highlights)

- **Grounding-audit closure (2026-04-23)**: **all four action items closed**. Every continuum GR object now carries an attached hypergraph-side origin-obligation Prop, with provably-inhabited witnesses for the flat cases.
  - `HypergraphMetricBridges.lean` + `RuleWitnesses.lean` (G2) — every metric in the zoo has a `HypergraphMetricOriginObligation` / `HypergraphPartialMetricOriginObligation` Prop; all **proved inhabited** using `identitySystem Unit` + `cycleHypergraph` + `emptyTrajectory` (the identity rule is load-bearing in each proof).
  - `CausalLorentzianBridge.lean` (G3) — `LorentzianManifoldOriginObligation` binds `CausalGraph V` + scale; witnessed via `trivialCausalGraph`.
  - `FiberedGraphConnectionBridge.lean` (G1) — `ConnectionDataOriginObligation` binds `FiberedGraph V W` + `FiberedGraph.Connection F` + scale; flat-connection case witnessed via `trivialFiberedGraph` + `trivialConnection`.
  - `EinsteinEquationsBridge.lean` (G4) — `EFEOriginObligation` bundles EFE-satisfaction with metric + connection origins; `minkowski4_flat_vacuum_EFE_originated_global` is the **first complete rule → metric → connection → EFE chain**.
  - `RuleSearch.lean` — decidable `IsConservative`; catalog of 5 rules (`identityRule`, `selfMapRule`, `edgeDuplicateRule`, `tripleToEdgeRule`, `pairToTriangleRule`); proved screens over `conservativeCatalog` / `growthCatalog`; `minkowski4_from_growthRule` uses `edgeDuplicateRule` load-bearingly; `conservative_blocks_dim_geq_one` formalises Gorard's structural block.

- **Hypergraph-grounded overnight grind (2026-04-23)**: dedicated to `GROUNDING_AUDIT.md`-compliant work only.
  - `PathHypergraphDistance.lean` — path heat kernel preserves constants; row-sum zero.
  - `CycleHeatDecayBounds.lean` — spectral gap, first-mode explicit decay, constant fixed.
  - `FisherMetricExtended.lean` — ℝ-linearity + PSD for Van Le branchial Fisher metric.
  - `HodgeLaplacianBounds.lean` — Pavel Hajek IT3 Hodge 0-Laplacian negative semi-definite (Dirichlet energy argument).
  - `BlowupPoissonConcrete.lean` — concrete bracket instances (zero, difference) + vertex/edge-count invariants for Kolcz M3 Lie-Poisson.
  - `EMETracker.lean` — Ahmed M7 EME persistence on Trajectory + concrete edge-count-bounded EME.
  - `BranchialCommutator.lean` — BranchialMultiRelated reflexive-transitive closure (symmetry + transitivity) for Ahmed-Zapata M5.
  - `ProperTimeBounds.lean` — `ChainOfLength` length-0/length-1 characterisations and concatenation lemmas.
  - `RuleSignatureEquiv.lean` — `RuleSignature.sigEquiv` (refl/symm/trans) + empty-hypergraph signature theorems.


- **Schwarzschild Lorentzian signature** (`Schwarzschild.lean`): `sgg_lorentzian_pointwise` — on every exterior point, the Schwarzschild metric `sgg M x` has diagonal Lorentzian signature (g_00 < 0, g_ii > 0, off-diagonal = 0). `SchwarzschildVacuumObligation M` is the statement-level B4 obligation. Axiom-clean.
- **2-sphere curvature witnesses** (`TwoSphere.lean`): `sphereChristoffel_1_0_1 = cot(θ)` closed form + `sphereChristoffel_nonzero` existence witness at generic points. Full "beyond flat" demonstration for the S² target.
- **GrandTour.lean** — headline-theorems tour. One-line examples referencing the eight main results (operator convergence, PDE spectrum, D6 multi-mode, T6 obligations, F3+Minkowski-vacuum, E1+E5, GR zoo, PDE bridge + curved Ricci).
- **gr_metric_zoo** (`GRMetricsDemo.lean`): single bundled theorem exhibiting all formalised GR target metrics — Minkowski, FLRW, Schwarzschild, Reissner-Nordström, de Sitter, 2-sphere. Centrepiece status marker for the continuum-target side of the bridge ladder. Axiom-clean.
- **de Sitter metric** (`DeSitter.lean`): `dsLapse Λ r = 1 − Λr²/3`, `dsG Λ`, `dsGinv Λ`, `DSValid Λ x`. `dsLapse_minkowski` (Λ=0 reduces to flat), `dsLapse_pos_iff` (cosmological horizon location). The curved-vacuum geometry that accommodates non-zero Λ (which Minkowski+flat cannot, per `minkowski4_flat_vacuum_forces_lambda_zero`). Axiom-clean.
- **2-sphere S² metric** (`TwoSphere.lean`): `sphereG`, `sphereGinv`, `sphereDg`, `SphereValid x := sin θ ≠ 0`. `spherePartial : PartialMetricData 2` fully bundled. `sphereChristoffel_0_1_1 = -sin(θ) cos(θ)` — explicit non-zero Christoffel on a genuinely curved Riemannian target (pairs with 3-regular-graph signature for R4 beyond-flat bridge). Axiom-clean.
- **B8 / Reissner-Nordström components** (`ReissnerNordstrom.lean`): `rnLapse M Q r = 1 − 2M/r + Q²/r²`. `rnG` diagonal charged-Schwarzschild metric, `rnGinv` diagonal reciprocal. `RNValid M Q x` exterior predicate (r > 0 ∧ rnLapse > 0 ∧ sin θ ≠ 0). `rnLapse_schwarzschild` (Q=0 recovers Schwarzschild), `rnLapse_pos_of_large_r_Q_zero` (r > 2M > 0 gives positive lapse at Q=0). Axiom-clean.
- **B6 / FLRW metric as PartialMetricData** (`FLRW.lean`): `flrwG a`, `flrwGinv a`, `flrwDg a da` bundle `ds² = -dt² + a(t)²(dx²+dy²+dz²)` into `flrwPartial a da : PartialMetricData 4` with `FLRWValid a x := a(x 0) ≠ 0` (excluding big-bang singularities). All axioms proved on the validity domain. `flrwChristoffel_0_00 = 0` (time-time Christoffel vanishes since g_{00} is constant). Axiom-clean.
- **X1 / PartialMetricData + B5 / Schwarzschild-as-PartialMetricData** (`PartialMetricData.lean`, `Schwarzschild.lean`,): `PartialMetricData n` carries a domain predicate `valid : (Fin n → ℝ) → Prop` so axioms are conditioned on the validity region — the clean way to type Schwarzschild (where `ginv_mul` fails inside the horizon). `MetricData.toPartial` coerces any full metric. `christoffel` + `christoffel_symm` on the validity domain. **`schwarzschildPartial M`** bundles Schwarzschild into a `PartialMetricData 4` with `valid = SchwarzschildValid M` (exterior region). `schwarzschildPartial_christoffel` proves equivalence with the existing explicit `schwarzschildChristoffel`. Axiom-clean.
- **Klein-Gordon continuum spectrum PROVED** (`ContinuumLimitStatement.lean`): `DiscreteKleinGordonSpectrum m` — lattice KG dispersion `n² · 4 sin²(πk/n) + m²` converges to `(2πk)² + m²` for every `m ∈ ℝ` and `k`. Proved via Schrödinger bridge + `Filter.Tendsto.add tendsto_const_nhds`. `pde_spectrum_bridge_summary_with_mass` in `ContinuumBridgeDemo.lean` extends the PDE bridge summary to include the massive KG case. Axiom-clean.
- **Lorentzian vacuum EFE bridge**: `minkowski4Manifold_satisfies_vacuum_EFE` — ties E1 + F3 into a single theorem; Minkowski-as-Lorentzian-manifold + flat connection solves vacuum EFE. Axiom-clean.
- **E1 / DiagLorentzianMetric + DiagLorentzianManifold** (`LorentzianManifold.lean`): signature predicate asserting `g_{00} < 0`, `g_{ii} > 0` for `i ≥ 1`, off-diagonal zero. Bundled `DiagLorentzianManifold n = MetricData + Lorentzian witness`. `minkowski4_diagLorentzian` + `minkowski4Manifold` exhibit Minkowski 4-space as a Lorentzian manifold. Accessors `g_00_neg`, `g_ii_pos`, `g_off_diag`, `g_00_ne_zero`. Axiom-clean.
- **X2 / Covariant derivative on ConnectionData** (`CovariantDerivative.lean`): `nabla_scalar`, `nabla_vector` (`∂_μ V^ν + Γ^ν_{μρ} V^ρ`), `nabla_covector` (`∂_μ ω_ν − Γ^ρ_{μν} ω_ρ`). Flat-connection cases collapse to partials. ℝ-linearity `nabla_{vector,covector}_add`. Axiom-clean.
- **Second Bianchi (flat vacuum case)** (`EinsteinEquations.lean`): `flatConnection_einstein_divergence_zero` — for the flat connection with vanishing partials of G, the divergence vanishes. The vacuous form of `∇_μ G^{μν} = 0`; Levi-Civita full Bianchi needs metric compatibility. Axiom-clean.
- **E5 / Discrete Cauchy foliation existence PROVED** (`CausalFoliation.lean`): `time_monotone_causallyPrecedes` + `time_strict_monotone_strictCausallyPrecedes` give monotonicity of time functions. `timeLevelSet G tf n := {v : τ v = n}`. `timeLevelSet_isAntichain` + `timeLevelSet_disjoint` + `timeLevelSet_covers` prove the three conditions for `IsFoliation`. **`timeFunction_foliation`**: every `TimeFunction` yields a foliation. **`stablyCausal_hasFoliation`**: every stably causal DAG admits a foliation — the discrete analog of Cauchy foliation existence. Full ADM lapse-shift decomposition needs continuum Lorentzian. Axiom-clean.
- **F3 / Einstein equations with Λ** (`EinsteinEquations.lean`): `EinsteinEqLambda M C Λ κ T x` predicate for `G_{μν} + Λ·g_{μν} = κ·T_{μν}` in 4 dimensions. `minkowski4_satisfies_EFE_zero_lambda` (Minkowski + flat solves EFE with Λ=0 + zero SE). `einsteinEqLambda_vacuum_iff` reduces vacuum case. **`minkowski4_flat_vacuum_forces_lambda_zero`**: at μ=ν=1, `-Λ·g_{11} = -Λ`, so flat vacuum EFE forces Λ=0 — de Sitter/anti-de Sitter cannot live on Minkowski+flat. Axiom-clean.
- **T5 / Path Laplacian annihilates constant mode** (`PathHypergraph.lean`): `pathEigenvector_zero_eq_one` — `pathEigenvector n 0 j = 1` (constant). `pathLaplacian_eigen_zero` — `laplacianHyper (pathHypergraph n) (pathEigenvector n 0) v = 0`. The `k=0` case of the path-Laplacian eigenvalue equation. Axiom-clean.
- **Cycle ball-volume at large radius covers everything** (`HypergraphDistance.lean`): `cycleHypergraph_ballVolume_large` — for `n ≥ 2` and `r ≥ n`, `geodesicBallVolume v r = n`. Complement of `cycleHypergraph_ballVolume_zero_exact` (r=0 → 1). Axiom-clean.
- **pde_spectrum_bridge_summary** (`ContinuumBridgeDemo.lean`): single bundled theorem exhibiting the full three-PDE spectral convergence from cycle to circle for any wavenumber `k`. Heat / wave / Schrödinger eigenvalue scalings all match. Analog of `wolfram_physics_bridge_summary` for PDE-to-PDE bridges. Axiom-clean.
- **DiscreteWave / DiscreteSchrödinger continuum-limit spectra PROVED** (`ContinuumLimitStatement.lean`): both `DiscreteWaveToContinuumWave` and `DiscreteSchrodingerToContinuumSchrodinger` (previously `True` stubs) upgraded to concrete spectral-convergence claims and proved. Wave: `n · 2 sin(πk/n) → 2πk` via `n_sin_pi_k_div_n_tendsto`. Schrödinger: `n² · 4 sin²(πk/n) → (2πk)²` as the negative of A4 (`cycleEigenvalue_scaled_tendsto`). The dispersion-relation / Hamiltonian-eigenvalue bridges for both PDEs now match the pattern of A4 (Laplacian spectral bridge). Full propagator-level convergence still needs unitary-convergence infrastructure. Axiom-clean.
- **ID6 CLOSED / Cycle ball-volume formula FULLY PROVED** (`HypergraphDistance.lean` + `RemainingObligations.lean`): `cycleHypergraph_ballVolume_exact` — for every `n ≥ 2`, `r` with `2r+1 ≤ n`, and `v : Fin n`, `geodesicBallVolume v r = 2r + 1`. `dimensionCompatibilityObligation_holds` proves the full obligation. Lower bound via shift-family Finsets; upper bound via walk structural induction (`cycleHypergraph_walk_in_shift`) + composition lemmas (F∘F, F∘G, G∘F, G∘G). Axiom-clean.
- **T6 / ALL seven infrageometry obligations PROVED** (`RemainingObligations.lean`, COMPLETE): `all_obligations_hold` bundles the six non-trivial closures (IT6 `scaleTrichotomyObligation_holds`, ID6 `dimensionCompatibilityObligation_holds`, IQ6 `fubiniStudyBhattacharyya_bound`, IQ8 EMEPersistence baseline, IQ9 PathIntegral baseline, IR7 `reverseEngineeringObligationRefined_holds`). Zero open obligations at this level. The original unrefined IR7 is provably FALSE (`not_reverseEngineeringObligation`).
- **IT6 / Scale trichotomy obligation PROVED (cycle endpoints)** (`RemainingObligations.lean`): upgraded `ScaleTrichotomyObligation` from `True ∧ False` to a concrete claim about the cycle hypergraph: at `ε = 0` no non-trivial VR 1-simplex exists (distinct vertices have `dist > 0` — quantum regime endpoint), at `ε = n` every pair is a VR 1-simplex (complete — coarse regime endpoint). `scaleTrichotomyObligation_holds` closes both endpoints via `Reachable.pos_dist_of_ne` + `SimpleGraph.Walk.IsPath.length_lt`.
- **IT5 / Latschev obligation PROVED (connectivity form)** (`RemainingObligations.lean`): `latschevObligation_holds` proves `LatschevObligation` — for every `n ≥ 2` and every `u, v : Fin n`, `(cycleHypergraph n).dist u v < (n : ℝ) + 1`. Proof uses `SimpleGraph.Walk.IsPath.length_lt` (shortest path on a finite graph has length `< Fintype.card V = n`) in the reachable branch, and `dist = 0 < n + 1` in the unreachable branch. This closes the discrete-connectivity form of the Latschev obligation; the full GH-homotopy-equivalence form still needs Mathlib's `Gromov_Hausdorff` + `HomotopyEquiv` composed, which remains future work. Axiom-clean.
- **R4 (partial) / Curved discrete-Ricci bridge — non-flat witness** (`CurvedRicciBridge.lean`): `warpedDiag2 : MetricData 2` is a warped 2-D metric with `g₁₁ = 1 + x₀²`. `warpedDiag2_christoffel_nonzero` proves `Γ¹_{01} ≠ 0` whenever `x 0 ≠ 0`. `curvedRicciBridgeObligation` is the existence statement of a non-flat continuum target (witnessed by `warpedDiag2` at `x = (1,0)`). `threeRegular_formanRicci_nonzero`: on any 3-regular graph the Forman-Ricci is `−2`, giving the discrete-side non-flat signature. Full R4 (Forman → continuum Ricci convergence) still needs scaling + convergence; the non-flat-witness half is now formalised. Axiom-clean.
- **R4 (extension) / warpedDiag2 curved Ricci closed form** (`WarpedDiag2C2.lean`): `warpedDiag2_C2 : MetricDataC2 2` supplies `ddg` (∂_0 ∂_0 g_{11} = 2) and `dginv` (∂_0 g^{11} = -2x₀/(1+x₀²)²). Real closed-form curvature computed via `leviCivitaConnection`: `warpedDiag2_riemann_0_1_0_1 = -1/(1+x₀²)`, `warpedDiag2_riemann_1_0_1_0 = -1/(1+x₀²)²`, `warpedDiag2_ricci_0_0 = -1/(1+x₀²)²`, `warpedDiag2_ricci_1_1 = -1/(1+x₀²)`. Generic lemma `riemann_diag_zero` (`R^ρ_{σμμ} = 0` from `riemann_antisymm`). The first real curved-case Ricci end-to-end in the project; off-diagonal Ricci + the Einstein identity `R_{μν} = K(x) · g_{μν}` with `K(x) = -1/(1+x₀²)²` are the follow-ups tracked under #217.
- **T5 (partial) / Path hypergraph type + free-path spectrum sentinel + spectral gap** (`PathHypergraph.lean`): `pathEdge n i = {i, i+1}` builds `pathHypergraph n` on `Fin n` with `n−1` edges. `pathHypergraph_edges_card_le` (|E| ≤ n−1). **Corrected to free-path formula**: `pathEigenvalue n k = −4 sin²(kπ/(2n))` and `pathEigenvector n k j = cos(kπ(2j+1)/(2n))` — these match the actual (no-boundary-condition) Laplacian on `pathHypergraph n`, not the Dirichlet spectrum. `pathEigenvalue_nonpos` (non-positivity), `pathEigenvalue_ground_zero` (k=0 mode vanishes), `pathEigenvalue_one_neg` (first non-constant mode strictly negative for n ≥ 2 — path spectral gap). Axiom-clean. Path is the open-chain analog of `cycleHypergraph`; together they are the 1-D atomic factors for d-torus products.
- **Branchial quantum-mechanics bridge closed (I2/I3/I4/I5/I6/I7/I9, R3)** (`BranchialHilbert.lean`, `BranchialSchrodinger.lean`): `BranchialHilbert S := EuclideanSpace ℂ S` (finite-dim ℂ-Hilbert alias) with ℂ-linear adjacency operator `branchialAdjLM` and Hermitian self-adjointness `branchialAdjLM_inner` for symmetric adj. `BranchialAmplitude` + Born rule `bornProbability` with `sum_bornProbability = ‖ψ‖²`. Uniform branchial measure `branchialUniformWeight` summing to 1. Full Schrödinger evolution `BranchialSchrodinger adj u v` with proven unitarity `branchialSchrodinger_unitary_evolution` (total probability conserved via self-adjointness). `BranchialObservable S` structure + `branchialAdjObservable`. `expectationValue A ψ := ⟨ψ, A ψ⟩` with real-valuedness for Hermitian operators. `branchialSliceFintype` + `branchialSliceHilbert` bridge to concrete branchial slice. 8/10 I-series tasks done.
- **Heat-kernel decay + eigenvector orthogonality (D6 partial)** (`HeatKernelDecay.lean`, `SymmEigenOrthogonal.lean`): `heatKernel_cycleHypergraph_firstMode_tendsto_zero` and `heatKernel_cycleHypergraph_nonzero_mode_tendsto_zero` prove pointwise decay of every non-constant mode. `heatKernel_cycleHypergraph_constMode_invariant` proves the constant mode is preserved. `heatKernel_cycleHypergraph_const_plus_mode_tendsto` shows linear combinations converge to the constant component. `symm_eigenvectors_orthogonal` + `cycleEigenvector_orthogonal` + `cycleEigenvector_const_orthogonal_nonzero` + `cycleEigenvector_first_half_orthogonal` establish orthogonality of eigenvectors with distinct eigenvalues, closing the spectral-theorem step. `cycleEigenvalue_strict_mono_first_half` + `cycleEigenvalue_ne_first_half` prove pairwise distinctness of first-half eigenvalues.
- **IT3 (Pavel Hajek): Hodge Laplacian spectrum baseline** (`HodgeLaplacianSpectrum.lean`): `vrHodge0_add`, `vrHodge0_smul` (ℝ-linearity), `vrHodge0_has_zero_eigenvalue` (constants are in the kernel — 0-form Hodge cohomology). Spectral foundation for IT3 closed.
- **IQ6: Fubini-Study/Bhattacharyya bound, upgraded to real content + proved** (`RemainingObligations.lean`): `FubiniStudyLimitObligation` now states `‖⟨ψ, φ⟩‖ ≤ ∑ s, ‖ψ s‖ · ‖φ s‖` (Cauchy-Schwarz / Bhattacharyya bound on branchial amplitudes). Proved as `fubiniStudyBhattacharyya_bound` via `PiLp.inner_apply` + `norm_sum_le` + `norm_mul` + `Complex.norm_conj`. T6 progress: 3/7 obligations upgraded.
- **T6 partial / Infrageometry obligations: upgraded from True ∧ False to real Prop types** (`RemainingObligations.lean`): `all_obligations_hold` bundles the substantive closures (IT5 `latschevObligation_holds`, IT6 `scaleTrichotomyObligation_holds`, ID6 `dimensionCompatibilityObligation_holds`, IQ6 `fubiniStudyBhattacharyya_bound`, IR7-refined `reverseEngineeringObligationRefined_holds`) together with IQ8 + IQ9 cosmetic zero-witness baselines (reopened as tasks #154 / #155 for real content). The original unrefined IR7 is provably FALSE via `not_reverseEngineeringObligation`.
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

- **IR7** — Reverse-engineer rule from target signature.
- **IT5** — Latschev theorem (as Prop obligation; proof for cycles).
- **IT6** — Scale-dependence trichotomy theorem.
- **ID6** — Compatibility theorem: all dimension notions agree on regular lattices.
- **ID7** — Spectral dimension via heat-kernel trace (heat trace now defined; small-`t` asymptotics pending).
- **IB2** — Causal-branchial-trivial commutator theorem.
- **IQ6** — Fubini-Study as limit of Fisher under refinement.
- **IQ8** — EME persistence as branchial observable.
- **IQ9** — Path integral over singleway causal graphs.

## Ready to pick up

### Near-term (Rung-1/Rung-2 follow-ons — the machinery is in hand)

- [x] **R3** — `ℓ²(BranchialSlice)` as ℂ-Hilbert space with branchial adjacency operator (done with Born rule, uniform measure, unitary evolution, Hermitian observables).
- [~] **R4 (in progress)** — Curved discrete-Ricci convergence beyond flat. First non-zero Forman-Ricci convergence case.
- [x] **A5** — Counting measure on `Hypergraph V` + pushforward (complete; groundwork for A6 / A7).
- [~] **A6 (in progress)** — Weak convergence of scaled counting measure → Lebesgue on [0,1). Monomials `1, x, x², x³` each have a closed convergence proof (`A6_for_constants`, `A6_for_identity`, `A6_for_sq`, `A6_for_cube`), each following a shared template: Gauss-style summation formula on `Fin n` in ℝ (`sum_fin_val_…`), `A6_…_sum_closed_form` for the Riemann sum, filter convergence of the closed form, and closing against `∫_0^1 x^d dx` via `integral_pow`. A6 is now packaged as a `A6Holds f` predicate with closure under `const_mul`, `add`, and `sub` (the latter two requiring `IntervalIntegrable`), so any polynomial of bounded degree is cheap via linearity (e.g., `A6Holds_poly_deg3` for degree ≤ 3). General continuous case via polynomial approximation is the remaining step.
- [~] **A7 (in progress)** — Wasserstein-1 convergence rate `O(1/n)`. Project-own W_1 now a full pseudometric on finite supports (`WassersteinFinite.lean` + `CycleWasserstein.lean`): `TransportPlan`, `cost`, `wasserstein1 = sInf cost`; `wasserstein1_self_eq_zero`, `wasserstein1_symm`, **`wasserstein1_triangle`** (via `TransportPlan.glue` + `glue_cost_le`); sharp δ-to-δ identity `wasserstein1_delta_eq_dist`; tensor plan + sup-norm bound. Cycle anchor: `cycleMetric_triangle` / `cycleMetricScaled_triangle`; `wasserstein1_cycleDelta_succ = 1/n` (sharp), `wasserstein1_shiftMeasure_le ≤ 1/n` (measure-level 1-step), **`wasserstein1_shiftIter_le : W_1_scaled(μ, shift^k μ) ≤ k/n`** (k-step via triangle induction). A7 zero-witness baseline superseded. Full scaled-counting-measure → Lebesgue convergence rate still pending.
- [ ] **A8** — Lift measure convergence to d-torus.
- [~] **D6 (in progress, partial)** — Long-time convergence of heat solution to uniform. `HeatKernelDecay.lean` + `SymmEigenOrthogonal.lean` cover single-mode decay and eigenvector orthogonality; remaining: distinctness of all `n` cycle eigenvalues + Parseval-style decomposition of arbitrary `ψ : Fin n → ℝ`.
- [x] **D7** — Scaled discrete heat → continuous heat on GH-limit.

### Schwarzschild follow-ons (B-group)

- [ ] **B2** — Schwarzschild Riemann tensor components.
- [ ] **B3** — Schwarzschild `Ric ≡ 0`.
- [ ] **B4** — `schwarzschild_satisfies_vacuum_EFE`.
- [x] **B5** — Schwarzschild as `PartialMetricData` on exterior.

### Curved-metric families (B6–B11)

- [~] **B6 (in progress)** — FLRW (Robertson-Walker) metric.
- [ ] **B7** — FLRW Ricci + Einstein equations with perfect fluid.
- [x] **B8** — Reissner-Nordström metric: `rnPartial M Q : PartialMetricData 4` on exterior validity domain; attached origin-obligation `rn_from_hypergraph M Q` inhabited via `rn_from_hypergraph_proved`.
- [ ] **B9** — Kerr metric.
- [~] **B10 (in progress)** — Ricci symmetry for Levi-Civita connection. Non-flat witness landed on `warpedDiag2` (`warpedDiag2_leviCivita_ricci_symm` / `warpedDiag2_ricci_symm`): diagonal terms are non-zero closed-form expressions, off-diagonal terms are two independently-computed zeros. Supersedes the flat-only cosmetic closure. General Levi-Civita case (metric compatibility + Riemann pair-swap symmetry) pending.
- [~] **B11 (in progress)** — second Bianchi identity `∇_μ G^{μν} = 0`. Non-flat witness landed on `warpedDiag2` via the 2D Einstein identity: `warpedDiag2_scalarCurvature = -2/(1+x₀²)²`, `warpedDiag2_einsteinTensor_zero : G_{μν} ≡ 0`, `warpedDiag2_einstein_divergence_zero`. Every 2D metric satisfies `G ≡ 0` because `Ric = K g ⇒ R = 2K ⇒ G = K g − K g = 0`. General Levi-Civita case (un-contracted Bianchi via metric compatibility) pending.

### Bundle machinery (C-group; Mathlib gap)

- [ ] **C1** — RiemannianMetric bundle structure.
- [ ] **C2** — LorentzianMetric bundle structure.
- [ ] **C3** — Connection on a vector bundle.
- [ ] **C4** — torsion and curvature at bundle level.
- [ ] **C5** — Levi-Civita existence-uniqueness (Koszul).
- [ ] **C6** — bundle Γ consistency with local-coord Γ.
- [ ] **C7** — discrete connection on a hypergraph.
- [ ] **C8** — scaled discrete connection → Levi-Civita.

### Branchial / QM (I-group)

- [x] **I1** — Fintype BranchialSlice for finite systems.
- [x] **I2** — Branchial measure (uniform on finite slice).
- [x] **I3** — Branchial amplitudes (ℂ-valued) + Born rule.
- [x] **I4** — `ℓ²(slice)` Hilbert space.
- [x] **I5** — Branchial evolution as unitary.
- [x] **I6** — Observables as Hermitian operators.
- [x] **I7** — Expectation values + Born rule.
- [ ] **I8** — Branchial → QM Hilbert-space continuum limit.
- [x] **I9** — Schrödinger on branchial graph.
- [ ] **I10** — Path-integral formulation.

### Combined / emergent frameworks (J-group)

- [ ] **J1** — combined causal + branchial structure.
- [ ] **J2** — path integral over causal graphs.
- [ ] **J3** — emergent-gravity (Jacobson / Verlinde style).
- [ ] **J4** — comparison with causal-set theory.
- [ ] **J5** — comparison with LQG spin-foam models.
- [ ] **J6** — AdS/CFT-analog in the Wolfram model.

### Einstein / stress-energy (F-group)

- [x] **F1** — Stress-energy tensor type.
- [x] **F2** — Energy conditions (WEC / NEC / SEC / DEC).
- [x] **F3** — Full Einstein equations with Λ (`EinsteinEqLambda`).
- [ ] **F4** — Schwarzschild as explicit vacuum solution.
- [ ] **F5** — FLRW as explicit solution with matter.
- [ ] **F6** — Kerr as vacuum solution.
- [x] **F7** — Penrose singularity theorem (statement).
- [x] **F8** — Raychaudhuri equation (discrete + continuum).
- [ ] Discrete stress-energy tensor counterpart (F-series continuation).

### Lorentzian-manifold (E-group)

- [x] **E1** — `LorentzianManifold` structure (`DiagLorentzianManifold`).
- [x] **E2** — chronological and causal relations as filters.
- [x] **E3** — light cones, causal future / past.
- [x] **E4** — causality conditions (strong / stable / globally-hyperbolic).
- [~] **E5 (in progress)** — Cauchy surfaces + ADM decomposition (foliation existence proved; lapse-shift pending).
- [ ] **E6** — Lorentzian Gromov-Hausdorff.
- [ ] **E7** — discrete-causal-DAG → continuum Lorentzian convergence.
- [ ] **D11** — Cauchy problem for Einstein evolution (Choquet-Bruhat).

### BBH-numerics (H-group)

- [ ] **H1** — catalog candidate rules from literature.
- [ ] **H2** — empirical dimensional-signatures pipeline.
- [ ] **H3** — candidate rule passing signature screens.
- [ ] **H4** — scaled trajectory → continuum manifold convergence.
- [ ] **H5** — curved-target RicciBridge extensions.
- [ ] **H6** — BBH initial data as hypergraph.
- [ ] **H7** — BBH evolution under candidate rule.
- [ ] **H8** — discrete Ψ₄ extraction matching NR waveforms.
- [ ] **H9** — convergence to BBH merger spacetime.

### Fields / gauge (G-group)

- [x] **G1** — discrete scalar field on `Hypergraph V`.
- [ ] **G2** — discrete gauge field via Rung-4 connection.
- [x] **G3** — discrete Lagrangian density + action.
- [x] **G4** — discrete Euler-Lagrange equations.
- [ ] **G5** — continuum limits of discrete fields.
- [ ] **G6** — HepLean integration.

### Infrageometry in-progress items (carried over across groups)

- [~] **IR7** — reverse-engineer rule from target signature.
- [~] **IB2** — causal-branchial-trivial commutator theorem.
- [x] **ID6 CLOSED** — compatibility theorem: V(v, r) = 2r+1 exact on cycleHypergraph for every r with 2r+1 ≤ n (`dimensionCompatibilityObligation_holds`).
- [~] **ID7** — spectral dimension via heat-kernel trace (small-`t` asymptotics).
- [~] **T5** — path and d-torus Laplacian spectrum closed forms.
- [ ] **IG10** — exponential map via weighted shortest-path counts.
- [ ] **Rule search** — large-scale empirical rule enumeration via `wolframscript` / SetReplace; `RuleSearch.lean` catalog infrastructure is in place.

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

### Pavel Hájek planning items (P-group)

From Pavel Hájek's weekly update and Discord "core dump" (entries dated 2025-10-06 through 2026-04-14). Each item cross-referenced below with existing Lean coverage where applicable; items without existing coverage are tracked as new tasks.

Source items that map to existing coverage:

- Mathematical content of his persistence project: `VietorisRips.lean` (IT1), `HodgeVR.lean` (IT2), `HodgeLaplacianSpectrum.lean` + `HodgeLaplacianBounds.lean` (IT3), persistence barcode (IT4), Latschev obligation proved for cycles (IT5), scale-trichotomy endpoints proved (IT6). Paclet migration itself is M6 (pending).
- Fisher-information side of holographic-duality discussions: `FisherMetric.lean` (IQ5), `FisherMetricExtended.lean`, M2 Van Le Fisher → Fubini-Study bridge completed, IQ6 `fubiniStudyBhattacharyya_bound` proved.
- Classification of graphs with pointwise constant Wolfram-Hausdorff dimension (with Dugan, inspired by Sam Rodkey): `ID1` WH dimension on hypergraphs, `ID2` plateau detection, `ID6` compatibility theorem CLOSED (`dimensionCompatibilityObligation_holds`: V(v,r) = 2r+1 exact on cycle for 2r+1 ≤ n). Tracked explicitly as **P20** below. Web search (2026-04) returned no published Rodkey paper on the topic; the attribution is to a conversational question (Sam Rodkey, GitHub `SamRodkey`, Texas), not to a paper.
- Combinatorial Levi-Civita connection in InfraGaugeTheory: IG1–IG11 covered; C5 Koszul Levi-Civita and C7 discrete connection on a hypergraph pending; `FiberedGraphConnectionBridge.lean` attaches the obligation Prop.
- Carlos's InfraCausality paper: IC1 CausalGraphType, IC2 ObserverChain, IC3 LightRay, IC4 Foliation + ProperTime, IC5 SpatialReconstruction, IC6 MultiFibrationProjection, IC7 EPSAxioms, IC8 MarzkeWheeler; M5 Zapata + Ahmed paper completed.
- Ioana on InfraGaugeTheory coordinatization pipeline: ID4 CoordinatizationDimension completed; M1 IG-intern coordination pending.
- Exponential map at a vertex (shortest-path counts): IG10 pending.
- Tropical geometry: M9 pending.
- 3-body problem as Turing machine: M10 pending.

New tasks P1–P19 (items not yet covered in any existing module or task):

- [ ] **P1** — Delta / simplicial machinery on hypergraphs (face maps, degeneracies, barycentric subdivision, coordinate-squashing for delta-complexes). Core-dump 2025-10-06 / 2025-10-18 / 2025-10-22.
- [ ] **P2** — Cup product on discrete de Rham + comparison of two form definitions (IA de Rham vs VR-complex route). Core-dump 2025-10-06.
- [ ] **P3** — Discrete Chern-Simons amplitude: Hodge propagator on graphs, 1-loop amplitude from ribbon graphs, IBL-∞ twist via Maurer-Cartan (overlaps M4 Pullman). Core-dump 2025-10-06, 2025-11-09.
- [ ] **P4** — Ribbon (hyper)graph structure + Whitehead moves + amplitudohedron-type alternatives (aligned with Kolpakov discussions). Core-dump 2025-10-18, 2025-11-06 + weekly update.
- [ ] **P5** — Sheaves on hypergraphs; restriction maps; sheaf cohomology; orientation sheaf. Core-dump 2025-10-18.
- [ ] **P6** — Koszul signs / graded Lie bracket on (hyper)graph rewriting. Core-dump 2025-10-18, 2025-11-12.
- [ ] **P7** — Homotopy colimit of a rewriting system (simplicial set from hypergraph + simplicial map from rewriting; extend Knill invariants to simplicial sets). Core-dump 2025-10-18.
- [ ] **P8** — Filtrations of multiway systems (vertical, layered, completion). Core-dump 2025-10-21.
- [ ] **P9** — Action principle for hypergraph rewriting (action functional on paths; variational). Carlos Zapata thread. Core-dump 2025-12-10, 2026-02-21.
- [ ] **P10** — n-Lie / Filippov extension of the insertion bracket (IB4) via signed confluence of n+1 rules. Core-dump 2026-02-22.
- [ ] **P11** — Interaction diagrams from causal graphs (light rays as degenerate-interval chains; elementary particles as volume-bounded subgraphs). Core-dump 2025-12-20.
- [ ] **P12** — Chaos theory in hypergraph rewriting (vertical + horizontal chaos). Core-dump 2026-02-02.
- [ ] **P13** — Utkarsh Bajaj twisted-difference operators + ring-of-functions reconstruction theorem. Core-dump 2026-04-14.
- [ ] **P14** — Blow-up rules as renormalization-group flow (via IB4 closure under commutator). Core-dump 2025-11-23.
- [ ] **P15** — Observability tools for hypergraph rewriting (flame graph, waterfall); tooling, not formal Lean theorems. Core-dump 2025-10-06.
- [ ] **P16** — Knill geodesics approximating Riemannian geodesics (extend Latschev); with Janko. Core-dump 2025-11-09.
- [ ] **P17** — Homotopy algebra / homological-algebra scaffold (supports future paclets: quantum topology, homological algebra, homotopy algebras). Core-dump 2025-10-06.
- [ ] **P18** — Holography / Unruh effect discussion track (Rangamani talk, Aaronson group, UT junior researchers); relates to J6 AdS/CFT-analog.
- [ ] **P19** — Hypergraph as (1-skeleton, clique-complex cochain) decomposition (Kolpakov direction).
- [ ] **P20** — Rodkey classification: characterise hypergraphs / graphs for which `localDimension v r` is constant across vertices at each fixed `r` (equivalently, `wolframHausdorffDimension` is vertex-uniform). Partner task with Pavel Hájek and Dugan Hammock; attributed to a question of Sam Rodkey. Infrastructure in place: sufficient chain `AdjTransitive → DistTransitive → BallVolumeVertexUniform → LocalDimensionVertexUniform`; necessary condition `BallVolumeVertexUniform ⇒ uniform SimpleGraph degree` (via `geodesicBallVolume v 1 = 1 + degree v`). Positive example: `cycleHypergraph n` for n ≥ 2 (full chain inhabited via rotation). Negative example: `pathHypergraph n` for n ≥ 3 (endpoints degree 1 vs interior degree 2 blocks radius-1 uniformity). Remaining open: d-torus positive example, general classification theorem, and sharper characterisations (e.g., Cayley structure). Per weekly update 2026-04.

Items deliberately out of scope here: Austin talk, Aaronson group meeting, Mukund Rangamani holography talk attendance (external activities); Vim distance, minimal square covering, git as hypergraph rewriting (off-topic fun posts); Knutt's paper (reference not held here); Turing 2 DS (done by Pavel in GeneralizedShift).

## External communication

- [ ] Structured external comment PDF (audit + refutation chain); to circulate to the Wolfram Institute / submit to arXiv.
- [ ] Publishable infrageometry paper: Phase-3 continuum-limit theorems + the Rung-1/2/3 bridge story (R1 + R2 + R5 + A3 + A4 are the technical core).

## Grounding principle (non-negotiable)

Every continuous structure in this repository must have an explicit hypergraph anchor or be the target of an explicit convergence theorem. See [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md). No silent assumptions; every open obligation is either a `∧ False`-guarded `Prop` (`ContinuumLimitStatement.lean`, `RemainingObligations.lean`) or an explicit pending task above.
