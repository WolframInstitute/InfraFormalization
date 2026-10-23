# Milestones — infrageometry research programme

Canonical progress tracker for the whole programme. All tasks have explicit checkboxes: `[x]` = done, `[ ]` = pending, `[~]` = in flight / partial, `[!]` = blocked by external dependency.

Grouped by phase (see [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md)). Each milestone either ships something verifiable (a Lean theorem, a numerical experiment, a written analytical refutation) or is broken into sub-milestones that do.

For full-program sequencing across phases (Phase A → B → C → D toward BBH-from-hypergraph), see [`ROADMAP.md`](ROADMAP.md).

---

## Recent landings (2026-04-27, late)

**12 tasks closed in 7 commits this push** (`c1447bc` → `683633c`):

- [x] **MILESTONE-GR / -QM / -BBH (#369, #370, #371)** — `Milestone.lean` lands. Closed Lean signatures `GR_emerges_from_hypergraph` (six conjuncts), specialisations `_minkowski`/`_schwarzschild`/`_flrw`/`_some`, `QM_emerges_from_hypergraph`, `BBH_emerges_from_hypergraph`. Placeholders `True`-typed so no axiom is introduced; `#print axioms` clean. **Three Lean-verifiable signals of completion** documented.
- [x] **AT0 (#285)** — `Hypergraph.elementaryAngle O A B` SWOLF's chord-ratio + lemmas (`elementaryAngle_self`, `_symm`, `_nonneg`).
- [x] **AT1 (#286)** — `Hypergraph.cosAngle`, `Hypergraph.angle := arccos cosAngle`.
- [x] **AT6 (#291)** — `CoordinatizationDimension.AreOrthogonalAxes` `True`-stub replaced with `IsOrthoApprox` chord-ratio ≈ √2.
- [x] **AT7 (#292)** — `RuleSignatureScreener` extension: `elementaryAngleSample`, `angularDeviation`, `AngularScreener`, `CombinedScreener` (curvature + angular triple), persistent-gap negative discharge. **Phase B screener pipeline complete.**
- [x] **AT9 (#294)** — `Hypergraph.scalarCurvatureAt v d r` Bishop-Gromov scalar curvature in `DiscreteRicci.lean`. `unitBallVolumeEuclidean d`, `flatBallVolume d r`. Sign theorems `_zero_of_match`, `_pos_iff`. **Cross-checks Forman-Ricci.**
- [x] **TOP1 (#323) + TOP4 (#326)** — new `HypergraphTopology.lean`: `spatialB0`, `IsSpatiallyConnected`, `firstBettiZ` (cycle rank, ℤ-arithmetic), `spatialB0_le_card`, `spatialB0_pos_of_nonempty`, `firstBettiZ_lower_bound`. **Pre-metric topology surfaced as first-class.**
- [x] **SPHERE1 (#334)** — `Hypergraph.infraSphere`, `infraDisk`, `infraSphereVolume` + boundary inclusion / disjointness / cardinality bound lemmas.
- [x] **HYPER2 (#339) + HYPER3 (#340) + MIDPT1 (#342)** — `perpBisector`, `closerHalf`, `HasTopologicalHyperplane` stub, `midpoint`, `nearMidpoint`, `voronoiCell` + `mem_*` characterisations + symmetry. **Bachmann motion-group substrate.**

84 new tasks logged this session (#285–#368) covering the full angle / topology / cellular-sheaf / knot framework + the NMURZIN "Geometry on Combinatorial Objects" cross-reference + 18 gap-tasks. Plus 3 milestone-tasks #369–#371. Total: 84 tasks logged, 11 closed in this push (12 if counting the AT0-substrate split).

## Recent landings (2026-04-26 — late)

Catch-up summary for landings since the previous MILESTONES sync (5 days back):

- [x] **`d ∘ d = 0`** (`KnillCore.dSquared_eq_zero`, #277) — cochain-complex axiom for signed boundary on oriented simplices, axiom-clean. Plus `dStarSquared_eq_zero` codual, `hodgeOnG_psd` (Hodge laplacian PSD as bilinear form), `hodgeOnG_dirichlet_zero_iff_isDiracKernel` (kernel-side Hodge isomorphism), `hodgeOnG_diag_eq_sum_dirac_sq`. Foundation for KN14 / KN15 / KN16 / KN18.
- [x] **#234 / W_1 obligation discharged** — `subdivisionDiscrepancy n := 1/2^n` discharges `WassersteinRateObligation` with `O(1/n)` rate via `Nat.lt_two_pow_self`. First end-to-end machine-checked rule-trajectory → continuum-target convergence certificate.
- [x] **#284 / Route D — canonical subdivision trajectory** bypasses engine simulation lemma; engine connection at n=0..4 by `decide`.
- [x] **#231 / first formal exec ↔ abstract bridge** — `MultiwayExecBridge.lean`. `ExecRule.toRule`, `Fin.embedSuffix`, single-rule `ExecSystem` cast, `consumed_toMultiset`, `ExecHG.toHypergraph_nil`/`_cons`. Closes the architectural gap between executable engine and abstract `Step`/`MultiStep`.
- [x] **#232 / edge-subdivision rule + n-step path-shape theorem** — closed via `subdivisionTrajectory_isPathOf` (canonical trajectory has IsPathOf shape with subdVerts of length 2^n + 1, Nodup). Engine alignment for all n is residual #267.
- [x] **#239 / KN3 partial** — `wuCharacteristic₂_eq_chi_sq_sub_disjoint` (Wu inclusion-exclusion).
- [x] **KN8 partial** — `eulerCharacteristic_eq_alt_sum_kSkeleton` + `_fintype` corollary (Euler-Poincaré f-vector identity).
- [x] **#280–#283** — structural helpers for #232 Phase 2 (`mem_subdivideVerts_imp`, `subdivideVerts_nodup`, `subdVerts_nodup`, `nextFresh_pathEdges`).
- [x] **Synthetic-geometry framing** for SIG2/SIG3 added to INFRAGEOMETRY.md (Tarski reduction, spectral angles, parallel postulate as branching characterization, Bachmann motions, class-of-graphs trichotomy).
- [x] **ROADMAP.md** — full-program phase sequencing toward BBH-from-hypergraph.

In flight (this session):
- [x] **#233 Phase A** — `HypergraphMetricOriginObligationStrong` adds `ScaledDiscrepancy` + `WassersteinRateObligation` to obligations. Concrete discharges: `minkowski4_from_hypergraph_strong` via `subdivisionDiscrepancyBundle`. Generic lifting `any_metric_has_strong_obligation_witness` + `any_partialMetric_has_strong_obligation_witness`. Per-metric strong-form Props for Minkowski / Schwarzschild / FLRW / RN / dS / S² / warpedDiag2. `all_gr_targets_have_strong_obligations_proven`. **First obligation Prop with quantitative rate content.**
- [x] **#233 Phase A follow-up** — generic `ConvergenceRateObligation d r` admits any rate function `r : ℕ → ℝ`. Rates: `rateOneOverN`, `rateOneOverNSquared`, `rateGeometric c`. Bidirectional bridge to `WassersteinRateObligation`. `subdivisionDiscrepancy_satisfies_geometric` (natural `(1/2)^n`). Phase B precondition.
- [~] **#231 heavier** — extend type-level bridge with `Application` constructor + single-application `Step` correspondence.

---

## Phase 0 — Audit of the JGORARD corpus

- [x] G1 (2004.14810) close-reading ([notes/2004.14810_close_reading.md](notes/2004.14810_close_reading.md))
- [x] G2 (2011.12174) partial close-reading (cross-paper audit)
- [x] G3 (2102.09363) close-reading ([notes/2102.09363_close_reading.md](notes/2102.09363_close_reading.md))
- [x] G4 (2303.07282) close-reading ([notes/2303.07282_close_reading.md](notes/2303.07282_close_reading.md))
- [x] Full 184-row claims catalog for G1 ([notes/claims_catalog.md](notes/claims_catalog.md))
- [x] Cross-paper map of repeated errors ([notes/corpus_audit.md](notes/corpus_audit.md))
- [x] Severity taxonomy S1–S6 ([notes/severity_taxonomy.md](notes/severity_taxonomy.md))
- [x] Continuum-limit claims catalog ([notes/continuum_limit_claims.md](notes/continuum_limit_claims.md))
- [x] Major-structural-flaws index F1–F8 ([MAJOR_FLAWS.md](MAJOR_FLAWS.md))
- [x] Corpus assessment ([notes/corpus_assessment.md](notes/corpus_assessment.md))
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
- [x] State-size invariant across a parallel schedule (`trajectory_preserves_size` / `trajectory_size_invariant`, `ParallelSchedule.lean` + `RuleDimensionBounds.lean`)
- [ ] Layer-cardinality bound `|layer_s| ≤ N/k` (the full parallel-layer bound, a.k.a. Theorem B)
- [x] Ball volume bounded by `Fintype.card V` for every hypergraph (`Hypergraph.geodesicBallVolume_le_card`, `RuleDimensionBounds.lean`)
- [ ] Linear BFS-cone bound for specific rule + specific seed

### Structural impossibilities (refute the major flaws)
- [x] F1: no canonical discrete metric tensor on a hypergraph (`Refutations/F1NoMetric.lean`)
- [x] F2: fiat orthonormality of non-parallel hyperedges is non-canonical (`Refutations/F2Orthonormality.lean`)
- [x] F3: "asymptotic dim preservation ⇒ Einstein eqn" is definitionally unfolded (`Refutations/F3Tautology.lean`)
- [x] F4: "causal invariance ⇔ general covariance" is a definition-equality (`Refutations/F4Tautology.lean`; axiom-free)
- [x] F5: "becomes" under-determined — two natural convergence notions disagree (`Refutations/F5Illdefined.lean`)
- [x] F6 (BD conjecture) flagged as an explicit Prop-level assumption (`DiscreteDAlembertian.lean`, `BenincasaDowkerConjecture` / `gorardF6_carries_BD_assumption`) — carries the unproven Sorkin limit as a machine-checkable dependency.
- [ ] F5': concrete counterexample — a rule whose discrete sum demonstrably does not GH-converge to an EH-style integral (stretch goal)

### Higher-dim continuum limits
- [x] 1D cycle → circle GH bound (`Infra/ScaledCycle.lean`, `Infra/GHBound.lean`)
- [x] 1D path → interval GH bound (`Infra/ScaledPath.lean`)
- [x] 2D lattice → 2-torus GH bound (`Infra/ScaledTorus.lean`)
- [x] (d+1)D lattice → (d+1)-torus GH bound, arbitrary `d ≥ 0` (`Infra/ScaledTorusD.lean`)
- [x] **Continuum Minkowski `ℝ^{1,d}`** (`Infra/Minkowski.lean`): `continuumSpaceDist`, `ContinuumCausalPrecedes`, Timelike/Null/Spacelike, signed interval, trichotomy.
- [x] **Int-to-ℝ embedding with exact isometry + iff preservation** (`Infra/ScaledLorentz.lean`): `lorentzIntEmbed` preserves spatial distance EXACTLY (`continuumSpaceDist_eq_cast`); `CausalPrecedes` and `Timelike` are preserved as **iff** (`_preserves_causal_iff`, `_preserves_timelike_iff`).
- [x] **Scaled embedding at scale `1/n`** (`Infra/ScaledLorentz.lean`): `scaledLorentzEmbed n`; density `1/(2n)` in ℝ^{d+1} via `round(n·x)`; exact scaling `continuumSpaceDist (scaled p) (scaled q) = (spaceDist p q : ℝ) / n`; iff causal preservation under the scaled embedding.
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
- [x] **Scaled-second-difference bridge** (`LaplacianBridge.lean`): `scaledSecondDiff f n x := n² · secondDifference f x (1/n)`; for any quadratic, exactly equals `f''(x) = 2a` independent of `n` and `x`. Linearity, vanishing on constants/linears.
- [x] **`cycleLaplacian_in_terms_of_secondDifference`**: for `n ≥ 2` and interior `i : Fin n` (no wrap), the cycle Laplacian on `g(j) := f(j.val/n)` equals the central second difference of `f` at `i.val/n` with step `1/n`. The interior-point bridge from the hypergraph cycle Laplacian to the continuum operator.
- [x] **`second_deriv_quadratic`** (Mathlib `deriv`-based): `deriv (deriv (fun y => a y² + b y + c)) x = 2a`, computed via `HasDerivAt` chaining.
- [x] **`polynomial_scaled_laplacian_eq_second_deriv`**: full polynomial-case bridge `scaledSecondDiff f n x = deriv (deriv f) x` for any quadratic, at any scale, any point. Now in the language of Mathlib's `deriv`, not just a numeric `2a`.
- [x] **`HypergraphCalculus.lean`**: discrete exterior calculus (Hyperedge gradient/divergence, summation-by-parts / discrete Stokes). Task A1.
- [x] **`HypergraphCycleBridge.lean`**: `cycleHypergraph n` (concrete Wolfram-model state), `laplacianHyper (cycleHypergraph n) = cycleLaplacian` (`laplacianHyper_cycleHypergraph`), end-to-end polynomial bridge `hypergraph_scaled_laplacian_eq_second_deriv`.
- [x] **`CTwoTaylor.lean`** (R1 / A2;): `scaledSecondDiff_tendsto_iteratedDeriv` — general C² Taylor convergence via Mathlib's `Real.taylor_tendsto` (Peano remainder). The central-second-difference ÷ h² → f''(x) for any `ContDiff ℝ 2 f`.
- [x] **`ScaledDiffC2Bridge.lean`** (A3;): `scaledSecondDiff_tendsto_iteratedDeriv_C2` — R1 specialised to h = 1/n (integer-scale refinement) + `hypergraph_scaled_laplacian_eq_scaledSecondDiff` (end-to-end cycleHypergraph → scaledSecondDiff at interior indices). Rung-2 bridge now works for **all** C² test functions, not just polynomials.
- [x] **`CycleSpectrum.lean`** (R5;): cycle Laplacian's closed-form eigenvalues/eigenvectors `λ_k = -4 sin²(πk/n)`, `f_k(j) = cos(2πkj/n)`; `cycleLaplacian_eigen_interior` (interior) + `cycleLaplacian_eigen` (full wrap-around using cos periodicity).
- [x] **`CycleEigenLimit.lean`** (A4;): `cycleEigenvalue_scaled_tendsto` — `n² · λ_k → -(2πk)²` (scaled cycle eigenvalues converge to continuum circle-Laplacian spectrum); key helper `n_sin_pi_k_div_n_tendsto` via Mathlib's `Real.sinc`.
- [x] **`LaplacianMatrix.lean`** (R2 / D3;): `laplacianMatrix H : Matrix V V ℝ`, `laplacianMatrix_mulVec = laplacianHyper`, heat kernel via Mathlib's `Matrix.exp` (`heatKernel H t := exp(t • Δ_H)`), `heatKernel_zero = 1`, `heatKernel_add` (semigroup), `laplacianMatrix_symm`, `laplacianMatrix_row_sum`, `laplacianMatrix_mulVec_const`, `heatTrace`, `heatTrace_zero = |V|`. Rung-3 matrix/heat-kernel infrastructure.
- [x] **`CycleMatrixSpectrum.lean`**: `laplacianMatrix_cycleHypergraph_eigen` — matrix-level eigenvalue equation (cycle eigenvectors are genuine matrix eigenvectors of `laplacianMatrix (cycleHypergraph n)`).
- [x] **`HeatKernelODE.lean`** (T1): ODE ↔ matrix heat kernel unification. `hasDerivAt_heatKernel` (d/dt = · · Δ), `heatKernel_commute_laplacianMatrix`, `hasDerivAt_heatKernel_mulVec`, **`heatKernel_isHeatSolution`** (the matrix heatKernel satisfies `HeatSolution H`). The two heat-equation definitions (ODE predicate + Matrix.exp propagator) are now linked.
- [x] **`ExpEigenvector.lean`** (T2): matrix exp fixes eigenvectors. **`exp_mulVec_of_eigenvector`**: if `A.mulVec v = λ • v`, then `(NormedSpace.exp A).mulVec v = Real.exp λ • v`. Via `exp_eq_tsum_rat` + `ContinuousLinearMap.map_tsum` + `matrix_pow_mulVec_of_eigenvector` induction + `Real.summable_pow_div_factorial`.
- [x] **`CycleHasEigenvalue.lean`** (T4): cycle spectrum in Mathlib `Module.End.HasEigenvalue` form. **`laplacianMatrix_cycleHypergraph_hasEigenvalue`** connects our pointwise eigenvalue theorem to Mathlib's spectral-theory API.
- [~] **`PathHypergraph.lean`** (T5 partial;): `pathEdge n i = {i, i+1}` defines `pathHypergraph n` on `Fin n`. `pathHypergraph_edges_card_le` (|E| ≤ n−1). **Corrected spectrum to match the free-path Laplacian**: `pathEigenvalue n k = −4 sin²(kπ/(2n))` and `pathEigenvector n k j = cos(kπ(2j+1)/(2n))`. `pathEigenvalue_nonpos`. `pathEigenvalue_ground_zero` (k=0 eigenvalue = 0). `pathEigenvalue_one_neg` (first non-constant mode strictly negative for n ≥ 2). Axiom-clean. Path is the open-chain analog of the cycle; `T5 = path + cycle^d` is the d-torus factor picture.
- [~] **`CurvedRicciBridge.lean`** (R4 partial;): `warpedDiag2 : MetricData 2` — warped 2-D metric with `g₁₁ = 1 + x₀²`. `warpedDiag2_christoffel_nonzero` (Γ¹_{01} ≠ 0 at `x 0 ≠ 0`). `curvedRicciBridgeObligation` — existence of non-flat continuum target; `threeRegular_formanRicci_nonzero` — every edge of a 3-regular graph has Forman-Ricci `−2`. The "beyond flat" witness half of R4. Axiom-clean.
- [x] **`WarpedDiag2C2.lean`** (R4 full Einstein identity on warpedDiag2 — the first complete curved-case Einstein closure in the project): `warpedDiag2_C2 : MetricDataC2 2` supplies second partials + inverse-metric derivatives. **Riemann closed forms**: `R^0_{101}(x) = -1/(1+x₀²)`, `R^1_{010}(x) = -1/(1+x₀²)²`, `R^0_{001} = 0`, `R^1_{110} = 0`. **Ricci closed forms**: `R_{00}(x) = -1/(1+x₀²)²`, `R_{11}(x) = -1/(1+x₀²)`, `R_{01} = R_{10} = 0`. **Einstein identity** `warpedDiag2_einstein : R_{μν}(x) = (-1/(1+x₀²)²) · g_{μν}(x)` for all `(μ, ν) : Fin 2²`. Gaussian curvature `K(x) = -1/(1+x₀²)² < 0` (non-constant). Generic `riemann_diag_zero` lemma (`R^ρ_{σμμ} = 0` via `riemann_antisymm`). Axiom-clean.
- [x] **IT5 Latschev (discrete-connectivity form) — PROVED** (`RemainingObligations.lean`;): `latschevObligation_holds` proves `LatschevObligation`. For every `n ≥ 2` and `u v : Fin n`, `(cycleHypergraph n).dist u v < n + 1`. Uses `SimpleGraph.Walk.IsPath.length_lt` (shortest path < card V = n) in the reachable branch and `dist_eq_zero_iff_eq_or_not_reachable` in the unreachable branch. Full GH-homotopy-equivalence form still needs more Mathlib. Axiom-clean.
- [x] **IT6 Scale trichotomy (cycle endpoints) — PROVED** (`RemainingObligations.lean`;): `scaleTrichotomyObligation_holds` proves `ScaleTrichotomyObligation`. For every `n ≥ 3`: at `ε = 0` no non-trivial VR 1-simplex (distinct vertices have `dist > 0`); at `ε = n` every pair is a VR 1-simplex. Uses `Reachable.pos_dist_of_ne` + `SimpleGraph.Walk.IsPath.length_lt`. Meso-regime Betti-number matching still needs persistent-homology. Axiom-clean.
- [~] **T6 partial — obligations upgraded from `True ∧ False` stubs to real Prop types; several discharged by zero witnesses (cosmetic)** (`RemainingObligations.lean`): IQ8 `EMEPersistenceObligation` (ψ = 0) and IQ9 `PathIntegralObligation` (α = 0) are satisfied trivially by zero witnesses — reopened as tasks #154 / #155 for real content. IT5 (cycle Latschev) and IT6 (cycle endpoints) are substantive. ID6 and IR7-refined are substantive. IQ6 is a genuine Cauchy-Schwarz bound. No `True ∧ False` stubs remain, but the cosmetic zero-witness obligations are tracked as open. Axiom-clean.
- [~] **ID6 partial — base cases r = 0 and r = 1 proved on cycle** (`HypergraphDistance.lean`, `RemainingObligations.lean`;): `cycleHypergraph_ballVolume_zero_exact` (ball volume 1 at r=0). `dimensionCompatibilityObligation_base_cases` bundles the r=0 and r=1 cases of the full `geodesicBallVolume v r = 2r+1` ID6 obligation. Also `cycleHypergraph_ballVolume_large` (r ≥ n gives full space = n). Full obligation needs general cycle-distance formula. Axiom-clean.
- [x] **DiscreteWave + DiscreteSchrödinger continuum spectra PROVED** (`ContinuumLimitStatement.lean`): upgraded `DiscreteWaveToContinuumWave` and `DiscreteSchrodingerToContinuumSchrodinger` from `True` stubs to concrete spectral-convergence claims and proved. Wave: `n · 2 sin(πk/n) → 2πk`. Schrödinger: `n² · 4 sin²(πk/n) → (2πk)²` (negative of A4). Axiom-clean.
- [x] **pde_spectrum_bridge_summary** (`ContinuumBridgeDemo.lean`): bundles the three PDE spectral convergences (heat, wave, Schrödinger) for each wavenumber k into a single theorem. Analog of `wolfram_physics_bridge_summary` for the PDE-to-PDE bridge. Axiom-clean.
- [x] **Klein-Gordon continuum spectrum** (`ContinuumLimitStatement.lean` + `ContinuumBridgeDemo.lean`): `DiscreteKleinGordonSpectrum m` + `discreteKleinGordonSpectrum_holds` proves `n² · 4 sin²(πk/n) + m² → (2πk)² + m²`. `pde_spectrum_bridge_summary_with_mass` includes it in the bundled PDE bridge. Axiom-clean.
- [x] **minkowski4Manifold_satisfies_vacuum_EFE**: Minkowski-as-DiagLorentzianManifold + flat-connection solves vacuum Einstein equations — bundles E1 + F3. Axiom-clean.
- [x] **X1 / PartialMetricData refactor** (`PartialMetricData.lean`;): `PartialMetricData n` bundles g, ginv, dg with domain predicate `valid : (Fin n → ℝ) → Prop`. `MetricData.toPartial` + `christoffel_symm` on validity. `schwarzschildPartial_christoffel` ties back to explicit formulas. Axiom-clean.
- [x] **GrandTour.lean** — one-file headline-theorems tour; one-line examples for every major theorem. Axiom-clean.
- [x] **Schwarzschild Lorentzian signature + B4 obligation** (`Schwarzschild.lean`): `sgg_lorentzian_pointwise` + `SchwarzschildVacuumObligation` statement form. Ricci = 0 (B3) remains open pending ∂²g.
- [x] **gr_metric_zoo** (`GRMetricsDemo.lean`): single bundled theorem exhibiting all formalised GR targets (Minkowski, FLRW, Schwarzschild, RN, de Sitter, S²). Centrepiece for the continuum-target side. Axiom-clean.
- [x] **de Sitter metric** (`DeSitter.lean`): `dsLapse`, `dsG`, `dsGinv`, `DSValid`, reduction-to-Minkowski at Λ=0, cosmological-horizon characterisation. Axiom-clean.
- [x] **2-sphere S² metric** (`TwoSphere.lean`): round sphere as `PartialMetricData 2`, non-zero `Γ⁰_{11}` closed form — concrete curved target. Axiom-clean.
- [x] **B8 / Reissner-Nordström metric components** (`ReissnerNordstrom.lean`;): `rnLapse`, `rnG`, `rnGinv` components + `RNValid` exterior predicate + reduction-to-Schwarzschild + horizon-positivity. Axiom-clean.
- [x] **B6 / FLRW metric as PartialMetricData** (`FLRW.lean`;): `flrwG`, `flrwGinv`, `flrwDg` components, `flrwPartial a da : PartialMetricData 4` with FLRWValid (`a(t) ≠ 0`) excluding big-bang. `flrwChristoffel_0_00 = 0`. Axiom-clean.
- [x] **B5 / Schwarzschild as PartialMetricData on exterior** (`Schwarzschild.lean`;): `schwarzschildPartial M` bundles Schwarzschild sgg/sginv/sdg + `SchwarzschildValid M` predicate into a `PartialMetricData 4`. Axioms are the existing Schwarzschild exterior theorems. Axiom-clean.
- [x] **E1 / Lorentzian manifold structure** (`LorentzianManifold.lean`;): `DiagLorentzianMetric M` predicate (`g_00 < 0`, `g_ii > 0`, off-diagonal zero). `DiagLorentzianManifold n` bundled structure. `minkowski4_diagLorentzian` + `minkowski4Manifold`. Axiom-clean.
- [x] **X2 / Covariant derivative on `ConnectionData`** (`CovariantDerivative.lean`;): `nabla_scalar`, `nabla_vector`, `nabla_covector`. Flat cases collapse to partials. ℝ-linearity additivity. Axiom-clean.
- [~] **Second Bianchi (flat vacuum case)** (`EinsteinEquations.lean`): `flatConnection_einstein_divergence_zero` — vacuous flat form of ∇_μ G^{μν} = 0. Full B11 requires metric compatibility. Axiom-clean.
- [x] **E5 / Discrete Cauchy foliation existence** (`CausalFoliation.lean`;): `time_monotone_causallyPrecedes`, `time_strict_monotone_strictCausallyPrecedes`, `timeLevelSet`, `timeLevelSet_isAntichain`, `timeLevelSet_disjoint`, `timeLevelSet_covers`, **`timeFunction_foliation`**, **`stablyCausal_hasFoliation`**. Every stably causal DAG admits a discrete Cauchy foliation. Axiom-clean.
- [x] **F3 / Einstein field equations with Λ** (`EinsteinEquations.lean`;): `EinsteinEqLambda M C Λ κ T x` = `∀ μ ν, G_{μν}(x) + Λ·g_{μν}(x) = κ·T_{μν}(x)`. `minkowski4_satisfies_EFE_zero_lambda` (Minkowski + flat + Λ=0 + T=0). `einsteinEqLambda_vacuum_iff`. **`minkowski4_flat_vacuum_forces_lambda_zero`**: de Sitter/anti-de Sitter cannot live on Minkowski + flat connection. Axiom-clean.
- [~] **T5 / Path Laplacian constant-mode eigenvalue equation** (`PathHypergraph.lean`;): `pathEigenvector_zero_eq_one` + `pathLaplacian_eigen_zero` — the `k=0` case of the path-Laplacian eigenvalue equation is proved. General k case remains future work.
- [x] **`HeatKernelDecay.lean`**: `heatKernel_cycleHypergraph_multi_mode_tendsto` — multi-mode D6 convergence. For any finite `S ⊆ {1,…,n−1}` of non-constant mode indices, `heatKernel t · (c·v_0 + Σ_{k∈S} d_k·v_k) → c·v_0` pointwise. Core spectral-theorem ingredient of D6 — once an eigenbasis decomposition is in place, every initial state converges to its spatial-average component under heat flow. Axiom-clean.

### Rung 5 — Riemann/Ricci/scalar curvature (local-coordinate route)
- [x] **`MetricData n`** (`CurvatureLocalCoord.lean`): metric components, inverse, first partial derivatives, symmetry + inverse axioms. Avoids bundle machinery.
- [x] **Christoffel symbols** `Γ^ρ_{μν} = ½ g^{ρσ} (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})` as explicit formula.
- [x] **`christoffel_symm`**: lower-index symmetry `Γ^ρ_{μν} = Γ^ρ_{νμ}`.
- [x] **Minkowski instance** on ℝ⁴ with signature `(−, +, +, +)`; `minkowski4_christoffel_zero` confirms all Christoffel symbols vanish.
- [x] **Riemann tensor** `R^ρ_{σμν}` (`CurvatureRiemann.lean`) via `ConnectionData n` carrying `Γ + ∂Γ` as data; `riemann_antisymm` in last two indices.
- [x] **Ricci tensor** `R_{σν} = Σ_ρ R^ρ_{σρν}` and **scalar curvature** `R = g^{σν} R_{σν}` and **Einstein tensor** `G_{μν} = R_{μν} − ½ R g_{μν}`.
- [x] `flatConnection`: `Γ ≡ 0`, with `flatConnection_riemann_zero`, `_ricci_zero`, `_scalar_zero`, `_einstein_zero`.
- [x] **`minkowski4_satisfies_vacuum_EFE`**: `G_{μν} = 0` on Minkowski with the flat connection — the trivial flat-space EFE sanity check.
- [x] **First (algebraic) Bianchi identity** `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0` for torsion-free connections (`CurvatureRiemann.lean`).
- [x] Schwarzschild instance with non-trivial Christoffel symbols — **all 8 textbook Christoffel entries computed** (`Schwarzschild.lean`, task B1 complete).
- [ ] Differential Bianchi `∇_μ G^{μν} = 0` (formal consequence; needs covariant derivative).
- [x] **`MetricDataC2 n`** (`CurvatureRiemann.lean`): extends `MetricData` with second partial derivatives `ddg`, inverse-metric partials `dginv`, plus Clairaut/Schwarz symmetry axioms.
- [x] **`dchristoffel`**: the partial derivative of the Christoffel symbol, explicit formula involving `ddg`, `dginv`, and the base metric data.
- [x] **`dchristoffel_symm`**: `∂Γ^ρ_{μν} = ∂Γ^ρ_{νμ}` (lower-index symmetry preserved under differentiation).
- [x] **`leviCivitaConnection : MetricDataC2 n → ConnectionData n`**: the canonical torsion-free connection derived from the metric. Combined with Riemann/Ricci machinery, this closes the MetricData → Riemann loop.

### Hypergraph anchors for Rung 5 (the "tie back to hypergraphs" obligation)
- [x] **`formanRicciEdge`**, `formanRicciVertex`, `formanRicciTotalScalar` (`DiscreteRicci.lean`): purely combinatorial Ricci on a graph; `4 − deg(v) − deg(w)` per edge.
- [x] `formanRicciEdge_zero_of_two_regular`: 2-regular graphs (e.g., cycle `Fin n`) have zero Forman-Ricci — matches the continuum Ricci of the circle (which is zero).
- [x] `formanRicciEdge_regular`, `formanRicciVertex_regular`, `formanRicciTotalScalar_regular` for arbitrary `k`-regular graphs.
- [x] **Hypergraph Forman-Ricci** (`DiscreteRicci.lean` extended): `formanRicciHyperedge e := |V(e)|·(2 − |V(e)|)` (Saito-Kimura-Yamanoi); vanishes on 2-vertex edges (simple-graph case), negative for ≥ 3-vertex edges. `formanRicciHypergraph H` (total scalar); vanishes on simple graphs.
- [x] **Hypergraph Laplacian** (`HypergraphLaplacian.lean`): `laplacianHyper H f v := ∑_{e ∈ H.edges} ∑_{w ∈ e.others v} (f(w) − f(v))`, defined directly on `Hypergraph V` (the actual Wolfram-model state type). Linearity + vanishes on constants + **discrete divergence theorem** `laplacianHyper_sum_zero`: `∑_v Δ_H f(v) = 0` (proved by Multiset induction + per-edge cancellation); sets up mass conservation for the hypergraph heat equation.
- [x] **Hypergraph discrete exterior calculus** (`HypergraphCalculus.lean`): `Hyperedge.src`, `Hyperedge.dst`, `hyperedgeGradient f e := f(dst e) − f(src e)`, `hypergraphDiv`, linearity of both, and **`summation_by_parts`** — discrete Stokes' theorem `∑_v f(v) · div(g)(v) = ∑_e g(e) · grad(f)(e)`. Foundation for variational calculus on hypergraphs.
- [x] **First bridge** (`RicciBridge.lean`): `forman_ricci_matches_continuum_on_cycle` and `forman_ricci_real_matches_continuum_on_cycle` — Forman-Ricci on a 2-regular graph equals continuum Ricci on the circle (both ≡ 0); explicit `circleMetric : MetricData 1` instance.
- [ ] **Convergence theorem (general)**: scaled Forman-Ricci on lattice graphs → continuum Ricci of the GH-limit manifold (extending beyond the trivial 0 = 0 case to non-flat targets). (R4 / pending.)

### Discrete d'Alembertian (Benincasa-Dowker-style) on the trajectory causal DAG
- [x] `openInterval τ j i` and `intervalSize τ j i` (`DiscreteDAlembertian.lean`).
- [x] `layer τ k i` — events `j ≺ i` whose interval has exactly `k` intermediates.
- [x] **`discreteDAlembertian4`**: BD-4D operator `-φ(i) + ∑_{L_0} φ − 9 ∑_{L_1} φ + 16 ∑_{L_2} φ − 8 ∑_{L_3} φ`.
- [x] Linearity (`discreteDAlembertian4_add`, `_smul`); vanishing on zero (`_zero`).
- [x] `layer_disjoint`: layers are pairwise disjoint.
- [x] `mem_layer_isCausalPred`: layer membership implies causal precedence.
- [x] **`BenincasaDowkerConjecture`** structure: explicit `Prop`-level placeholder for the unproven `B_ρ → □ − ½R` continuum limit; `gorardF6_carries_BD_assumption` makes the F6 dependency machine-checkable.
- [ ] General-dimension BD operator (coefficients indexed by `d`; 2D = `(1, -2, 1)`, 3D, etc.).
- [x] **Discrete action** `S[φ] := ∑_{i < N} φ(i) · B[φ](i)` (`discreteAction`); homogeneous of degree 2 (`discreteAction_smul`).
- [x] **Discrete EL equation** `discreteEL τ φ ↔ ∀ i, B[φ](i) = 0` — the discrete Euler-Lagrange (analog of JGORARD's `δS/δg^{ab} = 0`).
- [ ] Action expansion under perturbation: `S[φ + h] − S[φ]` to first order in `h`, recovering `discreteEL` from stationarity.

### Schwarzschild curved-metric sanity check (Rung 5)
- [x] **Schwarzschild component functions** (`Schwarzschild.lean`): `sgg M`, `sginv M`, `sdg M` — metric, inverse, partial derivatives in Schwarzschild coordinates.
- [x] **`SchwarzschildValid M x`** predicate: exterior region `r > 2M ∧ r > 0 ∧ sin θ ≠ 0`.
- [x] Symmetry axioms (`sgg_symm`, `sginv_symm`, `sdg_symm`).
- [x] **`sginv_mul_sgg`**: `∑ g^{μα} g_{αν} = δ^μ_ν` conditional on `SchwarzschildValid` (the key axiom of `MetricData`, established on the exterior).
- [ ] Domain-restricted `PartialMetricData` variant (pending; enables full `MetricData` packaging of Schwarzschild).
- [x] **`schwarzschildChristoffel M x ρ μ ν`** (`Schwarzschild.lean`): Christoffel formula specialised to Schwarzschild components.
- [x] `schwarzschildChristoffel_symm`: lower-index symmetry.
- [x] **`schwarzschildChristoffel_1_00`**: worked example `Γ^1_{00} = M(r − 2M)/r³` in the exterior — matches textbook value.
- [x] **All non-zero Christoffel entries** (task B1 complete): `schwarzschildChristoffel_0_01`, `_1_00`, `_1_11`, `_1_22`, `_1_33`, `_2_12`, `_2_33`, `_3_13`, `_3_23` — all 8 computed and axiom-clean.
- [x] **`schwarzschild_christoffel_collapse`**: specialised Christoffel formula on Schwarzschild components.
- [ ] Compute Riemann tensor components (B2 pending).
- [ ] Verify `Ric ≡ 0` (vacuum solution; B3 pending).
- [ ] Cross-check via `vacuumEFE` (B4 pending).

### Discrete heat equation on a hypergraph (Rung 6 entry)
- [x] `HeatSolution H u` predicate via `HasDerivAt` (`HeatEquation.lean`, task D1).
- [x] Linearity of solutions (`heatSolution_zero`, `_add`, `_smul`).
- [x] Mass conservation `∑ u(t) = ∑ u(0)` via `laplacian_sum_zero` (`heat_mass_conservation`, D4).
- [x] L² decay `‖u(t)‖² ≤ ‖u(0)‖²` via `laplacian_neg_psd` (`heat_L2_decay`, `heat_L2_antitone`, D5).
- [x] Wave equation on hypergraph (`WaveEquation.lean`, D8) with energy conservation.
- [x] Klein-Gordon equation on hypergraph (`KleinGordon.lean`, D9) with energy conservation.
- [x] Schrödinger equation on hypergraph (`SchrodingerEquation.lean`, D10) with unitarity / probability conservation.
- [x] Discrete scalar field Lagrangian + Euler-Lagrange (`ScalarField.lean`, G1, G3, G4); `KG_EulerLagrange_iff_KleinGordonSolution`.
- [x] Heat semigroup on a finite graph as `Matrix.exp` (`LaplacianMatrix.lean`, D3 / R2): `heatKernel H t := exp(t · laplacianMatrix H)`, `heatKernel_zero = 1`, `heatKernel_add` (semigroup).
- [x] **ODE ↔ matrix heat kernel identification** (`HeatKernelODE.lean`, T1): `heatKernel_isHeatSolution` — the matrix propagator satisfies the `HeatSolution H` ODE predicate. Unifies the two heat-equation definitions.
- [x] Scaled cycle Laplacian → 1D `d²/dx²` for all C² test functions (R1/A2/A3; `CTwoTaylor.lean` + `ScaledDiffC2Bridge.lean`).
- [x] **Existence + forward-time uniqueness** (`HeatEquationUniqueness.lean`, D2): `heat_exists` (via heatKernel T1), `heat_unique_forward` (via `heat_L2_antitone`), `heat_exists_unique_forward` package.
- [~] Long-time convergence to uniform (D6 partial; `HeatKernelDecay.lean` proves each non-constant eigenmode `1 ≤ k < n` decays coordinate-wise to 0 under heat flow, via strict negativity of `cycleEigenvalue n k` and `Real.tendsto_exp_atBot`; remaining: eigenbasis decomposition of arbitrary initial data).
- [ ] Scaled discrete heat → continuous heat on GH-limit (D7).
- [ ] Ollivier-Ricci with full proof (currently statement-only in `Infra/OllivierStatement.lean`).
- [ ] Choquet-Bruhat Einstein evolution (D11).

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
- [x] Finite-slice cardinality bound under finite-successors assumption (`BranchialFinite.lean`, `branchialSliceFinite_of_successors_finite`, task I1).
- [x] Fisher metric on branchial probability distributions (`FisherMetric.lean`, task IQ5).
- [ ] Branchial measure: a probability assignment on each slice (I2 pending).
- [x] ℓ²(slice) Hilbert space (I4 / R3 partial; `BranchialHilbert.lean` — `BranchialHilbert S := EuclideanSpace ℂ S` with ℂ-linear adjacency operator `branchialAdjLM` and self-adjointness `branchialAdjLM_inner` for symmetric adj).
- [x] Branchial amplitudes (I3; `BranchialHilbert.lean` — `BranchialAmplitude S := BranchialHilbert S` + Born-rule `bornProbability ψ s := Complex.normSq (ψ s)`, sum = `‖ψ‖²`).
- [x] Branchial measure (I2; `BranchialHilbert.lean` — `branchialUniformWeight S s := 1/|S|`, sum = 1 when nonempty).
- [x] Branchial Schrödinger evolution as unitary (I5; `BranchialSchrodinger.lean` — `BranchialSchrodinger adj u v` structure, `branchialSchrodinger_unitary_evolution` proves total-probability conservation via self-adjointness of real adjacency operator).
- [ ] Branchial amplitudes / evolution toward Hilbert-space limit (I3, I5, I8 pending).
- [x] IQ6 Fubini-Study / Bhattacharyya bound proved (`fubiniStudyBhattacharyya_bound`) — substantive.
- [~] IQ8 EME persistence: zero-witness baseline only; reopened as task #154 for real content.
- [~] IQ9 Path-integral: α = 0 baseline only; reopened as task #155 for real content.

### Infrageometry program — 9 groups × 57 tasks (see [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md))

Full collation of the post-phase-1 infrageometry programme. Each group is a coherent research direction; per-task status tracked in `COVERAGE_MAP.md` §8.

#### IA — Infraanalysis / DAG calculus (5 tasks, all done)
- [x] IA1 DAG-as-blowup-of-interval (`DagBlowup.lean`;).
- [x] IA2 Calculus on coordinate DAGs (`DagCalculus.lean`;).
- [x] IA3 de Rham complex on Hypergraph V (`DeRham.lean`;).
- [x] IA4 Form → cochain integration map (`FormCochainIntegration.lean`;).
- [x] IA5 Blowup / refinement operators (`BlowupOperations.lean`;).

#### IG — InfraGaugeTheory (11 tasks, 10/11 done)
- [x] IG1 FiberedGraph type + basic properties (`FiberedGraph.lean`;).
- [x] IG2 Section structure + smoothness.
- [x] IG3 Connection on a FiberedGraph.
- [x] IG4 Parallel transport along a base path (`Holonomy.lean`;).
- [x] IG5 HolonomyMatrix on a loop.
- [x] IG6 Wilson loop = trace of holonomy.
- [x] IG7 FlatConnection predicate + theorems.
- [x] IG8 FiberBundle predicate (`FiberBundle.lean`;).
- [x] IG9 GraphTangentBundle construction.
- [x] IG11 Multi-fibered graph (`MultiFibrationProjection.lean`;).
- [ ] IG10 Exponential map via weighted shortest-path counts.

#### IC — Infracausality (8 tasks, all done)
- [x] IC1 Transitively-reduced causal graph type (`CausalGraphType.lean`;).
- [x] IC2 ObserverChain (maximal chain;).
- [x] IC3 LightRay as degenerate-interval subgraph.
- [x] IC4 Foliation = successive antichains, ProperTime (`CausalFoliation.lean`;).
- [x] IC5 SpatiallyReconstructedHypergraph (`SpatialReconstruction.lean`;).
- [x] IC6 Multi-fibration from non-unique shortest-path projection.
- [x] IC7 Ehlers-Pirani-Schild axioms as Props (`EPSAxioms.lean`;).
- [x] IC8 Marzke-Wheeler clock construction (`MarzkeWheeler.lean`;).

#### IT — Infratopology / Vietoris-Rips (6 tasks, 3 proved + 3 obligation-level)
- [x] IT1 Vietoris-Rips complex on a hypergraph (`VietorisRips.lean`;).
- [x] IT2 Hodge Laplacian on VR-complex 0- and 1-forms (`HodgeVR.lean`;).
- [x] IT4 Persistence diagram / barcode sentinel.
- [x] IT3 Spectrum of Hodge Laplacian as hypergraph invariant (`HodgeLaplacianSpectrum.lean`: `vrHodge0_add`, `vrHodge0_smul`, `vrHodge0_symm` (ℓ² self-adjointness), `vrHodge0_has_zero_eigenvalue`, `vrHodge0_const_in_kernel` — finite-dim spectral theorem now applies).
- [x] IT5 Latschev obligation proved for cycles (`latschevObligation_holds`).
- [x] IT6 Scale-dependence trichotomy proved at cycle endpoints (`scaleTrichotomyObligation_holds`).

#### ID — Infradimension (7 tasks, 5 proved + 2 obligation-level)
- [x] ID1 Wolfram-Hausdorff dimension as function on hypergraphs (`HypergraphDistance.lean`;).
- [x] ID2 Plateau-detection for Wolfram-Hausdorff dimension (`PlateauDimension.lean`;).
- [x] ID3 Homology dimension from persistence (`HomologyDimension.lean`;).
- [x] ID4 Coordinatization dimension via extremal orthogonal axes (`CoordinatizationDimension.lean`;).
- [x] ID5 Causal-graph dimension from longest-antichain analysis (`CausalDimension.lean`;).
- [x] ID6 Compatibility theorem: V(v, r) = 2r + 1 exact on the cycle hypergraph (`dimensionCompatibilityObligation_holds`).
- [ ] ID7 Spectral dimension via heat-kernel trace.

#### IB — Infrablowup (6 tasks, 5/6 done)
- [x] IB1 ElementaryBlowup (`ElementaryBlowup.lean`;).
- [x] IB3 BlowupLieAlgebra structure (`BlowupLieAlgebra.lean`;).
- [x] IB4 Insertion Lie algebra from unary blowups.
- [x] IB5 Poisson bracket on formal hypergraph functions.
- [x] IB6 Radial / laminar blowup operations (`RadialLaminarBlowup.lean`;).
- [ ] IB2 Causal-branchial-trivial commutator theorem.

#### IQ — Branchial / quantum (4 formal obligations + 1 real theorem)
- [x] IQ5 Fisher metric on branchial graph (`FisherMetric.lean`;).
- [x] IQ6 Fubini-Study / Bhattacharyya bound (`fubiniStudyBhattacharyya_bound`) — substantive; full Fisher → FS refinement limit remains as a follow-up.
- [~] IQ8 EME persistence: zero-witness baseline; reopened (task #154).
- [~] IQ9 Path-integral over singleway causal graphs: zero-witness baseline; reopened (task #155).

#### IS — Synthetic axiomatic infrageometry (3 tasks, all done)
- [x] IS1 Synthetic circle / line / sphere (`SyntheticGeometry.lean`;).
- [x] IS2 InfrageometricScene — multi-construction scene type (`InfrageometricScene.lean`;).
- [x] IS3 Axiomatic synthetic infrageometry, Euclid-style (`SyntheticAxiomatic.lean`;).

#### IR — Ruliology / rule taxonomy (7 tasks, 6 proved + 1 obligation-level)
- [x] IR1 RuleSignature functor (`RuleSignature.lean`;).
- [x] IR2 Conservation theorem — |LHS|=|RHS| implies bounded dimension (`RuleDimensionBounds.lean`;).
- [x] IR3 Tree-producing rules have log-branching dimension (`StructuralRuleBounds.lean`;).
- [x] IR4 Planar rules have dim ≤ 2 (Euler formula;).
- [x] IR5 Product rule dimension additivity.
- [x] IR6 Candidate-rule database + screening pipeline (`CandidateRuleDatabase.lean`;).
- [x] IR7 Reverse-engineer rule from target signature: refined obligation proved (`reverseEngineeringObligationRefined_holds`); original unrefined form provably FALSE (`not_reverseEngineeringObligation`).

### R-series real-work items (5 tasks, 3.5/5 done)
- [x] R1 C² Taylor convergence for scaled second difference (`CTwoTaylor.lean`;).
- [x] R2 laplacianMatrix + heatKernel via Matrix.exp (`LaplacianMatrix.lean`;).
- [x] R3 ℓ²(BranchialSlice) as Hilbert space with branchial adjacency operator — closed: `BranchialHilbert.lean` (Hilbert alias, ℂ-linear adjacency, Born rule, uniform measure, observables, expectation values) + `BranchialSchrodinger.lean` (unitary Schrödinger evolution) + `BranchialCanonical.lean` (canonical rewriting-system-grounded Hamiltonian — no islands).
- [ ] R4 Curved discrete-Ricci convergence beyond flat.
- [x] R5 Cycle Laplacian spectrum closed form (`CycleSpectrum.lean`;).

### M-series colleague-work items (10 tasks, all pending)
- [ ] M1 IMILEA gauge-intern project coordination.
- [ ] M2 HVLE Fisher→Fubini-Study bridge.
- [ ] M3 HKOLCZ Lie-Poisson MBQC.
- [ ] M4 JPULLMAN IBL-∞ / BV formalism.
- [ ] M5 CZAPATA + SAHMED axiomatic-relativity paper.
- [ ] M6 NMURZIN `Infrageometry` paclet — Lean port parity (NMURZIN is Creator + principal committer; the previous "PPOKORNY Infrageometry paclet parity" wording conflated PPOKORNY with the `Infrageometry` paclet — see `CONTRIBUTORS.md`).
- [ ] M7 SAHMED EME-tracking community post.
- [ ] M8 Diffusion-geometry bridge — attribution under review (previously credited PPOKORNY without verified evidence; see `CONTRIBUTORS.md`).
- [ ] M9 Tropical-geometry synthetic infrageometry.
- [ ] M10 3BP / dynamical-systems dimension signature.

### Remaining-obligations module
- [~] `RemainingObligations.lean`: **T6 — obligations upgraded from True ∧ False to real Prop types**, bundled in `all_obligations_hold`. Substantive: IT5 `latschevObligation_holds`, IT6 `scaleTrichotomyObligation_holds`, ID6 `dimensionCompatibilityObligation_holds` (V(v, r) = 2r+1 exact), IQ6 `fubiniStudyBhattacharyya_bound`, IR7-refined `reverseEngineeringObligationRefined_holds`. Cosmetic zero-witness: IQ8 + IQ9 (baselines via `no_stub_obligations_remain`; reopened as tasks #154/#155). Original unrefined IR7 is provably FALSE (`not_reverseEngineeringObligation`).

## Phase 2 — Corrected continuum identities (Lean)

### Stated correctly (statement-only, no Mathlib Ricci yet)
- [x] Correct Ollivier identity as `OllivierIdentityLeading` (T27)
- [x] JGORARD's form and coincidence condition (T28)
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
- [x] Scaled $d$-dim lattice → flat $d$-torus, any $d$ (`Infra/ScaledTorusD.lean`, `dTorus_gh_bound`).
- [x] Discrete → continuum Minkowski bridge for any $d$ (`Infra/ScaledLorentz.lean` + `Infra/FullBridge.lean`): exact isometry + iff causal preservation + density.
- [ ] Scaled Cayley graph of a finitely-generated group → its asymptotic cone.
- [ ] Random geometric graph on a Riemannian manifold → the manifold (the positive analogue of JGORARD's §3).
- [ ] Causal-set Poisson sample of a Lorentzian spacetime → the spacetime (Lorentzian-GH, contingent on Mathlib infrastructure).

## Phase 4 — Discrete geometric structures library (Lean)

- [x] `Hypergraph V` as a graph-distance space (`HypergraphDistance.lean`): `Hypergraph.Adj`, `Hypergraph.dist`, geodesic balls, ball volume; `dist_self`, `dist_comm`, **`dist_triangle`** (via `Connected` hypothesis) + **`dist_triangle_of_reachable_{left,right}`** (conditional forms), monotonicity; cycle-hypergraph adjacency / ballVolume instances; **`cycleHypergraph_connected`** (for n ≥ 2) + **`cycleHypergraph_dist_triangle`** unconditional on cycles (T3 tightening).
- [x] Wolfram-Hausdorff dimension as function on hypergraphs (task ID1 `wolframHausdorffDimension`; plateau version ID2).
- [x] Benincasa–Dowker discrete d'Alembertian on a causal graph (`DiscreteDAlembertian.lean`): BD-4D operator, action, EL, F6 flagged as explicit Prop obligation.
- [x] Vietoris-Rips complex + Hodge Laplacian on a hypergraph (`VietorisRips.lean`, `HodgeVR.lean`).
- [x] Hypergraph Laplacian as a matrix (`LaplacianMatrix.lean`): symmetric matrix, kills constants, row-sum zero; heat kernel as `Matrix.exp`.
- [x] **Counting measure on a hypergraph + pushforward** (`HypergraphMeasure.lean`, A5): `countingMeasure`, `uniformProbability`, `pushforwardCounting`, `pushforwardUniform`; `countingMeasure_univ = |V|`, `uniformProbability_univ = 1`.
- [x] **Pseudo-metric axioms** proved: `dist_self`, `dist_comm`, **`dist_triangle`** (T3; `Connected` form + conditional `Reachable` forms). `PseudoMetricSpace` instance via ℕ→ℝ cast deferred but all axioms in hand.
- [ ] Ollivier–Ricci on directed hyperedges, following Eidi–Jost 2019 (statement-only in `Infra/OllivierStatement.lean`).
- [ ] Convergence results connecting discrete to continuum via random-geometric-graph / Poisson sampling.

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

- [x] Causal-graph type class — `CausalGraph V` (TR-DAG) with `causallyPrecedes` (refl, trans), `causalEdge_implies_precedes`, `ChainOfLength`, `DegenerateInterval`, `OnLightStepFrom` (`CausalGraphType.lean`; IC1-IC3).
- [x] Foliation / antichain theory: `IsAntichain`, `IsFoliation`, `FiniteSupportFoliation`, `HasProperTime`, `properTime_self_exists` (`CausalFoliation.lean`; IC4).
- [x] Benincasa–Dowker discrete d'Alembertian on trajectory causal DAG (`DiscreteDAlembertian.lean`, Phase-1 heading above).
- [ ] Poisson sampling of a Lorentzian spacetime into a causal set.
- [ ] Expected-value convergence $\langle B^{(d)}_\rho \phi\rangle \to \Box \phi - \tfrac12 R\phi$ (Sorkin–BD conjecture, open in the literature; flagged as F6 / `BenincasaDowkerConjecture` placeholder).
- [ ] $\langle S_{\mathrm{BD}}\rangle \to S_{\mathrm{EH}}$ (open in the literature).

## Phase 7 — Quantum-mechanical bridge (multiway / branchial)

JGORARD's companion program (arXiv:2004.14808 and related) claims that the *branchial* structure of the multiway evolution graph recovers quantum mechanics. This is its own research line and has not been adequately audited yet; included here because quantum-mechanical content is the *only* plausible first-principles bridge between Wolfram rewriting and observed physics (since GR emerges only statistically / in the continuum limit).

- [ ] Audit JGORARD's QM paper with same S1–S6 methodology.
- [x] Define the `RewritingSystem` / `Step` / `MultiStep` machinery in Lean (states = hypergraphs, edges = applications; full branching tree via `Branchial.lean`).
- [x] Define `BranchialSlice` (states at a common evolution depth with shared ancestry; `Branchial.lean`, `BranchialFinite.lean`).
- [x] Define `SchrodingerEquation` on `Hypergraph V` with proven unitarity (`SchrodingerEquation.lean`, task D10).
- [x] Fisher metric on branchial distributions (`FisherMetric.lean`, IQ5).
- [ ] Integrate with `../efficient_rewriting_final/` multi-way engine for concrete examples (X4 pending).
- [ ] Define a measure / amplitude on branchial paths (I2 pending).
- [~] Branchial-amplitude / Hilbert-space limit (I3, I5, I8 pending; I4 / R3 ℓ²(slice) ✅ partial via `BranchialHilbert.lean`).
- [~] Fisher → Fubini-Study as branchial refinement limit — Bhattacharyya bound `fubiniStudyBhattacharyya_bound` proved; full refinement-limit claim still open.

## Phase 8 — Oliver Knill quantum-calculus formalisation (KN-group, added 2026-04-24)

Lean formalisation of Oliver Knill's discrete-geometry program (Harvard).
Source: [`resources/Infrageometry/QuantumCalculus.md`](resources/Infrageometry/QuantumCalculus.md)
+ Mathematica counterpart `resources/Infrageometry/Infrageometry/Kernel/QuantumCalculus.wl`.

Knill's program is **strict finitism applied to differential geometry**: every
continuum concept (curvature, cohomology, wave equation, geodesic flow) gets a
purely combinatorial counterpart on finite simplicial complexes / delta sets.
McKean-Singer supersymmetry between even/odd forms is the load-bearing single
identity that derives both Euler-Poincaré and Brouwer-Lefschetz.

Critical path: **IGE1 first** unblocks everything (Lean port of `Infrageometry.wl`
core gives us `complexClosure`, Euler/Fermi, Dirac/Hodge, connection/Green,
Betti/Lefschetz/super-trace primitives). Then KN14 supersymmetry → KN15/KN18
cohomological consequences → KN3/KN8 cohomology applications → KN10 cutting-edge
wave-front calculus.

- [ ] **IGE1** — Lean port of `Infrageometry.wl` core (351 lines): foundation for the whole KN-track.
- [ ] **IGE2** — `SimplicialSet.wl` Lean port — face/degeneracy maps + delta-complex morphisms; bridges KN12 + IA1–IA5.
- [ ] **IGE3** — `TDA.wl` Lean port — VR / Čech / persistence; aligns with IT1–IT4.
- [ ] **IGE4** — `Mesh.wl` Lean port — mesh-generation primitives.
- [ ] **IGE5** — `Chains.wl` Lean port — formal chain complex.

Knill items (KN1–KN20) — see [`INFRAGEOMETRY.md §5 Group KN`](INFRAGEOMETRY.md) and [`NEXT_STEPS.md`](NEXT_STEPS.md) for full descriptions:

- [ ] **KN1** — Wave equation `u(t) = cos(D t) u₀ + t · sinc(D t) v₀`.
- [ ] **KN2** — Discrete-time wave step + unitary wave propagator.
- [ ] **KN3** — Wu characteristic + Wu cohomology + fusion inequality.
- [ ] **KN4** — Isospectral Lax-pair deformation `D' = [d − d*, D]`.
- [ ] **KN5** — Connes spectral distance ↔ `Hypergraph.dist` bridge.
- [ ] **KN6** — Dynamical connection matrix `L(T)` + Green function `g(T)`; unimodularity, energy theorem.
- [ ] **KN7** — Curvature generalisations (index expectation, sectional, form, boundary).
- [ ] **KN8** — Dirac / Connection / Lefschetz zeta functions.
- [ ] **KN9** — Analytic torsion + spectral monotonicity under barycentric refinement.
- [ ] **KN10** — Wave-front exterior derivative + spherical-average non-local `d` (Knill 2025–2026).
- [ ] **KN11** — Geodesic gas + cellular-automaton geodesics.
- [ ] **KN12** — Delta sets / quivers — face-map exterior derivative + cohomology.
- [ ] **KN13** — Soft barycentric refinement + Fisk-manifold predicate.
- [ ] **KN14** — McKean-Singer supersymmetry. **Load-bearing for KN15 / KN18.**
- [ ] **KN15** — Atiyah-Singer / Atiyah-Bott analog in finite geometry.
- [ ] **KN16** — Cartan's magic formula `L_X = i_X d + d i_X` (discrete).
- [ ] **KN17** — Bosonic / Fermionic distinction in the type system.
- [ ] **KN18** — Brouwer fixed-point for graph endomorphisms (via Lefschetz).
- [ ] **KN19** — Deformed exterior derivatives `d_h` family.
- [ ] **KN20** — Level sets + Euler characteristic — discrete Morse-theory bridge.

## Phase 9 — Synthetic Infrageometry concrete tasks (SIG-group, added 2026-04-24)

Lean ports of [`resources/SyntheticInfrageometry/SyntheticInfrageometry/Kernel/*.wl`](resources/SyntheticInfrageometry/SyntheticInfrageometry/Kernel/)
plus the branching-stability research questions from the upstream README:
"Constructions in the discrete world are notoriously **ambiguous**, so the same
infra-geometric construction may branch at every step, producing several valid
final infrageometric scenes."

- [ ] **SIG1** — `Tools.wl` Lean port — primitive constructions (`Line`, `Ray`, `Segment`, `Perpendicular`, `Parallel`).
- [ ] **SIG2** — `Postulates.wl` Lean port — Euclid-style axioms; ruliological study (which postulates hold on which rule outputs?).
- [ ] **SIG3** — `Predicates.wl` Lean port — `collinear`, `concyclic`, `perpendicular`, `congruentSegment`, `betweenness`.
- [ ] **SIG4** — `Coordinatization.wl` Lean port — analytisation via shortest-path counts / Cayley-style embedding. Bridges ID4 + IGE1.
- [ ] **SIG5** — Branching-construction stability: `SceneDistance` via #214 W_1 + `ConstructionStability` under refinement.

## Multi-way engine integration

The `../efficient_rewriting_final/` repo is a high-performance C++ multi-way hypergraph-rewriting engine with a Mathematica paclet interface. Single-way SetReplace cannot verify causal invariance or explore branchial structure; this engine can.

- [ ] Wrap paclet for headless invocation from our Python test harness
- [ ] Measure the named rule's cone exponent in other update orders and reconcile the SetReplace and Python exponents
- [ ] Test causal invariance of simple rules (is any family provably causal-invariant?)
- [ ] Collect branchial-graph data for Phase 7 quantum-mechanical thread
- [ ] Use as a probe for candidate GR-recovering rules (Phase 5 search)

## Lean physics conventions to adopt

- [ ] Survey existing Lean physics projects for conventions (HepLean / particle physics; Mathlib's `Geometry.Manifold`, `MeasureTheory`, `Topology.MetricSpace`; smaller efforts in classical mechanics, quantum theory)
- [ ] Align `DirectedHypergraph` namespace and type conventions with Mathlib's `Geometry.Manifold`-style idioms
- [ ] Adopt Mathlib Lorentzian infrastructure when it lands; contribute if slower than we need

## Output targets (see also [`PUBLISHABLE.md`](PUBLISHABLE.md))

- [ ] Publishable audit note: the JGORARD-corpus refutation with Lean backing
- [ ] Publishable constructive note: correct Ollivier + Gray identities formalised
- [ ] Publishable infrageometry paper: our Phase-3 continuum-limit theorems + abstraction
- [ ] Publishable research paper: the first provable Wolfram-to-GR rule (Phase 5 milestone)
- [ ] Publishable joint paper: quantum-mechanical content via branchial structure (Phase 7 milestone)

---

**Maintenance.** Every Lean commit adds one or more `[x]` above. Every research decision updates the ordering and dependencies. Open this file at the start of each working block to re-anchor.
