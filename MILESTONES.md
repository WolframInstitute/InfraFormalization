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
- [x] State-size invariant across a parallel schedule (`trajectory_preserves_size` / `trajectory_size_invariant`, `ParallelSchedule.lean` + `RuleDimensionBounds.lean`)
- [ ] Layer-cardinality bound `|layer_s| ≤ N/k` (the full parallel-layer bound, a.k.a. Theorem B)
- [x] Bounded-ball-volume under conservative trajectory (`trajectory_conservative_ballVolume_bounded`, `RuleDimensionBounds.lean` / IR2)
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
- [x] **`CTwoTaylor.lean`** (R1 / A2; #176, #13): `scaledSecondDiff_tendsto_iteratedDeriv` — general C² Taylor convergence via Mathlib's `Real.taylor_tendsto` (Peano remainder). The central-second-difference ÷ h² → f''(x) for any `ContDiff ℝ 2 f`.
- [x] **`ScaledDiffC2Bridge.lean`** (A3; #14): `scaledSecondDiff_tendsto_iteratedDeriv_C2` — R1 specialised to h = 1/n (integer-scale refinement) + `hypergraph_scaled_laplacian_eq_scaledSecondDiff` (end-to-end cycleHypergraph → scaledSecondDiff at interior indices). Rung-2 bridge now works for **all** C² test functions, not just polynomials.
- [x] **`CycleSpectrum.lean`** (R5; #180): cycle Laplacian's closed-form eigenvalues/eigenvectors `λ_k = -4 sin²(πk/n)`, `f_k(j) = cos(2πkj/n)`; `cycleLaplacian_eigen_interior` (interior) + `cycleLaplacian_eigen` (full wrap-around using cos periodicity).
- [x] **`CycleEigenLimit.lean`** (A4; #15): `cycleEigenvalue_scaled_tendsto` — `n² · λ_k → -(2πk)²` (scaled cycle eigenvalues converge to continuum circle-Laplacian spectrum); key helper `n_sin_pi_k_div_n_tendsto` via Mathlib's `Real.sinc`.
- [x] **`LaplacianMatrix.lean`** (R2 / D3; #177, #44): `laplacianMatrix H : Matrix V V ℝ`, `laplacianMatrix_mulVec = laplacianHyper`, heat kernel via Mathlib's `Matrix.exp` (`heatKernel H t := exp(t • Δ_H)`), `heatKernel_zero = 1`, `heatKernel_add` (semigroup), `laplacianMatrix_symm`, `laplacianMatrix_row_sum`, `laplacianMatrix_mulVec_const`, `heatTrace`, `heatTrace_zero = |V|`. Rung-3 matrix/heat-kernel infrastructure.
- [x] **`CycleMatrixSpectrum.lean`**: `laplacianMatrix_cycleHypergraph_eigen` — matrix-level eigenvalue equation (cycle eigenvectors are genuine matrix eigenvectors of `laplacianMatrix (cycleHypergraph n)`).
- [x] **`HeatKernelODE.lean`** (T1): ODE ↔ matrix heat kernel unification. `hasDerivAt_heatKernel` (d/dt = · · Δ), `heatKernel_commute_laplacianMatrix`, `hasDerivAt_heatKernel_mulVec`, **`heatKernel_isHeatSolution`** (the matrix heatKernel satisfies `HeatSolution H`). The two heat-equation definitions (ODE predicate + Matrix.exp propagator) are now linked.
- [x] **`ExpEigenvector.lean`** (T2): matrix exp fixes eigenvectors. **`exp_mulVec_of_eigenvector`**: if `A.mulVec v = λ • v`, then `(NormedSpace.exp A).mulVec v = Real.exp λ • v`. Via `exp_eq_tsum_rat` + `ContinuousLinearMap.map_tsum` + `matrix_pow_mulVec_of_eigenvector` induction + `Real.summable_pow_div_factorial`.
- [x] **`CycleHasEigenvalue.lean`** (T4): cycle spectrum in Mathlib `Module.End.HasEigenvalue` form. **`laplacianMatrix_cycleHypergraph_hasEigenvalue`** connects our pointwise eigenvalue theorem to Mathlib's spectral-theory API.

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
- [x] Schwarzschild instance with non-trivial Christoffel symbols — **all 8 textbook Christoffel entries computed** (`Schwarzschild.lean`, task B1 #20 complete).
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
- [ ] **Convergence theorem (general)**: scaled Forman-Ricci on lattice graphs → continuum Ricci of the GH-limit manifold (extending beyond the trivial 0 = 0 case to non-flat targets). (R4 / #179 pending.)

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
- [x] **Discrete EL equation** `discreteEL τ φ ↔ ∀ i, B[φ](i) = 0` — the discrete Euler-Lagrange (analog of Gorard's `δS/δg^{ab} = 0`).
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
- [x] **All non-zero Christoffel entries** (task B1 #20 complete): `schwarzschildChristoffel_0_01`, `_1_00`, `_1_11`, `_1_22`, `_1_33`, `_2_12`, `_2_33`, `_3_13`, `_3_23` — all 8 computed and axiom-clean.
- [x] **`schwarzschild_christoffel_collapse`**: specialised Christoffel formula on Schwarzschild components.
- [ ] Compute Riemann tensor components (B2 #21 pending).
- [ ] Verify `Ric ≡ 0` (vacuum solution; B3 #22 pending).
- [ ] Cross-check via `vacuumEFE` (B4 #23 pending).

### Discrete heat equation on a hypergraph (Rung 6 entry)
- [x] `HeatSolution H u` predicate via `HasDerivAt` (`HeatEquation.lean`, task D1 #42).
- [x] Linearity of solutions (`heatSolution_zero`, `_add`, `_smul`).
- [x] Mass conservation `∑ u(t) = ∑ u(0)` via `laplacian_sum_zero` (`heat_mass_conservation`, D4 #45).
- [x] L² decay `‖u(t)‖² ≤ ‖u(0)‖²` via `laplacian_neg_psd` (`heat_L2_decay`, `heat_L2_antitone`, D5 #46).
- [x] Wave equation on hypergraph (`WaveEquation.lean`, D8 #49) with energy conservation.
- [x] Klein-Gordon equation on hypergraph (`KleinGordon.lean`, D9 #50) with energy conservation.
- [x] Schrödinger equation on hypergraph (`SchrodingerEquation.lean`, D10 #51) with unitarity / probability conservation.
- [x] Discrete scalar field Lagrangian + Euler-Lagrange (`ScalarField.lean`, G1 #68, G3 #70, G4 #71); `KG_EulerLagrange_iff_KleinGordonSolution`.
- [x] Heat semigroup on a finite graph as `Matrix.exp` (`LaplacianMatrix.lean`, D3 #44 / R2 #177): `heatKernel H t := exp(t · laplacianMatrix H)`, `heatKernel_zero = 1`, `heatKernel_add` (semigroup).
- [x] **ODE ↔ matrix heat kernel identification** (`HeatKernelODE.lean`, T1): `heatKernel_isHeatSolution` — the matrix propagator satisfies the `HeatSolution H` ODE predicate. Unifies the two heat-equation definitions.
- [x] Scaled cycle Laplacian → 1D `d²/dx²` for all C² test functions (R1/A2/A3; `CTwoTaylor.lean` + `ScaledDiffC2Bridge.lean`).
- [x] **Existence + forward-time uniqueness** (`HeatEquationUniqueness.lean`, D2 #43): `heat_exists` (via heatKernel T1), `heat_unique_forward` (via `heat_L2_antitone`), `heat_exists_unique_forward` package.
- [~] Long-time convergence to uniform (D6 #47 partial; `HeatKernelDecay.lean` proves each non-constant eigenmode `1 ≤ k < n` decays coordinate-wise to 0 under heat flow, via strict negativity of `cycleEigenvalue n k` and `Real.tendsto_exp_atBot`; remaining: eigenbasis decomposition of arbitrary initial data).
- [ ] Scaled discrete heat → continuous heat on GH-limit (D7 #48).
- [ ] Ollivier-Ricci with full proof (currently statement-only in `Infra/OllivierStatement.lean`).
- [ ] Choquet-Bruhat Einstein evolution (D11 #52).

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
- [x] Finite-slice cardinality bound under finite-successors assumption (`BranchialFinite.lean`, `branchialSliceFinite_of_successors_finite`, task I1 #84).
- [x] Fisher metric on branchial probability distributions (`FisherMetric.lean`, task IQ5 #152).
- [ ] Branchial measure: a probability assignment on each slice (I2 #85 pending).
- [x] ℓ²(slice) Hilbert space (I4 #87 / R3 #178 partial; `BranchialHilbert.lean` — `BranchialHilbert S := EuclideanSpace ℂ S` with ℂ-linear adjacency operator `branchialAdjLM` and self-adjointness `branchialAdjLM_inner` for symmetric adj).
- [ ] Branchial amplitudes / evolution toward Hilbert-space limit (I3 #86, I5 #88, I8 #91 pending).
- [ ] Fubini-Study limit under refinement (IQ6 #153 in progress).
- [ ] EME persistence as branchial observable (IQ8 #154 in progress).
- [ ] Path-integral over singleway causal graphs (IQ9 #155 in progress).

### Infrageometry program — 9 groups × 57 tasks (see [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md))

Full collation of the post-phase-1 infrageometry programme. Each group is a coherent research direction; per-task status tracked in `COVERAGE_MAP.md` §8.

#### IA — Infraanalysis / DAG calculus (5 tasks, all done)
- [x] IA1 DAG-as-blowup-of-interval (`DagBlowup.lean`; #109).
- [x] IA2 Calculus on coordinate DAGs (`DagCalculus.lean`; #110).
- [x] IA3 de Rham complex on Hypergraph V (`DeRham.lean`; #111).
- [x] IA4 Form → cochain integration map (`FormCochainIntegration.lean`; #112).
- [x] IA5 Blowup / refinement operators (`BlowupOperations.lean`; #113).

#### IG — InfraGaugeTheory (11 tasks, 10/11 done)
- [x] IG1 FiberedGraph type + basic properties (`FiberedGraph.lean`; #114).
- [x] IG2 Section structure + smoothness (#115).
- [x] IG3 Connection on a FiberedGraph (#116).
- [x] IG4 Parallel transport along a base path (`Holonomy.lean`; #117).
- [x] IG5 HolonomyMatrix on a loop (#118).
- [x] IG6 Wilson loop = trace of holonomy (#119).
- [x] IG7 FlatConnection predicate + theorems (#120).
- [x] IG8 FiberBundle predicate (`FiberBundle.lean`; #121).
- [x] IG9 GraphTangentBundle construction (#122).
- [x] IG11 Multi-fibered graph (`MultiFibrationProjection.lean`; #124).
- [ ] IG10 Exponential map via weighted shortest-path counts (#123 pending).

#### IC — Infracausality (8 tasks, all done)
- [x] IC1 Transitively-reduced causal graph type (`CausalGraphType.lean`; #125).
- [x] IC2 ObserverChain (maximal chain; #126).
- [x] IC3 LightRay as degenerate-interval subgraph (#127).
- [x] IC4 Foliation = successive antichains, ProperTime (`CausalFoliation.lean`; #128).
- [x] IC5 SpatiallyReconstructedHypergraph (`SpatialReconstruction.lean`; #129).
- [x] IC6 Multi-fibration from non-unique shortest-path projection (#130).
- [x] IC7 Ehlers-Pirani-Schild axioms as Props (`EPSAxioms.lean`; #131).
- [x] IC8 Marzke-Wheeler clock construction (`MarzkeWheeler.lean`; #132).

#### IT — Infratopology / Vietoris-Rips (6 tasks, 3 proved + 3 obligation-level)
- [x] IT1 Vietoris-Rips complex on a hypergraph (`VietorisRips.lean`; #133).
- [x] IT2 Hodge Laplacian on VR-complex 0- and 1-forms (`HodgeVR.lean`; #134).
- [x] IT4 Persistence diagram / barcode sentinel (#136).
- [ ] IT3 Spectrum of Hodge Laplacian as hypergraph invariant (#135 in progress).
- [ ] IT5 Latschev theorem as Prop obligation + proof for cycles (#137 in progress).
- [ ] IT6 Scale-dependence trichotomy theorem (#138 in progress).

#### ID — Infradimension (7 tasks, 5 proved + 2 obligation-level)
- [x] ID1 Wolfram-Hausdorff dimension as function on hypergraphs (`HypergraphDistance.lean`; #139).
- [x] ID2 Plateau-detection for Wolfram-Hausdorff dimension (`PlateauDimension.lean`; #140).
- [x] ID3 Homology dimension from persistence (`HomologyDimension.lean`; #141).
- [x] ID4 Coordinatization dimension via extremal orthogonal axes (`CoordinatizationDimension.lean`; #142).
- [x] ID5 Causal-graph dimension from longest-antichain analysis (`CausalDimension.lean`; #143).
- [ ] ID6 Compatibility theorem — all dimension notions agree on regular lattices (#144 in progress).
- [ ] ID7 Spectral dimension via heat-kernel trace (#145 in progress; `heatTrace` already built).

#### IB — Infrablowup (6 tasks, 5/6 done)
- [x] IB1 ElementaryBlowup (`ElementaryBlowup.lean`; #146).
- [x] IB3 BlowupLieAlgebra structure (`BlowupLieAlgebra.lean`; #148).
- [x] IB4 Insertion Lie algebra from unary blowups (#149).
- [x] IB5 Poisson bracket on formal hypergraph functions (#150).
- [x] IB6 Radial / laminar blowup operations (`RadialLaminarBlowup.lean`; #151).
- [ ] IB2 Causal-branchial-trivial commutator theorem (#147 in progress).

#### IQ — Branchial / quantum (4 formal obligations + 1 real theorem)
- [x] IQ5 Fisher metric on branchial graph (`FisherMetric.lean`; #152).
- [ ] IQ6 Fubini-Study as limit of Fisher under refinement (#153 in progress; obligation).
- [ ] IQ8 EME persistence as branchial observable (#154 in progress; obligation).
- [ ] IQ9 Path integral over singleway causal graphs (#155 in progress; obligation).

#### IS — Synthetic axiomatic infrageometry (3 tasks, all done)
- [x] IS1 Synthetic circle / line / sphere (`SyntheticGeometry.lean`; #156).
- [x] IS2 InfrageometricScene — multi-construction scene type (`InfrageometricScene.lean`; #157).
- [x] IS3 Axiomatic synthetic infrageometry, Euclid-style (`SyntheticAxiomatic.lean`; #158).

#### IR — Ruliology / rule taxonomy (7 tasks, 6 proved + 1 obligation-level)
- [x] IR1 RuleSignature functor (`RuleSignature.lean`; #159).
- [x] IR2 Conservation theorem — |LHS|=|RHS| implies bounded dimension (`RuleDimensionBounds.lean`; #160).
- [x] IR3 Tree-producing rules have log-branching dimension (`StructuralRuleBounds.lean`; #161).
- [x] IR4 Planar rules have dim ≤ 2 (Euler formula; #162).
- [x] IR5 Product rule dimension additivity (#163).
- [x] IR6 Candidate-rule database + screening pipeline (`CandidateRuleDatabase.lean`; #164).
- [ ] IR7 Reverse-engineer rule from target signature (#165 in progress; obligation).

### R-series real-work items (5 tasks, 3.5/5 done)
- [x] R1 C² Taylor convergence for scaled second difference (`CTwoTaylor.lean`; #176).
- [x] R2 laplacianMatrix + heatKernel via Matrix.exp (`LaplacianMatrix.lean`; #177).
- [~] R3 ℓ²(BranchialSlice) as Hilbert space with branchial adjacency operator (#178) — partial: Hilbert alias + ℂ-linear adjacency operator + self-adjointness proved (`BranchialHilbert.lean`); remaining: unitary evolution `exp (i·t·A)`.
- [ ] R4 Curved discrete-Ricci convergence beyond flat (#179).
- [x] R5 Cycle Laplacian spectrum closed form (`CycleSpectrum.lean`; #180).

### M-series colleague-work items (10 tasks, all pending)
- [ ] M1 Ioana Milea gauge-intern project coordination (#166).
- [ ] M2 Van Le Fisher→Fubini-Study bridge (#167).
- [ ] M3 Hubert Kolcz Lie-Poisson MBQC (#168).
- [ ] M4 Jan Pullman IBL-∞ / BV formalism (#169).
- [ ] M5 Carlos Zapata + Sara Ahmed axiomatic-relativity paper (#170).
- [ ] M6 Pokorny Infrageometry paclet parity (#171).
- [ ] M7 Ahmed EME-tracking community post (#172).
- [ ] M8 Pokorny diffusion-geometry bridge (#173).
- [ ] M9 Tropical-geometry synthetic infrageometry (#174).
- [ ] M10 3BP / dynamical-systems dimension signature (#175).

### Remaining-obligations module
- [~] `RemainingObligations.lean`: **T6 partial upgrade (2/7 done)**. IR7 `ReverseEngineeringObligation` and ID6 `DimensionCompatibilityObligation` now state real mathematical content in Lean types (existence of rule producing target signature; exact ball-volume formula on the cycle respectively). Five others (Latschev IT5, scale trichotomy IT6, Fubini-Study limit IQ6, EME persistence IQ8, path integral IQ9) remain at `True ∧ False` stub level pending additional Mathlib infrastructure; `five_stub_obligations_open` certifies those stubs are uninhabited.

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
- [x] Scaled $d$-dim lattice → flat $d$-torus, any $d$ (`Infra/ScaledTorusD.lean`, `dTorus_gh_bound`).
- [x] Discrete → continuum Minkowski bridge for any $d$ (`Infra/ScaledLorentz.lean` + `Infra/FullBridge.lean`): exact isometry + iff causal preservation + density.
- [ ] Scaled Cayley graph of a finitely-generated group → its asymptotic cone.
- [ ] Random geometric graph on a Riemannian manifold → the manifold (the positive analogue of Gorard's §3).
- [ ] Causal-set Poisson sample of a Lorentzian spacetime → the spacetime (Lorentzian-GH, contingent on Mathlib infrastructure).

## Phase 4 — Discrete geometric structures library (Lean)

- [x] `Hypergraph V` as a graph-distance space (`HypergraphDistance.lean`): `Hypergraph.Adj`, `Hypergraph.dist`, geodesic balls, ball volume; `dist_self`, `dist_comm`, **`dist_triangle`** (via `Connected` hypothesis) + **`dist_triangle_of_reachable_{left,right}`** (conditional forms), monotonicity; cycle-hypergraph adjacency / ballVolume instances; **`cycleHypergraph_connected`** (for n ≥ 2) + **`cycleHypergraph_dist_triangle`** unconditional on cycles (T3 tightening).
- [x] Wolfram-Hausdorff dimension as function on hypergraphs (task ID1 `wolframHausdorffDimension`; plateau version ID2).
- [x] Benincasa–Dowker discrete d'Alembertian on a causal graph (`DiscreteDAlembertian.lean`): BD-4D operator, action, EL, F6 flagged as explicit Prop obligation.
- [x] Vietoris-Rips complex + Hodge Laplacian on a hypergraph (`VietorisRips.lean`, `HodgeVR.lean`).
- [x] Hypergraph Laplacian as a matrix (`LaplacianMatrix.lean`): symmetric matrix, kills constants, row-sum zero; heat kernel as `Matrix.exp`.
- [x] **Counting measure on a hypergraph + pushforward** (`HypergraphMeasure.lean`, A5 #16): `countingMeasure`, `uniformProbability`, `pushforwardCounting`, `pushforwardUniform`; `countingMeasure_univ = |V|`, `uniformProbability_univ = 1`.
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

Gorard's companion program (arXiv:2004.14808 and related) claims that the *branchial* structure of the multiway evolution graph recovers quantum mechanics. This is its own research line and has not been adequately audited yet; included here because quantum-mechanical content is the *only* plausible first-principles bridge between Wolfram rewriting and observed physics (since GR emerges only statistically / in the continuum limit).

- [ ] Audit Gorard's QM paper with same S1–S6 methodology.
- [x] Define the `RewritingSystem` / `Step` / `MultiStep` machinery in Lean (states = hypergraphs, edges = applications; full branching tree via `Branchial.lean`).
- [x] Define `BranchialSlice` (states at a common evolution depth with shared ancestry; `Branchial.lean`, `BranchialFinite.lean`).
- [x] Define `SchrodingerEquation` on `Hypergraph V` with proven unitarity (`SchrodingerEquation.lean`, task D10).
- [x] Fisher metric on branchial distributions (`FisherMetric.lean`, IQ5 #152).
- [ ] Integrate with `../efficient_rewriting_final/` multi-way engine for concrete examples (X4 #75 pending).
- [ ] Define a measure / amplitude on branchial paths (I2 #85 pending).
- [~] Branchial-amplitude / Hilbert-space limit (I3 #86, I5 #88, I8 #91 pending; I4 #87 / R3 #178 ℓ²(slice) ✅ partial via `BranchialHilbert.lean`).
- [ ] Fubini-Study limit under branchial refinement (IQ6 #153 in progress).

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
