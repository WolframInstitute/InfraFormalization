# Publishable outputs: target list

This is the list of papers and technical notes the programme is working toward. Each entry names its audience and the conditions under which the paper is ready. Entries run from those whose content mostly exists to those that are open research.

Status labels follow `STATUS_OF_GORARD_CLAIMS.md`: PROVED (a Lean theorem with axioms at most `propext`, `Classical.choice`, `Quot.sound`), PROVED-WITH-NATIVE-DECIDE, MEASURED, READ (from the paper text, with line numbers), OPEN. A paper target cites PROVED or PROVED-WITH-NATIVE-DECIDE results as contributions.

Paper files: G1 = `papers/gorard_2004.14810.txt`, G2 = `papers/gorard_2011.12174.txt`, G3 = `papers/gorard_2102.09363.txt`, G4 = `papers/gorard_2303.07282.txt`.

## P1: Audit of G1-G4 (J. Gorard)

Summary. An audit of arXiv:2004.14810, 2011.12174, 2102.09363 and 2303.07282. The papers state that general relativity follows from Wolfram-model hypergraph rewriting. The audit records, with line numbers, where the papers give no proof of a step, and what the repository proves and measures about the rule of G3. The findings about the papers are READ findings (`STATUS_OF_GORARD_CLAIMS.md`, `MAJOR_FLAWS.md`). The Lean files prove statements about the rule of G3.

Status: not ready. F6 has no Lean statement about G3, the technical comment is not written, and external review has not taken place.

Conditions:
- [x] Severity taxonomy S1-S6 with TeX line references (`notes/severity_taxonomy.md`). READ.
- [x] F1-F5: findings about G1. READ.
- [ ] F6: G3's initial data is sampled from the target geometry (READ, G3 lines 6148-6152 and 6179). A Lean statement about G3's procedure is OPEN.
- [x] Cross-paper map of repeated findings (`notes/corpus_audit.md`). READ.
- [x] Continuum-limit claims catalog (`notes/continuum_limit_claims.md`). READ.
- [x] Close readings of the four papers. READ.
- [x] Edge-count conservation of the rule of G3: `Refutations.gorardNamedRule_applications_preserve_size`. PROVED.
- [x] Causal graph of the rule of G3, for every update order: an identity is consumed by at most one event, every antichain has at most N/4 events (`CausalHistory.gorardNamedRule_antichain_card_le`), and at most 5^t events lie within directed distance t of an event (`CausalHistory.gorardNamedRule_ball_card_le`). PROVED.
- [ ] Linear cone growth of the rule of G3: `CausalHistory.GorardNamedRuleConeGrowthLinear`. OPEN.
- [x] Cone-growth exponents of the rule of G3: the SetReplace and Python tables differ because the tools use different update orders. Across four update orders the exponent ranges from 0.77 to 1.26 on 9 seeds (`notes/empirical_refutation.md` §4). MEASURED.
- [ ] A run of the rule of G3 on a Poisson sprinkling of Brill-Lindquist initial data at the resolutions of G3 Table 6. OPEN.
- [ ] A technical comment of at most 15 pages.
- [ ] External review by Wolfram Institute colleagues.

Audience. *Complex Systems*; arXiv math-ph and gr-qc.

Lean results cited:
- F1-F6: none.
- F7: `Refutations.gorardNamedRule_applications_preserve_size`, `Application.size_result_of_conservative`, `CausalHistory.gorardNamedRule_antichain_card_le`, `CausalHistory.gorardNamedRule_ball_card_le` (PROVED).

## P2: Corrected continuum identities

Summary. The Ollivier-Ricci identity and the Gray tube formula stated as Lean definitions, with their leading terms compared with the forms in G3 (eqs. 342 and 344) on S² and S³.

Status: the statements and the comparisons are PROVED arithmetic. The identities themselves come from Gray 1973 and Ollivier 2009 and are not formalised.

Conditions:
- [x] `Infra.OllivierIdentityLeading`, `GorardMisstatedForm`, `Infra.ollivier_gorard_agree_iff` (for δ, ε ≠ 0 the leading terms agree iff R = Ric(v,v)). PROVED.
- [x] `Infra.GrayTubeLeading`, `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`. PROVED.
- [ ] Proofs of the Ollivier and Gray identities, using the project's Ricci tensor (task #217) and Wasserstein-1 distance (task #214). OPEN.

Audience. arXiv math.DG and math-ph.

## P3: Discrete-to-continuum templates (cycle, path, torus, Lorentz lattice)

Summary. A Lean library of Gromov-Hausdorff bounds from discrete spaces to continuum spaces: cycle to circle, path to interval, (d+1)-lattice to (d+1)-torus, integer lattice to Minkowski space, under a common `GHApproximation` structure. It includes spectral convergence of the cycle Laplacian and a project-own Wasserstein-1 distance.

Status: flat targets are done. Curved targets are OPEN (task #218).

Conditions:
- [x] `cycle_circle_gh_bound`. PROVED.
- [x] `path_interval_gh_bound`. PROVED.
- [x] `torus_gh_bound` (2D) and `dTorus_gh_bound` (any d). PROVED.
- [x] `lorentzIntEmbed_preserves_causal_iff` (causal relation preserved in both directions by the integer embedding). PROVED.
- [x] `scaledLorentzEmbed_dense`, `continuumSpaceDist_eq_cast` (scaled isometry and density). PROVED.
- [x] Scaled second difference: `scaledSecondDiff_tendsto_iteratedDeriv` (convergence to f'' for every C² function, `CTwoTaylor.lean`), `scaledSecondDiff_tendsto_iteratedDeriv_C2` (`ScaledDiffC2Bridge.lean`), `hypergraph_scaled_laplacian_eq_scaledSecondDiff`. PROVED.
- [x] Cycle spectrum: `cycleLaplacian_eigen` (`CycleSpectrum.lean`) (eigenvalues −4 sin²(πk/n), eigenvectors cos(2πkj/n)). PROVED.
- [x] Eigenvalue convergence: `cycleEigenvalue_scaled_tendsto` (`CycleEigenLimit.lean`) (n²·λ_k → −(2πk)²). PROVED.
- [x] Laplacian matrix and heat kernel: `laplacianMatrix_mulVec`, `heatKernel H t := exp(t·Δ)`, `heatKernel_add`, `heatTrace`, `laplacianMatrix_symm`. PROVED.
- [x] Heat kernel solves the heat ODE: `heatKernel_isHeatSolution`; existence and forward uniqueness (`heat_exists_unique_forward`). PROVED.
- [x] Conservation laws of the heat kernel: `heatKernel_mulVec_const`, `heatKernel_mass_conservation`, `heatKernel_L2_decay`, `heatKernel_mulVec_add`. PROVED.
- [x] `exp_mulVec_of_eigenvector` (the matrix exponential maps an eigenvector v to e^λ v) and `laplacianMatrix_cycleHypergraph_hasEigenvalue`. PROVED.
- [x] Counting measure and pushforward on `Hypergraph V` (`HypergraphMeasure.lean`). PROVED.
- [~] Wasserstein-1 distance on finite supports (`WassersteinFinite.lean`, `CycleWasserstein.lean`): `wasserstein1_self_eq_zero`, `wasserstein1_symm`, `wasserstein1_triangle`, `wasserstein1_delta_eq_dist`, `wasserstein1_lipschitz_bound` (|E_μ f − E_ν f| ≤ L·W_1(μ,ν) for L-Lipschitz f). On the cycle: `wasserstein1_cycleDelta_succ = 1/n`, `wasserstein1_shiftMeasure_le`, `wasserstein1_shiftIter_le` (W_1(μ, shift^k μ) ≤ k/n). PROVED. The convergence rate of the scaled counting measure to Lebesgue measure is OPEN.
- [x] `Hypergraph.dist` triangle inequality and connectivity of the cycle (`dist_triangle`, `cycleHypergraph_connected`). PROVED.
- [ ] A 25-page paper with the Lean library as an appendix.

Audience. arXiv math.MG, math-ph and formal methods.

## P4: Library of structural theorems on hypergraph rewriting

Summary. A Lean library of structural theorems about hypergraph rewriting: edge conservation, degree sums, causal-level monotonicity, antichain bounds, the hypergraph Laplacian and discrete exterior calculus.

Status: the theorems below are PROVED unless marked. The library has 39 modules with theorems that depend on `native_decide`. A paper reports the status of each cited result.

Conditions:
- [x] Edge conservation, degree sums, per-event balance. PROVED.
- [x] Level monotonicity and same-level antichain, forward direction (`level_add_one_le_of_isCausalPred`, `no_causal_edge_within_level`). PROVED.
- [x] Hypergraph Laplacian: self-adjointness, Dirichlet form, positive semidefiniteness of −Δ, `laplacianHyper_sum_zero`. PROVED.
- [x] Laplacian matrix: symmetry, zero row sums, heat kernel as `Matrix.exp` (semigroup, `heatTrace`). PROVED.
- [x] Forman-Ricci curvature (graphs and hypergraphs). On 2-regular graphs it is 0, and the circle metric has Ricci tensor 0 (`cycle_forman_and_flat_ricci_zero`). PROVED.
- [x] Cycle Laplacian equals the central second difference at interior points. PROVED.
- [x] Scaled second difference converges to f'' for every C² function. PROVED.
- [x] Cycle spectrum and convergence of the scaled eigenvalues to those of the circle. PROVED.
- [x] Discrete PDEs on `Hypergraph V`: heat (mass conservation, L² decay), wave (energy conservation), Klein-Gordon, Schrödinger (unitarity), scalar field (Euler-Lagrange equation equivalent to Klein-Gordon). PROVED.
- [x] Discrete exterior calculus: `summation_by_parts` (`HypergraphCalculus.lean`), `DeRham.lean`, `FormCochainIntegration.lean`. PROVED.
- [x] `Knill.dSquared_eq_zero` (`KnillCore.lean`, d∘d = 0 on oriented simplices, `[LinearOrder V]`), `dStarSquared_eq_zero`, `hodgeOnG_psd`, `hodgeOnG_dirichlet_zero_iff_isDiracKernel`. PROVED.
- [x] `Knill.wuCharacteristic₂_eq_chi_sq_sub_disjoint` (Wu inclusion-exclusion). PROVED.
- [x] `Knill.eulerCharacteristic_eq_alt_sum_kSkeleton` and `Knill.eulerCharacteristic_eq_alt_sum_fintype` (Euler-Poincaré f-vector identity). PROVED.
- [x] `KnillEulerCharIdentity.knill_eq_six_euler_char` (Σ_v K6(v) = 6·(V − E + T)). PROVED.
- [x] Type-level map from the executable engine to the abstract rewriting system (`MultiwayExecBridge.lean`: `ExecRule.toRule`, `Fin.embedSuffix`, the single-rule `ExecSystem` cast). PROVED. A step-level simulation lemma between `singleWayStep` and `MultiStep` is OPEN.
- [x] Infrageometry groups IA-IR: definitions with lemmas. IR3, IR4 and IR5 are definitions only.
- [x] Hypergraph distance, geodesic balls, Wolfram-Hausdorff dimension (`HypergraphDistance.lean`). PROVED.
- [x] Benincasa-Dowker discrete d'Alembertian, action and Euler-Lagrange equation (definitions, linearity, `layer_disjoint`, `mem_layer_isCausalPred`). PROVED.
- [x] `trajectory_size_invariant` (state size constant along a conservative trajectory). PROVED.
- [x] Trajectory-structure lemma for histories with hyperedge identities: every consumed identity is initial or produced by an earlier event (`CausalHistory.History.ins_source`, `CausalHistory.History.edge_lt`). PROVED. The value-based form for `Trajectory` in `CausalLevel.lean` is OPEN.
- [x] Antichain bound for histories with hyperedge identities: for \|LHS\| = \|RHS\| = k and N initial hyperedges, k·\|A\| ≤ N for every antichain A (`CausalHistory.RuleHistory.antichain_card_le`). PROVED. The layer form `|layer_s| ≤ N/k` for `Trajectory` is OPEN.
- [ ] A 25-page paper.

Audience. arXiv cs.LO, math.CO and formal methods.

## P5: A Wolfram-model rule with a proved continuum limit

Summary. A rewriting rule whose evolution is proved to converge, in the Gromov-Hausdorff sense, to a specific Lorentzian manifold, with discrete curvature on the causal graph converging to the continuum Ricci tensor.

Status: OPEN. No candidate rule is identified.

Results available as infrastructure:
- [x] `Infra/LorentzLattice.lean`, `Infra/Minkowski.lean`, `Infra/FullBridge.lean`: the integer Lorentz lattice embeds in continuum Minkowski space isometrically on spatial distance and preserves the causal relation. `causallyPrecedes_gives_continuum` holds under the hypothesis `LightConeCompatible τ φ`. PROVED.
- [x] `DiscreteDAlembertian`: the Benincasa-Dowker operator on trajectories, `discreteAction`, `discreteEL`. PROVED (definitions and linearity).
- [x] `leviCivitaConnection : MetricDataC2 n → ConnectionData n` and the Riemann, Ricci and Einstein tensors in local coordinates. PROVED.
- [x] Schwarzschild: all nonzero Christoffel symbols in the exterior (`Schwarzschild.lean`). PROVED. The Riemann and Ricci tensors (B2, B3) are OPEN.
- [x] FLRW: Ricci tensor, and the diagonal Einstein equations with a perfect fluid are equivalent to the Friedmann equations (`flrwEFE_diag_iff_friedmann`, `flrw_satisfies_EFE_00_11_of_friedmann`, `flrw_friedmann_of_EFE`). PROVED.

- [x] Cycle spectrum converges to the circle spectrum (`CycleSpectrum.lean`, `CycleEigenLimit.lean`). PROVED.
- [x] `EPSAxioms.lean`, `MarzkeWheeler.lean`: Ehlers-Pirani-Schild structures and Marzke-Wheeler ticks on a causal graph, as definitions with `eps_worldline_not_light` and `mwClock_implies_causallyPrecedes`. PROVED.
- [x] Causal foliation, spatial reconstruction and proper time (IC4, IC5): `stablyCausal_hasFoliation` (every stably causal DAG has a foliation). PROVED.
- [x] `CandidateRuleDatabase.lean`: candidate-rule records and screening predicates. PROVED.
- [x] `RuleDimensionBounds.lean`: `Hypergraph.geodesicBallVolume_le_card` (ball volume at most the vertex count). PROVED. It holds for every finite hypergraph and does not bound a dimension.
- [x] Angles, scalar curvature from ball growth, topology: `Hypergraph.elementaryAngle`, `cosAngle`, `angle`, `IsOrthoApprox`, `Hypergraph.scalarCurvatureAt`, `firstBettiZ`, `spatialB0`, `perpBisector`, `voronoiCell`, `midpoint`. Definitions with lemmas, PROVED. `HasTopologicalHyperplane` is a placeholder: it requires A and B to be unreachable from each other in the whole hypergraph, and does not state that removing the bisector disconnects them.
- [x] The bounded rule search of `RuleSignatureExecSearch.lean`. PROVED-WITH-NATIVE-DECIDE.
- [ ] A candidate rule with a curved target (Phase C, `ROADMAP.md`). OPEN.
- [ ] A convergence theorem for that rule to a curved Lorentzian metric (#218, #236). OPEN.

Audience. arXiv gr-qc and math-ph (*Physical Review D*, *Classical and Quantum Gravity*, *Foundations of Physics*).

## P6: Branchial quantum mechanics, audit and formalisation

Summary. An audit of the statement that branchial structure recovers quantum mechanics, with the same method as P1, and a formalisation of the parts that hold.

Status: partial infrastructure.

Conditions:
- [x] `Branchial.lean`: `BranchialRelated`, `NStep`, `BranchialSlice`. PROVED.
- [x] `BranchialFinite.lean`: `branchialSliceFinite_of_successors_finite`. PROVED.
- [x] `FisherMetric.lean`: Fisher metric on distributions over a slice. PROVED.
- [x] `SchrodingerEquation.lean`: discrete Schrödinger equation on `Hypergraph V` with unitarity. PROVED.
- [ ] S1-S6 audit of the QM paper (arXiv:2004.14808).
- [x] Uniform measure on a finite slice (`branchialUniformWeight`). PROVED.
- [x] ℓ²(slice) as a complex Hilbert space with the adjacency operator `branchialAdjLM`, self-adjoint for symmetric adjacency (`branchialAdjLM_inner`). PROVED.
- [~] Amplitudes and unitary evolution: `BranchialAmplitude`, Born probabilities, `branchialSchrodinger_unitary_evolution` (PROVED). The Hilbert-space continuum limit (I8) is OPEN.
- [ ] A proof or disproof of a statement that branchial structure converges to a quantum system. OPEN.

Audience. arXiv quant-ph and math-ph.

## P7: Binary black hole merger from hypergraph rewriting

Summary. Hypergraph initial data for a binary black hole, evolved under a rule from P5, with a proof of convergence to the merger spacetime.

Status: depends on P5. G3 §6 reports a numerical comparison of this kind (READ, G3 lines 6146-6290) and gives no proof that the rule used satisfies the Einstein equations.

Conditions:
- [ ] P5 completed.
- [ ] Discrete Brill-Lindquist initial data on a hypergraph.
- [ ] Evolution under the P5 rule.
- [ ] Discrete Ψ₄ extraction compared with binary black hole waveforms.
- [ ] Lorentzian Gromov-Hausdorff convergence to a merger spacetime.

Audience. As P5.

## P8: Discrete d'Alembertian on a causal DAG

Summary. A Lean formalisation of the Benincasa-Dowker discrete d'Alembertian on the causal DAG of a Wolfram-model trajectory. G3 uses the continuum limit of the Benincasa-Dowker action under the assumptions of zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood (READ, G3 lines 6110-6120). The note would state that limit as an open conjecture.

Status: the operator is defined and its linearity is PROVED (`DiscreteDAlembertian.lean`). The conjecture is not stated in Lean.

Conditions:
- [x] `openInterval`, `intervalSize`, `layer τ k i`, `discreteDAlembertian4` defined; `discreteDAlembertian4_add` and related linearity lemmas. PROVED.
- [x] `discreteAction` (analogue of G1 eq. 86) and `discreteEL`; `discreteAction_smul`. PROVED.
- [x] `layer_disjoint`, `mem_layer_isCausalPred`. PROVED.
- [ ] A Lean statement of the Benincasa-Dowker limit B_ρ → □ − ½R. OPEN.
- [ ] A d'Alembertian for general dimension d, with coefficients indexed by d (2D: (1, −2, 1)). Not defined. OPEN.
- [ ] A 10-page note with a review of the Benincasa-Dowker literature.

Audience. arXiv gr-qc and hep-th (*Classical and Quantum Gravity*, Letter).

## P9: The derivation of the Einstein equations in G1, step by step

Summary. A paper that follows the derivation in G1 §3.3 (lines 2168-2240) step by step. For each step it states whether G1 gives a construction or a proof: G1 introduces a metric without a construction (F1), assumes orthonormality without a bilinear form (F2), states asymptotic dimension preservation as the Euler-Lagrange equation (F3), identifies causal invariance with discrete general covariance (F4), and passes from sum to integral without a notion of convergence (F5). These findings are READ. The library has no Lean statement for them.

Status: not ready. F6 has no Lean statement about G3.

Conditions:
- [x] F1-F5: close reading of G1 §3.3 with line numbers. READ.
- [ ] F6:
 a Lean statement of the Benincasa-Dowker limit and of G3's initial-data procedure. OPEN.
- [ ] A 15-page draft.

Audience. arXiv gr-qc and cs.LO.

## Dependencies and ordering

```
P1 (audit) ──────────────────┐
P2 (corrected identities) ───┤
P3 (continuum templates) ────┤
P4 (structural library) ─────┤
P8 (discrete d'Alembertian) ─┤
P9 (G1 derivation) ──────────┘
                             │
                             ▼
                            P5 (Wolfram → GR)
                           /       \
                          ▼         ▼
                         P7 (BBH)   P6 (QM branchial)
```

P1-P4, P8 and P9 are independent of each other, and most of their content exists. P5 is open research. P7 depends on P5. P6 is independent of P5.

## Conventions

- Every paper target names the Lean results it cites, with their status labels.
- Draft PDFs live under `reports/`.
- No paper leaves the group without internal review.
- A paper states only results with the status PROVED, PROVED-WITH-NATIVE-DECIDE, MEASURED or READ as findings, and states open problems as OPEN.
