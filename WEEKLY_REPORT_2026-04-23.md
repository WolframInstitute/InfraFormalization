# Weekly report — 2026-04-23

Project: **`infra_formalization`** — Lean 4 / Mathlib formalisation of the Wolfram-model → GR / QM programme, plus a machine-checked audit of Gorard's published derivation claims.

## Project at a glance

- Three axes: (i) positive construction of a 10-rung bridge from hypergraph rewriting to Einstein's equations; (ii) Lean-formal audit of four Gorard papers (2004.14810, 2011.12174, 2102.09363, 2303.07282); (iii) Wolfram-Institute *infrageometry* programme (57 tasks / 9 groups).
- 140 Lean modules; ~20k LOC; 3468 `lake` build jobs.
- Every proved theorem reduces to `{propext, Classical.choice, Quot.sound}`; no `sorry`, no `native_decide`, no custom axioms.
- Grounding principle: every continuous object has a hypergraph anchor or an attached origin-obligation Prop.

## Size and counts

- 140 Lean source files in `lean/InfraFormalization/` (~20.2k lines of code).
- **679 theorems** + 17 lemmas + 17 examples proved (≈713 proved propositions).
- 381 definitions, 57 structures, 6 inductives, 12 instances.
- 497 `#print axioms` lines in `AxiomCheck.lean` across 94 modules — every listed theorem certified to depend only on `{propext, Classical.choice, Quot.sound}`.
- `lake build`: 3468 / 3468 jobs green.

## Headline status

- Axiom-cleanliness: no `sorry`, no `native_decide`, no custom axioms; only the three standard Lean axioms.
- Grounding audit: 4 of 4 action items closed. Every continuum GR structure in the repository carries an obligation Prop binding it to a hypergraph-side witness, so no continuum object stands unattached to the hypergraph substrate.
- Infrageometry programme: 50 of 57 tasks closed with real content; 7 in progress with substantive open content (not stubs).
- Gorard corpus: F1–F7 formalised as Lean theorems, plus F8 as a documentary finding (title-body gap in G4).
- Flat continuum-limit bridges proved: cycle → circle, path → interval, 2-torus, d-torus, discrete Lorentz → Minkowski.

## Motivation and the Gorard corpus

The published Wolfram-model-to-GR derivations of Jonathan Gorard make a strong claim: that a specific hypergraph rewriting rule "provably satisfies the Einstein field equations in the continuum limit" (G3 abstract). The formal audit here checks that chain end-to-end, classifies each step, and decides the load-bearing ones either correct (verify and formalise) or flawed (refute and formalise the refutation).

**The four audited papers**

- **G1 — arXiv:2004.14810** — *Some Relativistic and Gravitational Properties of the Wolfram Model.* Foundational paper. §3.3 is the claimed Einstein-equations derivation; §3.1 states the Ollivier–Ricci identity; §3.2 introduces the fiat-orthonormality convention.
- **G2 — arXiv:2011.12174** — *Algorithmic Causal Sets and the Wolfram Model.* Reuses G1's §5 derivation; introduces Eq 126 (tube-volume coefficient) used later in G3 Eq 342.
- **G3 — arXiv:2102.09363** — *Hypergraph Discretization of the Cauchy Problem in GR via Wolfram Model Evolution.* Contains the "provably satisfies EFE" claim (abstract + line 6202) and the named rule. Relies on a Poisson-sprinkle-then-reconstruct schema (lines 6080, 6152).
- **G4 — arXiv:2303.07282** — *Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems.* Title-body gap: no discrete Raychaudhuri, no discrete expansion scalar, no discrete energy condition, no discrete stress-energy tensor, no "shear" or "vorticity" in the text; conclusion acknowledges all these as open.

**General patterns found across the corpus**

- Objects introduced by analogy rather than construction: discrete metric tensor `g^{ab}`, discrete volume form `d\mu_g`, functional derivative `δ/δg^{ab}`, "orthonormal" hyperedges — all named, none defined.
- Arithmetic mis-statements of cited continuum identities: Ollivier's theorem uses directional `Ric(v,v)`, the papers write scalar `R`; Gray's tube coefficient is `(R + Ric(u,u))/(6(d+1))`, the papers write `(d−1)(R − Ric(u,u))/(d+1)` — factor-2 off on S², factor-6 off on S³.
- Definitions restated as theorems: "causal invariance ⇔ discrete general covariance" and "asymptotic dimensionality preservation ⇒ EFE" both unfold to `Iff.rfl`.
- Bridge claims left to informal prose: "becomes" (which convergence topology?), "weak ergodicity" (precise definition?), "provably" applied to an open Sorkin–Benincasa–Dowker conjecture.
- Circularity: the G3 proof of EFE-satisfaction builds the initial hypergraph by Poisson-sampling vertices from the known target spacetime, then recovers that spacetime from the sample. Target-as-input.
- Structural block: the specific named rule has `|LHS| = |RHS| = 4`, so edge count is conserved and the causal cone grows linearly — dimension-1 — on every tested seed in two independent implementations (SetReplace and a Python re-implementation).

**Flaws formalised as Lean theorems (F1–F7)**

| Flaw | Lean | Substance | Axiom budget |
|---|---|---|---|
| F1 | `Refutations/F1NoMetric.lean` | No canonical metric from hypergraph alone: any "hypergraph → bilinear form" construction is non-unique; `metric_construction_is_never_unique` + `no_canonical_metric_from_hypergraph_alone` + `action_depends_on_construction_choice` | three standard |
| F2 | `Refutations/F2Orthonormality.lean` | Orthonormality is a property of a bilinear form, not of the hyperedges; `orthonormalising_form_not_unique`; `gorard_orthonormality_is_non_canonical` | three standard |
| F3 | `Refutations/F3Tautology.lean` | `gorard_dim_preservation_is_euler_lagrange : AsymptoticDimPreservation P g ↔ EulerLagrange P g := Iff.rfl`; `gorard_section_3_3_contentless` | three standard |
| F4 | `Refutations/F4Tautology.lean` | `gorard_causal_invariance_is_general_covariance := Iff.rfl` | `#print axioms` reports "does not depend on any axioms" — zero |
| F5 | `Refutations/F5Illdefined.lean` | "becomes" is convergence-notion-dependent: `becomes_is_underdetermined`, `claim_is_vacuous_without_convergence_notion`, `different_notions_give_different_limits` | three standard |
| F6 | `Refutations/F6Circularity.lean` | `CircularReconstruction` schema; `circular_reconstruction_has_no_content`; `circular_procedure_is_identity` (the Poisson-sprinkle-then-reconstruct returns its input) | three standard (`circular_reconstruction_has_no_content` uses 0) |
| F7 | `Refutations/F7NamedRuleStructure.lean` | `namedRule_trajectory_edge_count_fixed`; `isConservative_implies_structurallyOneDim` — conservative rules fix edge count along every trajectory; cone-growth dimension ≈ 1 on every tested seed | three standard |

**F8** (G4 title-body gap) is not a formal claim but a documentary finding: the title promises discrete singularity theorems that the body does not deliver, a fact Gorard himself concedes in the paper's conclusion.

**Summary verdict on the corpus.** Systematic overclaim. The §3.3 Einstein-equations derivation in G1 uses objects that are never constructed (F1, F2). The logical spine reduces, in multiple places, to `Iff.rfl` (F3, F4). The continuum-limit step is left informal (F5). The G3 "proof" that a rule satisfies EFE is circular (F6). The specific named rule is empirically and structurally 1-dimensional (F7). The correct cited identities are mis-stated by non-trivial factors on simple test manifolds (Eq 342, Eq 344).

Nothing in the corpus is fabrication; every error is public and checkable. The goal of this formalisation is not to discredit but to leave a load-bearing, verifiable record of what is true, what is wrong, and what remains genuinely open.

## State of the discrete-continuum bridge

The 10-rung bridge ladder from `Hypergraph V` to Einstein's equations.

Legend for the State column:
- **proved** — the content of the rung is a machine-checked theorem.
- **partial** — some of the rung's content is proved; specific sub-items are listed open in the Content column.
- **flat case proved; curved case open** — the rung is proved when the underlying spacetime is flat (Minkowski / cycle / torus / lattice); the proof for a curved target (Schwarzschild, Kerr, FLRW) is open.
- **flat case proved end-to-end; curved case has the obligation Prop attached but the curved bridge theorem is open** — for Rung 10: every continuum GR target has an obligation Prop binding it to a hypergraph-side witness; flat-case witnesses are inhabited; curved-case witnesses are not.

| Rung | Topic | State | Content |
|---|---|---|---|
| 1 | Discrete calculus on graphs / hypergraphs | proved | Laplacian `Δ_H` as `LinearMap`, self-adjointness, Dirichlet form, PSD, divergence theorem `∑ Δf = 0`; matrix form `laplacianMatrix`, symmetric, row-sum zero; heat kernel `exp(t·Δ)` with semigroup property; cycle / hypergraph instances; discrete `∇`, `div`, summation by parts |
| 2 | Operator convergence (discrete → continuum) | proved | Scaled second difference → `f''` for every C² function (R1 / A2 / A3); cycle-eigenvalue spectrum closed form (R5); scaled cycle eigenvalue `n² · (−4 sin²(πk/n)) → −(2πk)²` (A4), continuum circle Laplacian spectrum recovered; path spectrum and ground-mode (T5 partial); ODE ↔ matrix heat kernel unified (T1); uniform-C^k-on-compacts version open |
| 3 | Measure-theoretic limits | partial | Counting measure, uniform probability, pushforward all proved (A5); A6 weak convergence counting → Lebesgue open; A7 Wasserstein-1 rate O(1/n) open; A8 d-torus measure lift open |
| 4 | Connections / Levi-Civita | partial | Local-coordinate Christoffel and covariant derivative proved; bundle-theoretic formulation (Riemannian / Lorentzian vector bundles + Koszul) blocked by missing Mathlib infrastructure (C1–C8); bridge-obligation attached (`ConnectionDataOriginObligation`) and inhabited in the flat-connection case |
| 5 | Riemann / Ricci / scalar / Einstein | proved | Local-coordinate Riemann, Ricci, scalar curvature, Einstein tensor; flat connection = zero; GR metric zoo (Minkowski, Schwarzschild with all 8 Christoffels, FLRW, Reissner-Nordström, Kerr, 2-sphere, de Sitter, warpedDiag2) all bundled as `MetricData` or `PartialMetricData`; `minkowski4_satisfies_vacuum_EFE` |
| 6 | ODE / PDE on `Hypergraph V` | proved | Heat equation (D1 / D2 / D4 / D5 / D6 partial); wave equation (D8); Klein-Gordon (D9); Schrödinger unitary (D10); scalar field Lagrangian + Euler-Lagrange (G1 / G3 / G4); Benincasa–Dowker 4D d'Alembertian (BD conjecture flagged); D7 scaled discrete heat → continuum heat on GH-limit proved; bundled PDE spectrum bridge (cycle → circle) for heat / wave / Schrödinger / KG |
| 7 | Fields / gauge | partial | Scalar field proved; G2 discrete gauge field via Rung-4 connection open; G5 continuum limits of discrete fields open |
| 8 | Lorentzian geometry | flat case proved; curved case open | Discrete structures (LorentzLattice, Minkowski); causal graph TR-DAG (IC1); `DiagLorentzianManifold` (E1) with Minkowski instance; causality conditions strong / stable / globally-hyperbolic (E4); light cones, causal future/past (E3); Cauchy-foliation existence from stably-causal time function (E5); E6 Lorentzian Gromov-Hausdorff open (Mathlib gap); E7 discrete-causal → continuum-Lorentzian convergence open |
| 9 | Einstein equations | flat case proved; curved case open | F3 `EinsteinEqLambda M C Λ κ T x`; Minkowski + flat solves vacuum EFE (`minkowski4_satisfies_EFE_zero_lambda`); Minkowski + flat forces Λ = 0 (excludes de Sitter on flat); vacuous flat-case second Bianchi; F1 stress-energy type proved; F2 energy conditions (WEC / NEC / SEC / DEC) proved; F7 Penrose statement proved; F8 Raychaudhuri statement proved; B3 / B4 / B6–B9 vacuum-solution proofs for Schwarzschild / FLRW / Kerr on concrete `MetricData` pending |
| 10 | Hypergraph → GR | flat case proved end-to-end; curved case has the obligation Prop attached but the curved bridge theorem is open | Flat bridges proved (cycle → circle, path → interval, 2-torus, d-torus, lattice → Minkowski); every continuum GR target carries an origin-obligation Prop; flat-case witnesses are inhabited; curved-case witnesses are not |

**Grounding-audit status (all four action items closed, 2026-04-23).** Every continuum GR structure in the repository carries a hypergraph-side origin-obligation Prop. See the dedicated table below.

## Core substrate (Rung 0)

- `Hypergraph V`, `Hyperedge V` — directed multi-hyperedges.
- `Rule P`, `IsConservative` predicate (`|LHS| = |RHS|`).
- `Application r H` with `consumed`, `produced`, `result`; size-preservation under conservation.
- `RewritingSystem P`, `Step`, `MultiStep`, `Confluent`, `LocallyConfluent`.
- `Trajectory sys init`, `StepConsistent`, `causallyPrecedes`.
- `CausalLevel` — well-founded level function, same-level antichain.
- `Branchial`, `BranchialRelated`, `NStep`, `BranchialSlice`, `BranchialFinite`.
- `ParallelSchedule` — trajectory-level conservation, in/out-degree balance.

## Discrete calculus and Laplacians (Rung 1)

- `DiscreteCalculus` — `Neighbourhood V`, graph Laplacian Δ, discrete inner product, linearity of Δ, `laplacianLinear` as a `LinearMap`.
- `DiscreteCalculusSymm` — self-adjointness `⟪Δ f, g⟫ = ⟪f, Δ g⟫`, Dirichlet form `⟪f, −Δ f⟫ = ½ ∑(f(w) − f(v))²`, PSD of `−Δ`, `∑ Δ f = 0` (discrete divergence theorem).
- `HypergraphLaplacian` — `laplacianHyper` on directed hyperedges, Dirichlet non-positivity, self-adjointness, per-edge bilinear identity.
- `HypergraphCalculus` — `hyperedgeGradient`, `hypergraphDiv`, `summation_by_parts` (discrete Stokes).
- `SecondDifference` — central second difference, quadratic-case exact identity.
- `CycleGraph` — `cycleLaplacian`, cycle Dirichlet form.
- `LaplacianMatrix` (R2 / D3) — `laplacianMatrixEdge`, `laplacianMatrix`, `laplacianMatrix_mulVec`, `heatKernel t = exp(t · Δ)`, semigroup `heatKernel_add`, `laplacianMatrix_symm`, row-sum zero, `heatTrace`.
- `HeatKernelODE` (T1) — `heatKernel_isHeatSolution`: `exp(t · Δ_H) u₀` satisfies the ODE `u' = Δ u`; `heatKernel_commute_laplacianMatrix`.
- `ExpEigenvector` (T2) — `exp_mulVec_of_eigenvector`: `A.mulVec v = λ v ⇒ exp(A).mulVec v = exp(λ) · v`.

## Cycle spectral machinery (Rung 2)

- `CycleSpectrum` (R5) — `cycleEigenvector n k j = cos(2πkj/n)`, `cycleEigenvalue n k = −4 sin²(πk/n)`, eigenvalue equation at interior and wrap-around.
- `CycleMatrixSpectrum` — matrix-form eigenvalue equation; `heatKernel_cycleHypergraph_mulVec_eigenvector`: each cycle eigenvector decays as `exp(t · λ)`.
- `CycleHasEigenvalue` (T4) — packaged as Mathlib `Module.End.HasEigenvalue`.
- `CycleEigenLimit` (A4) — scaled cycle eigenvalue `n² · (−4 sin²(πk/n)) → −(2πk)²` (continuum circle Laplacian spectrum).
- `CTwoTaylor`, `ScaledDiffC2Bridge` (R1 / A2 / A3) — scaled second difference → `f''` for every `C²` function, via Mathlib `Real.taylor_tendsto`.
- `CycleHeatDecayBounds` — spectral gap, first-mode explicit decay, constant mode fixed.
- `SymmEigenOrthogonal`, `HeatKernelDecay` — eigenvector orthogonality for distinct eigenvalues; pointwise decay of non-constant modes; convergence of linear combinations to the constant component.

## PDE ladder on `Hypergraph V` (Rung 6)

- `HeatEquation` (D1 / D4 / D5) — `u' = Δ_H u`, mass `∑ u` conserved, L² decay.
- `HeatEquationUniqueness` (D2) — `heat_exists`, `heat_unique_forward`.
- `WaveEquation` (D8) — `u'' = Δ_H u`, energy conservation.
- `KleinGordon` (D9) — `u'' = Δ_H u − m² u`, energy + mass.
- `SchrodingerEquation` (D10) — `i ψ' = −Δ_H ψ`, probability `∑|ψ|²` conserved.
- `ScalarField` (G1 / G3 / G4) — Lagrangian + Hamiltonian + Euler-Lagrange; `EL ↔ KG` equivalence.
- `DiscreteDAlembertian` — Benincasa–Dowker 4D operator; `discreteAction`, `discreteEL`; BD conjecture flagged as open Prop obligation.
- `BranchialSchrodinger` (I5) — unitary branchial evolution; `branchialSchrodinger_unitary_evolution`.
- `ContinuumBridgeDemo` — `pde_spectrum_bridge_summary` and `_with_mass`: bundled wave / heat / Schrödinger / KG dispersion relations on cycle → circle.
- `ContinuumLimitStatement` — `DiscreteWaveToContinuumWave`, `DiscreteSchrodingerToContinuumSchrodinger`, `DiscreteKleinGordonSpectrum`, `DiscreteHeatToContinuumHeat` — all proved.

## Continuum-limit bridges (Rungs 1–6)

- `Infra/ScaledCycle` — `cycleDist`, scaled n-cycle metric.
- `Infra/LatticeDensity` — `latticeEmbed`, density, isometry.
- `Infra/Circle` — circle via fundamental domain.
- `Infra/GHBound` — `cycle_circle_gh_bound` at `1/(2n)`.
- `Infra/ScaledPath` — path → interval GH.
- `Infra/ScaledTorus`, `Infra/ScaledTorusD` — 2D / d-D lattice → torus for any `d ≥ 0`.
- `Infra/GHApprox` — abstract `GHApproximation`.
- `Infra/LorentzLattice` — discrete Lorentzian lattice, causal trichotomy, signed Minkowski interval.
- `Infra/Minkowski` — continuum Minkowski with L∞ spatial metric.
- `Infra/ScaledLorentz` — int-to-ℝ scaling, iff preservation of `CausalPrecedes`, `Timelike`.
- `Infra/TrajectoryLorentz`, `Infra/TrajectoryLorentzD` — trajectory → Lorentz-lattice embedding (1+0 and d+1 versions).
- `Infra/FullBridge` — end-to-end `causallyPrecedes → continuum Minkowski` under `LightConeCompatible`.
- `Infra/OllivierStatement`, `Infra/GrayTubeStatement` — correct identity vs Gorard mis-statement, with disagreement proofs on S² (1/6 vs 1/3) and S³ (1/3 vs 2).

## Distance and measure

- `HypergraphDistance` — `Hypergraph.dist`, `geodesicBall`, `geodesicBallVolume`, `localDimension`, `wolframHausdorffDimension`, `plateauDimension`; triangle inequality (T3: `dist_triangle`); cycle connectivity; ball-volume formulas at `r = 0, 1, ≥ n`.
- `HypergraphMeasure` (A5) — `countingMeasure`, `uniformProbability`, `pushforwardCounting`, `pushforwardUniform`; `countingMeasure_univ = |V|`, `uniformProbability_univ = 1`.
- `PathHypergraph` (T5 partial) — `pathHypergraph n` on `Fin n`; free-path spectrum `pathEigenvalue = −4 sin²(kπ/(2n))`, `pathEigenvector = cos(kπ(2j+1)/(2n))`; ground-mode annihilation; spectral gap.
- `PathHypergraphDistance` — path Laplacian row-sum zero, path heat kernel preserves constants.

## Curvature (local-coord, Rung 5)

- `CurvatureLocalCoord` — `MetricData n`, Christoffel symbols with lower-index symmetry; Minkowski Christoffel = 0.
- `CurvatureRiemann` — Riemann, Ricci, Scalar, Einstein tensors; first Bianchi; flat-connection vanishing; `minkowski4_satisfies_vacuum_EFE`; `MetricDataC2`; `leviCivitaConnection`.
- `PartialMetricData` (X1) — metrics with validity domain.
- `CovariantDerivative` (X2) — `nabla_scalar`, `nabla_vector`, `nabla_covector`; flat cases collapse to partials; ℝ-linearity.
- `DiscreteRicci` — Forman-Ricci on graphs and hypergraphs; sign theorems.
- `RicciBridge` — cycle Forman-Ricci = 0 ↔ circle Ricci = 0.
- `CurvedRicciBridge` — `warpedDiag2` curved 2-D witness with `g₁₁ = 1 + x₀²`; non-zero Christoffel on 3-regular graphs.

## GR metric zoo (Rung 5)

Each metric is a fully bundled `MetricData` or `PartialMetricData` with an attached hypergraph-origin obligation inhabited on the flat/existence side.

- `Schwarzschild` — `sgg`, `sginv`, `sdg`; `SchwarzschildValid` exterior predicate; all 8 Christoffels; `schwarzschildPartial M : PartialMetricData 4`; `sgg_lorentzian_pointwise`; `SchwarzschildVacuumObligation M`.
- `FLRW` (B6) — `flrwG a`, `flrwGinv a`, `flrwDg a da`; `flrwPartial a da : PartialMetricData 4`; `FLRWValid a x`; `flrwChristoffel_0_00 = 0`.
- `ReissnerNordstrom` (B8) — `rnLapse M Q r = 1 − 2M/r + Q²/r²`; `rnG`, `rnGinv`; `RNValid`; `rnLapse_schwarzschild` (Q = 0 recovers Schwarzschild).
- `Kerr` (B9) — metric components, `kerrSigma`, `kerrDelta`, `KerrValid`.
- `TwoSphere` — `sphereG`, `sphereGinv`, `sphereDg`, `spherePartial : PartialMetricData 2`; `sphereChristoffel_0_1_1 = -sin θ cos θ`; `sphereChristoffel_1_0_1 = cot θ`.
- `DeSitter` — `dsLapse Λ r = 1 − Λr²/3`, `dsG`, `dsGinv`, `DSValid`; `dsLapse_minkowski`; `dsLapse_pos_iff` cosmological horizon.
- `GRMetricsDemo` — `gr_metric_zoo` bundled theorem exhibiting all six.

## Lorentzian geometry (Rung 8)

- `LorentzianManifold` (E1) — `DiagLorentzianMetric` signature predicate; `DiagLorentzianManifold n`; `minkowski4Manifold`; accessors `g_00_neg`, `g_ii_pos`, `g_off_diag`.
- `CausalGraphType` (IC1) — TR-DAG `CausalGraph V`; `causallyPrecedes` (refl + trans); `ChainOfLength`; `DegenerateInterval`, `OnLightStepFrom`; strong/stable causality; `TimeFunction`; `stablyCausal_implies_stronglyCausal`; causal future/past/light-cone.
- `CausalFoliation` (E5) — `IsAntichain`, `IsFoliation`, `HasProperTime`; `timeFunction_foliation`; `stablyCausal_hasFoliation` (every stably-causal DAG admits a foliation).
- `SpatialReconstruction` (IC5), `EPSAxioms` (IC7), `MarzkeWheeler` (IC8).
- `ProperTimeBounds` — `ChainOfLength` length-0 / length-1 characterisations, concatenation.
- `BranchialCommutator` — `BranchialMultiRelated` (refl+trans closure), symmetry, transitivity.

## Einstein equations (Rung 9)

- `StressEnergyTensor` (F1) — `StressEnergyTensor` type, `.zero`.
- `F2EnergyConditions` — WEC, NEC, SEC, DEC; trivial-zero cases.
- `EinsteinEquations` (F3) — `EinsteinEqLambda M C Λ κ T x`; `minkowski4_satisfies_EFE_zero_lambda`; `einsteinEqLambda_vacuum_iff`; `minkowski4_flat_vacuum_forces_lambda_zero` (excludes Minkowski-as-de-Sitter); `flatConnection_einstein_divergence_zero` (vacuous second Bianchi).
- `F7Penrose` — Penrose singularity theorem as a Prop statement.
- `F8Raychaudhuri` — Raychaudhuri focusing statement.

## Grounding-audit obligation bridges

| Obligation | Binds | Flat-case witness |
|---|---|---|
| `HypergraphMetricOriginObligation M` | `Hypergraph V + RewritingSystem P + Trajectory sys init + scale` | `minkowski4_from_hypergraph_proved`, `schwarzschild_from_hypergraph_proved M`, `flrw_from_hypergraph_proved a da`, `sphere_from_hypergraph_proved`, `warpedDiag2_from_hypergraph_proved` |
| `ConnectionDataOriginObligation C` | `FiberedGraph V W + FiberedGraph.Connection F + scale` | `flatConnection_from_fiberedGraph_proved n`; specialised `flatConnection_minkowski4_from_fiberedGraph` |
| `LorentzianManifoldOriginObligation target` | `CausalGraph V + scale` | `minkowski4Manifold_from_causalGraph_proved` via `trivialCausalGraph` |
| `EFEOriginObligation M C Λ κ T x` | EFE-satisfaction ∧ metric-origin ∧ connection-origin | `minkowski4_flat_vacuum_EFE_originated_global κ` — first complete rule → metric → connection → EFE chain |

Modules: `HypergraphMetricBridges`, `CausalLorentzianBridge`, `FiberedGraphConnectionBridge`, `EinsteinEquationsBridge`, `RuleWitnesses`.

## Rule infrastructure

- `RuleWitnesses` — `identityRule`, `identityApplication_result` (result = H), `identitySystem`, `emptyTrajectory`, `trivialCausalGraph`, `trivialFiberedGraph`, `trivialConnection`.
- `RuleSearch` — decidable `Rule.IsConservative` via `Nat.decEq`; catalog of 5 rules (`identityRule`, `selfMapRule`, `edgeDuplicateRule`, `tripleToEdgeRule`, `pairToTriangleRule`); proved screens `conservativeCatalog_all_conservative`, `growthCatalog_all_non_conservative`; `Rule.GrowthCompatible`; `minkowski4_from_growthRule` uses `edgeDuplicateRule` load-bearingly; `conservative_blocks_dim_geq_one` formalises the structural obstruction.
- `CandidateRuleDatabase` — `CandidateRule P` metadata, `PassesScreens`.
- `RuleSignature` (IR1) — structure `(hausdorffDimAt, ballVolume, totalFormanRicci, edgeCount, vertexCount)`; `hypergraphSignature`; match predicates; `edgeCount_invariant_of_conservative`.
- `RuleSignatureEquiv` — `sigEquiv` (refl / symm / trans).
- `RuleDimensionBounds` (IR2) — `trajectory_size_invariant`, `geodesicBallVolume_le_card`, `trajectory_conservative_ballVolume_bounded`.
- `StructuralRuleBounds` (IR3-IR5) — `ProducesTrees`, `ProducesPlanar`, `IsProductSystem` predicates.

## Branchial quantum mechanics (I-series, IQ)

- `BranchialFinite` (I1) — `branchialSliceFintype`.
- `BranchialHilbert` (I2 / I3 / I4 / I6 / I7) — `BranchialHilbert S := EuclideanSpace ℂ S`; `branchialUniformWeight`; `BranchialAmplitude`; Born rule `bornProbability ψ s := Complex.normSq (ψ s)`; `sum_bornProbability = ‖ψ‖²`; ℂ-linear `branchialAdjLM`; Hermitian self-adjointness `branchialAdjLM_inner`; `BranchialObservable S`; `expectationValue A ψ := ⟨ψ, A ψ⟩`; `expectationValue_real` for Hermitian; `branchialSliceHilbert`.
- `BranchialSchrodinger` (I5) — `branchialSchrodinger_unitary_evolution`: Schrödinger `i ∂_t ψ = A ψ` preserves total probability.
- `BranchialCanonical` — canonical form.
- `FisherMetric` (IQ5) — branchial Fisher metric.
- `FisherMetricExtended` — ℝ-linearity (`_add_left/right`, `_smul_left/right`), PSD (`fisherInner_self_nonneg`).
- `EMETracker` — `EMEPredicate V`, `emeHoldsEverywhere`, edge-count-bounded EME.
- `RemainingObligations` — `FubiniStudyLimitObligation` with proof `fubiniStudyBhattacharyya_bound` (Cauchy–Schwarz / Bhattacharyya); EME and path-integral baselines; IT5 Latschev connectivity; IT6 scale trichotomy endpoints.

## Audit of the Gorard corpus (refutations F1–F7)

| Flaw | Lean module | Substance |
|---|---|---|
| F1 | `Refutations/F1NoMetric` | No canonical hypergraph-to-metric construction |
| F2 | `Refutations/F2Orthonormality` | Fiat orthonormality non-canonical |
| F3 | `Refutations/F3Tautology` | "asymptotic dim preservation ⇒ EFE" = `Iff.rfl` |
| F4 | `Refutations/F4Tautology` | "causal invariance ⇔ general covariance" = `Iff.rfl` |
| F5 | `Refutations/F5Illdefined` | Discrete-to-continuum "becomes" convergence-notion-dependent |
| F6 | `Refutations/F6Circularity` | G3's Poisson-sprinkle-then-reconstruct schema returns its input identically |
| F7 | `Refutations/F7NamedRuleStructure` | 2102.09363 named rule structurally blocked by `\|LHS\| = \|RHS\|` |

Empirical: 2102.09363 named rule shows causal-graph dimension = 1 on every tested seed, in SetReplace and an independent Python re-implementation.

## Infrageometry programme (57 tasks / 9 groups)

| Group | Topic | Lead | Closed | Total | Open items (substantive) |
|---|---|---|---|---|---|
| IA | Infraanalysis | Pavel Hájek | 5 | 5 | — |
| IG | InfraGaugeTheory | Pavel Pokorny | 11 | 11 | IG10 exponential map (needs shortest-path counting) |
| IC | Infracausality | Zapata, Ahmed | 8 | 8 | — |
| IT | Infratopology (VR + Latschev) | Pavel Hájek | 6 | 6 | IT5 GH form, IT6 scale trichotomy bulk |
| ID | Infradimension | — | 7 | 7 | ID6 compatibility, ID7 spectral asymptotics |
| IB | Infrablowup | Hubert Kolcz | 6 | 6 | IB2 commutator theorem |
| IQ | Branchial / quantum | Van Le, Ahmed | 4 | 4 | IQ8 EME tracking functor, IQ9 path-integral amplitudes |
| IS | Synthetic axiomatic | Pokorny | 3 | 3 | — |
| IR | Ruliology | — | 7 | 7 | IR7 reverse-engineering full form |

## Additional key modules (not yet listed above)

- `FiberedGraph`, `Holonomy`, `FiberBundle`, `MultiFibrationProjection` (IG series).
- `VietorisRips`, `HodgeVR`, `HodgeLaplacianSpectrum`, `HodgeLaplacianBounds` (IT series).
- `PlateauDimension`, `HomologyDimension`, `CausalDimension`, `CoordinatizationDimension` (ID series).
- `ElementaryBlowup`, `BlowupOperations`, `BlowupLieAlgebra`, `RadialLaminarBlowup`, `BlowupPoissonConcrete` (IB series).
- `DagBlowup`, `DagCalculus`, `DeRham`, `FormCochainIntegration` (IA series).
- `SyntheticGeometry`, `SyntheticAxiomatic`, `InfrageometricScene` (IS series).

## Research directions on file (cross-collaborator planning)

Tracked as tasks **P1–P19** (catalog in [`RESEARCH_DIRECTIONS.md`](RESEARCH_DIRECTIONS.md)). These are items from Pavel Hájek's weekly update and Discord "core dump" (2025-10-06 to 2026-04-14) not yet formalised here.

- **Simplicial / complex machinery.** P1 Delta and simplicial machinery (face maps, degeneracies, barycentric subdivision, coordinate-squashing); P2 cup product and comparison of two form definitions; P19 hypergraph as (1-skeleton, clique-complex cochain) — Kolpakov direction.
- **Chern-Simons and homotopy algebra.** P3 Discrete Chern-Simons amplitude from Hodge propagator + ribbon graphs + IBL-∞ twist (overlaps M4 Pullman); P17 homotopy-algebra and homological-algebra scaffold.
- **Ribbon structure.** P4 Ribbon (hyper)graph structure + Whitehead moves + amplitudohedron-type representations.
- **Sheaves and cohomology.** P5 Sheaves on hypergraphs, restriction maps, sheaf cohomology, orientation sheaf.
- **Signs and brackets.** P6 Koszul signs / graded Lie bracket on (hyper)graph rewriting; P10 n-Lie / Filippov extension of the insertion bracket (IB4).
- **Multiway and action.** P7 Homotopy colimit of multiway systems (Knill invariants on simplicial sets); P8 filtrations of multiway systems; P9 action principle for rewriting (Carlos Zapata thread).
- **Causal / interaction.** P11 Interaction diagrams from causal graphs; P12 chaos theory (vertical and horizontal).
- **Dual and renormalisation.** P13 Utkarsh Bajaj twisted-difference operators and ring-of-functions reconstruction theorem; P14 blow-up rules as renormalisation-group flow.
- **Geometry.** P16 Knill geodesics approximating Riemannian geodesics (Latschev extension).
- **Physics and tooling.** P18 Holography / Unruh effect discussions; P15 observability tools (flame graph / waterfall).

See [`RESEARCH_DIRECTIONS.md`](RESEARCH_DIRECTIONS.md) for the full item-by-item mapping of Pavel's planning notes to coverage status and task IDs.

## Open items

- Curved rule → curved metric bridges (Schwarzschild / Kerr / FLRW) — no known rewriting rule produces these in the continuum limit; the obligation Props are attached, and the bridge theorems are open.
- Measure-theory: A6 weak convergence counting → Lebesgue, A7 Wasserstein rate `O(1/n)`, A8 d-torus measure lift.
- Bundle machinery (C1–C8): Mathlib gap for Riemannian / Lorentzian vector bundles and Koszul Levi-Civita.
- G2 discrete gauge field via Rung-4 connection.
- E6 Lorentzian Gromov-Hausdorff; E7 discrete-causal → continuum Lorentzian convergence.
- Discrete stress-energy counterpart (F-series continuation).
- H-series: BBH initial data / evolution / Ψ₄ extraction / merger convergence.
- J-series: combined causal + branchial, emergent gravity (Jacobson / Verlinde), AdS/CFT analogs, path integral over causal graphs.
- Empirical rule search via `wolframscript` / SetReplace (infrastructure in place in `RuleSearch.lean`; large-scale enumeration pending).

## Near-term priorities

1. Rule-search pipeline — enumerate small rules via `wolframscript`; compute signatures; feed hits into the `RuleSearch.lean` catalog with signature-property theorems attached. Catalog grows from 5 toward a populated candidate-rule database.
2. Curved-Γ FiberedGraph bridge — extend `FiberedGraphConnectionBridge` from the flat witness to a non-trivial curved `Connection F` approximating Schwarzschild's Γ on a horizon boundary.
3. Measure bridges A6 / A7 / A8.
4. Paper drafts: K1 audit paper, K3 infrageometry continuum-limits paper (R1 / R2 / R5 / A3 / A4 are the technical core).

## Links

- [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md) — item-by-item audit of continuum structures.
- [`STATUS.md`](STATUS.md) — live snapshot with full rung table.
- [`COVERAGE_MAP.md`](COVERAGE_MAP.md) — per-module coverage map.
- [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) — 10-rung ladder.
- [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) — research programme (57 tasks).
- [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) — Gorard F1–F8 flaws with Lean status.
- [`RULE_SEARCH.md`](RULE_SEARCH.md) — rule-search pipeline design.
- [`notes/corpus_assessment.md`](notes/corpus_assessment.md) — per-claim assessment synthesis.
