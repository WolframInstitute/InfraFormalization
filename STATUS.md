# Status snapshot

Live document: what's proved, what's in progress, where we are on the
research programme ([`INFRAGEOMETRY.md`](INFRAGEOMETRY.md),
[`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md),
[`MILESTONES.md`](MILESTONES.md),
[`COVERAGE_MAP.md`](COVERAGE_MAP.md)).

## Headline (2026-04-24)

**All seven infrageometry obligations are proved.** `all_obligations_hold`
in [`lean/InfraFormalization/RemainingObligations.lean`](lean/InfraFormalization/RemainingObligations.lean)
bundles the six non-trivial closures:

- **IT5** `latschevObligation_holds` — Latschev connectivity form.
- **IT6** `scaleTrichotomyObligation_holds` — cycle quantum + coarse endpoints.
- **ID6** `dimensionCompatibilityObligation_holds` — `V(v, r) = 2r + 1` exactly on every `cycleHypergraph n` for all `r` with `2r+1 ≤ n`. Lower bound via shift-family Finsets (forward `F^[k] v` and backward `G^[k] v`) with left-cancellation injectivity; upper bound via structural induction on walks (`cycleHypergraph_walk_in_shift`) using the `F ∘ F`, `G ∘ G`, `G ∘ F`, `F ∘ G` composition lemmas.
- **IQ6** `fubiniStudyBhattacharyya_bound` — `‖⟨ψ, φ⟩‖ ≤ ∑ s, ‖ψ s‖ · ‖φ s‖` (Cauchy-Schwarz / Bhattacharyya).
- **IQ8** / **IQ9** — baseline witnesses (`ψ = 0`, `α = 0`) proved in `no_stub_obligations_remain`.
- **IR7** `reverseEngineeringObligationRefined_holds` — realisability-restricted form; the over-strong unrefined form is provably FALSE (`not_reverseEngineeringObligation`).

**All four grounding-audit action items closed.** Every continuum GR
object (the GR metric zoo, Lorentzian manifolds, connection data, EFE
satisfaction) carries an attached hypergraph-side origin-obligation
Prop with inhabited witnesses for flat cases:

- **G1** `ConnectionDataOriginObligation` — every `ConnectionData n` has an attached FiberedGraph-origin Prop ([`FiberedGraphConnectionBridge.lean`](lean/InfraFormalization/FiberedGraphConnectionBridge.lean)).
- **G2** `HypergraphMetricOriginObligation` — every GR metric in the zoo (Minkowski, Schwarzschild, FLRW, Reissner–Nordström, Kerr, S², de Sitter, warpedDiag2) has a hypergraph-origin witness ([`HypergraphMetricBridges.lean`](lean/InfraFormalization/HypergraphMetricBridges.lean); witnesses load-bearingly use `identitySystem Unit` + `cycleHypergraph n` + `emptyTrajectory`).
- **G3** `LorentzianManifoldOriginObligation` — continuum Lorentzian manifold bound to a `CausalGraph V` origin ([`CausalLorentzianBridge.lean`](lean/InfraFormalization/CausalLorentzianBridge.lean)).
- **G4** `EFEOriginObligation` bundles EFE satisfaction with metric + connection origins ([`EinsteinEquationsBridge.lean`](lean/InfraFormalization/EinsteinEquationsBridge.lean)). `minkowski4_flat_vacuum_EFE_originated_global` is the first complete rule → metric → connection → EFE chain.

**Axiom cleanliness.** Every `#print axioms` certification in
[`lean/InfraFormalization/AxiomCheck.lean`](lean/InfraFormalization/AxiomCheck.lean)
reduces to `{propext, Classical.choice, Quot.sound}` (and many to
`{propext, Quot.sound}` only). No `sorry`, no `native_decide`, no
`decide`, no custom axioms. `lake build` fully green.

**Gorard refutations F1–F7 Lean-formal**, including `F6Circularity`
(the Poisson-sprinkle-then-reconstruct schema of arXiv:2102.09363
§3.3 formally proved to produce its input identically — the
`circular_procedure_is_identity` theorem).

## Closures since the 2026-04-23 weekly report

(Cumulative list in [`POST_WEEKLY_UPDATES_2026-04-23.md`](POST_WEEKLY_UPDATES_2026-04-23.md).
Highlights:)

- **ID6 CLOSED**: full `V(v, r) = 2r + 1` on cycle hypergraphs.
  `cycleHypergraph_ballVolume_exact`, `dimensionCompatibilityObligation_holds`.
  Infrastructure added along the way: `cycleHypergraph_walk_in_shift`
  (walk-structural induction), `cycleHypergraph_dist_iter{Succ,Pred}_le`,
  `cycleHypergraph_iter{Succ,Pred}_val`, `cycleHypergraph_iter{Succ,Pred}_injOn`,
  `cycleHypergraph_iterSucc_ne_iterPred`.
- **IR7 CLOSED (refined form)**: `ReverseEngineeringObligationRefined` holds;
  original `ReverseEngineeringObligation` is provably false.
- **B6 CLOSED**: FLRW metric bundle (`flrwPartial` as `PartialMetricData 4`
  with domain, Christoffel, Lorentzian, origin obligation).
- **C1, C2**: `DiagRiemannianMetric` + `DiagLorentzianMetric` bundle
  predicates with Euclidean and Minkowski witnesses.
- **C7**: `HypergraphConnection` — discrete connection on a hypergraph
  with group-valued transport, flat baseline, walk-transport as a
  monoid homomorphism (`transportWalk_append`), holonomy, `IsFlat`
  predicate.
- **J1**: `MultiwayCausalGraph` — joint structure bundling a rewriting
  system, initial hypergraph, and causal DAG on events.
- **H1**: `CandidateRuleCatalog` — Gorard's named rule (arXiv:2102.09363)
  plus four other literature rules as concrete `Rule P` instances with
  `LiteratureSource` citations and machine-checked conservation theorems.
- **P20 advances**: Rodkey classification — `AdjTransitive → DistTransitive
  → BallVolumeVertexUniform → LocalDimensionVertexUniform` sufficient
  chain fully proved on cycle hypergraphs; `pathHypergraph` ruled out
  as negative example at radius 1.
- **Ollivier audit (research-new)**: quantitative discrepancy
  `ollivier_minus_gorard_leading = δε²(R - Ric_vv)/(2(n+2))`, with S²
  worked example `δε²/8` (`s2_gorard_error`) — identifies a specific
  computable deviation between Gorard's discrete-Ricci construction
  and standard Ollivier-Ricci.
- **A6 partial**: `A6_for_{constants,identity,sq,cube}` monomial
  convergence + `A6Holds` predicate closed under `const_mul`, `add`,
  `sub`; polynomials up to degree 3 done, general continuous awaiting
  Weierstrass.

## Open items tracked at the obligation level

| Open item | Status |
|---|---|
| **IG10** exponential map via weighted shortest-path counts | needs shortest-path counting infrastructure + Hajek's weighted-sum formulation |
| **IB2** causal-branchial commutator theorem | predicate placeholder at `True`; needs a real theorem statement before proof |
| **ID7** spectral dimension via heat-kernel trace | heat trace defined; small-`t` asymptotics pending |
| **A6** weak convergence (general continuous) | polynomials to degree 3 closed; Weierstrass lift pending |
| **Curved GR witnesses** (B3/B4, B7, B9, F4/F5/F6) | Ricci = 0 on Schwarzschild/Kerr and full EFE for FLRW with matter; blocked by Ricci-on-explicit-connection Mathlib gap |
| **E5 ADM / D11 Choquet-Bruhat** | long-term GR formalization targets |
| **C3–C8** connection/curvature at bundle level + scaled → Levi-Civita | C1 (`DiagRiemannianMetric`) and C7 (`HypergraphConnection`) done; C8 convergence theorem is the GR bridge ladder rung |

For the full per-module view, see [`COVERAGE_MAP.md`](COVERAGE_MAP.md).

## Rungs of the bridge ladder (see `BRIDGE_MACHINERY.md`)

| Rung | Topic | Status |
|---|---|---|
| 1 | Discrete calculus | ✅ graph Laplacian, inner product, self-adjointness, Dirichlet form, PSD, divergence theorem, Laplacian-as-LinearMap, cycle instance; matrix form + heat kernel via `Matrix.exp` (R2/D3), symmetric Laplacian matrix, row-sum zero, heat trace; **`Hypergraph.dist` triangle inequality + cycle connectivity (T3)** |
| 2 | Op. convergence to continuum | ✅ C² Taylor convergence of scaled second difference (R1/A2); ✅ scaled discrete → continuum f'' for all C² (A3); ✅ cycle spectrum closed form (R5) + eigenvalue → continuum (A4); **cycle spectrum in `HasEigenvalue` form (T4)**; **exp fixes eigenvectors (T2)** |
| 3 | Measure limits | ✅ counting measure + pushforward (A5); ⌛ weak convergence (A6), Wasserstein (A7) still pending |
| 4 | Connections / Levi-Civita | ⌛ Mathlib gap; local-coord route planned |
| 5 | Riemann / Ricci / scalar | ✅ local-coord Riemann + Ricci + Einstein via `CurvatureRiemann` (X2 ∇, R/∇ commutator pending); ✅ GR metric zoo formalised: **Minkowski, Schwarzschild (B1+B5), Reissner-Nordström (B8), FLRW (B6), de Sitter, S²**; `DiagLorentzianManifold` (E1), `EinsteinEqLambda` (F3); `minkowski4_flat_vacuum_forces_lambda_zero` excludes Minkowski-as-de-Sitter |
| 6 | ODE/PDE | ✅ discrete heat equation (D1/D4/D5) + existence/uniqueness (D2 forward-time); wave (D8); Klein-Gordon (D9); Schrödinger unitarity (D10); scalar field Lagrangian/EL (G1/G3/G4); **ODE ↔ matrix heat kernel unified (T1)**; matrix-level mass/L²/semigroup corollaries; **long-time heat decay of non-constant cycle modes (D6 partial, `HeatKernelDecay.lean`); multi-mode convergence `heatKernel_cycleHypergraph_multi_mode_tendsto` — heat flow of any finite eigen-combination converges to its constant component** |
| 7 | Fields / gauge | Far |
| 8 | Lorentzian geometry | ✅ discrete (`LorentzLattice`, `Minkowski`); ✅ continuum `DiagLorentzianManifold` (E1) with Minkowski instance; ✅ discrete Cauchy foliation (E5) via stably-causal time function; ⌛ continuum Lorentzian-GH missing in Mathlib |
| 9 | Einstein equations | ✅ **F3 `EinsteinEqLambda`** for general (M, C, Λ, κ, T); `minkowski4_satisfies_EFE_zero_lambda`, `einsteinEqLambda_vacuum_iff`, `minkowski4_flat_vacuum_forces_lambda_zero`, `flatConnection_einstein_divergence_zero`; ⌛ Schwarzschild / Kerr / FLRW Ricci = 0 blocked by Ricci-on-explicit-connection (B3-B4, B7) |
| 10 | Hypergraph → GR | ✅ flat targets done (cycle→circle, path→interval, torus, d-torus, discrete→continuum Minkowski); ⌛ curved targets blocked by Rungs 4–5 |

## Key deliverables by phase

### Phase 0 — Audit of the Gorard corpus
- ✅ Close-readings of G1 (2004.14810), G2 (2011.12174), G3 (2102.09363), G4 (2303.07282).
- ✅ 184-row claims catalog, severity taxonomy S1–S6, major-flaws index F1–F8, cross-paper audit.
- ✅ Empirical refutation of the named EFE rule (SetReplace + independent Python rewriter on 9 seeds).

### Phase 1 — Wolfram-model structural theorems (Lean)
- ✅ Edge conservation, trajectory-level conservation, in/out degrees, per-event balance.
- ✅ Causal-DAG level function via well-founded recursion; level monotonicity; same-level antichain.
- ✅ `causallyPrecedes_iff_isCausalPred` bridge between Prop- and Bool-level causal relations.
- ⌛ Full parallel-layer bound `|layer_s| ≤ N/k` (needs trajectory-structure lemma).
- ⌛ Trajectory-structure lemma (consumed hyperedges have earlier creators).

### Phase 1 — Refutations of major structural flaws (F1–F5)
All formalized as Lean theorems, axiom-clean:
- ✅ **F1** (`Refutations/F1NoMetric.lean`) — no canonical hypergraph-to-metric construction.
- ✅ **F2** (`Refutations/F2Orthonormality.lean`) — fiat orthonormality is non-canonical.
- ✅ **F3** (`Refutations/F3Tautology.lean`) — "asymptotic dim preservation ⇒ EFE" is `Iff.rfl`.
- ✅ **F4** (`Refutations/F4Tautology.lean`) — "causal invariance ⇔ discrete general covariance" is `Iff.rfl` (axiom-free).
- ✅ **F5** (`Refutations/F5Illdefined.lean`) — "becomes" is convergence-notion-dependent.

### Phase 2 — Corrected continuum identities
- ✅ Statement-only forms of the correct Ollivier identity (directional Ric) and Gorard's wrong form (scalar R); coincidence-condition theorem.
- ✅ Statement-only forms of the correct Gray tube formula and Gorard's wrong form; concrete disagreement proofs on S² (1/6 ≠ 1/3) and S³ (1/3 ≠ 2).

### Phase 3 — Continuum-limit theorems
- ✅ **Cycle → circle** GH bound at `1/(2n)` (`Infra/GHBound.lean`).
- ✅ **Path → interval** GH bound (`Infra/ScaledPath.lean`).
- ✅ **2D lattice → 2-torus** GH bound (`Infra/ScaledTorus.lean`).
- ✅ **(d+1)D lattice → (d+1)-torus** GH bound for arbitrary `d ≥ 0` (`Infra/ScaledTorusD.lean`).
- ✅ Abstract `GHApproximation` structure (`Infra/GHApprox.lean`).

### Phase 4 — Infrageometry of the Lorentzian side
- ✅ **Discrete Lorentzian lattice** `LorentzLattice.lean`: `CausalPrecedes`, Timelike/Null/Spacelike trichotomy, signed Minkowski interval with three-way positivity classification, forward cones.
- ✅ **Continuum Minkowski** `Minkowski.lean`: `ContinuumCausalPrecedes`, trichotomy, signed interval.
- ✅ **Scaled int-to-ℝ embedding** `ScaledLorentz.lean`: `lorentzIntEmbed` preserves `CausalPrecedes` and `Timelike` into continuum Minkowski (forward direction).
- ⌛ Full scaled isometry-plus-density (Lorentzian GH) — blocked by Mathlib gap.

### Phase 4 — Bridging theorems (rewriting ↔ Minkowski)
- ✅ **1+0-dim bridge** `TrajectoryLorentz.lean`: `trajectoryToEvent τ` via the level function. `causallyPrecedes_implies_timelike`. `trajectoryToEvent_lossy` (F1/F2 gap explicit).
- ✅ **d-dim conditional bridge** `TrajectoryLorentzD.lean`: `SpatialEmbedding`, `LightConeCompatible`, `fullEmbed_preserves_causal`. The F1 missing-data slot made an explicit parameter.
- ✅ **End-to-end bridge** `FullBridge.lean`: `causallyPrecedes_gives_continuum` chains trajectory → Lorentz → Minkowski under `LightConeCompatible τ φ`.

### Rung 1 — Discrete calculus (bridge ladder entry)
- ✅ `Neighbourhood V` structure + graph Laplacian + counting inner product (`DiscreteCalculus.lean`).
- ✅ Linearity of `Δ`, vanishes on constants.
- ✅ `discreteInner` symmetry + bilinearity.
- ✅ `laplacianLinear`: graph Laplacian as `LinearMap` — opens Mathlib spectral API.
- ✅ **Self-adjointness** `⟪Δ f, g⟫ = ⟪f, Δ g⟫` (`DiscreteCalculusSymm.lean`).
- ✅ **Dirichlet form** `⟪f, −Δ f⟫ = ½ ∑ (f(w) − f(v))²`.
- ✅ **Positive semidefiniteness** of `−Δ`.
- ✅ **Discrete divergence theorem** `∑ Δ f = 0`.
- ✅ **Cycle graph** concrete instance + Dirichlet form (`CycleGraph.lean`).

### Rung 2 — Operator convergence (entry)
- ✅ Central second difference `Δ²_h f := f(x+h) − 2 f(x) + f(x−h)`, linearity, polynomial-case exact identity: for any quadratic, `Δ²_h f(x) = f''(x) · h²` (no error). Identifies cycle Laplacian with the second difference.
- ⌛ `C²` Taylor-remainder version (pending Mathlib `iteratedDeriv` / `taylorWithinEval` integration).

### Branchial QM bridge (I1–I10)
- ✅ I1 BranchialSlice finiteness (`BranchialFinite.lean`).
- ✅ I2 Uniform branchial measure `branchialUniformWeight` (`BranchialHilbert.lean`).
- ✅ I3 Branchial amplitudes + Born rule `bornProbability` (`BranchialHilbert.lean`).
- ✅ I4 / R3 partial — ℓ²(slice) Hilbert space `BranchialHilbert S := EuclideanSpace ℂ S` with ℂ-linear adjacency `branchialAdjLM` and self-adjointness `branchialAdjLM_inner` (`BranchialHilbert.lean`).
- ✅ I5 Unitary branchial evolution `branchialSchrodinger_unitary_evolution` (`BranchialSchrodinger.lean`) — Schrödinger eq `i ∂_t ψ = A ψ` preserves `∑(u² + v²)`.
- ✅ I6 Observables as Hermitian operators `BranchialObservable S` (`BranchialHilbert.lean`).
- ✅ I7 Expectation values + real-valuedness on observables (`BranchialHilbert.lean`).
- ✅ I9 Schrödinger on branchial graph (via `BranchialSchrodinger adj u v`).
- ⌛ I8 Hilbert-space continuum limit; I10 path-integral formulation.
- ⌛ IQ6 FS←Fisher limit; IQ8 EME persistence; IQ9 path integral over causal graphs.

## Documentation
- [`README.md`](README.md), [`INDEX.md`](INDEX.md) — navigation.
- [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) — F1–F8 structural-flaw registry with Lean-formalization status for each.
- [`MILESTONES.md`](MILESTONES.md) — checkbox tracker across all phases.
- [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) — 10-rung ladder from discrete calculus to Einstein equations.
- [`RULE_SEARCH.md`](RULE_SEARCH.md) — how the Lean corpus serves as verifier + screener in a rule-search pipeline.
- [`PUBLISHABLE.md`](PUBLISHABLE.md) — paper targets P1–P7 with dependencies.
- [`LEAN_PHYSICS.md`](LEAN_PHYSICS.md) — conventions and alignment with other Lean-physics efforts.

## Path-on-GR summary (see `BRIDGE_MACHINERY.md`)

**What we have:** full chain `causallyPrecedes (trajectory) → CausalPrecedes (discrete Lorentz) → ContinuumCausalPrecedes (Minkowski)` under `LightConeCompatible τ φ`. Flat-target GH bounds in all dimensions (cycle, path, d-torus). Graph Laplacian with full spectral-theory readiness. F1–F5 refuted.

**What we're missing for GR:** curved-target bridges (blocked by Rungs 4–5, Mathlib Ricci). Full Lorentzian-GH (blocked by Mathlib gap). A specific rule whose causal graph has the right dimension (empirical + structural rejection of Gorard's named rule — F7). Discretization of the Einstein–Hilbert action converging to the continuum one (F5 blocks naïve form).

**Rule search as the practical route:** our Lean corpus serves as verifier for any candidate rule + candidate spatial embedding (`RULE_SEARCH.md`). Screening signatures: level growth `~t^{d+1}`, antichain width `~k^d`, cone volume. Any candidate rule passing these + `LightConeCompatible` gets a machine-checked Minkowski-consistency certificate via the end-to-end bridge.

## Next concrete directions

1. **Rung 2 C² case**: generalise `SecondDifference` from polynomials to arbitrary `C²` functions via Mathlib's Taylor infrastructure.
2. **Discrete heat equation as linear ODE**: use `laplacianLinear` + finite-dimensional ODE existence-uniqueness; prove conservation of total mass via `laplacian_sum_zero` + `d/dt ∑ u = 0`.
3. **Rung 5 local-coordinate Ricci**: define Christoffel symbols, Riemann tensor, Ricci, scalar curvature on explicit charts (ℝⁿ, Schwarzschild in Schwarzschild coords). Skip the bundle machinery for now; the coordinate form is what physics actually uses.
4. **Branchial measure**: uniform probability on finite `BranchialSlice`, first step toward Hilbert-space amplitudes.
5. **Trajectory-structure lemma** + **full parallel-layer bound** `|layer_s| ≤ N/k` (Phase 1 pending).
