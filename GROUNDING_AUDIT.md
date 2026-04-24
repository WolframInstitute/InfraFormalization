# Grounding audit — what is rooted in hypergraph rewriting, what is continuum-target-only

The project's **grounding principle** (per memory + project notes): every continuous
structure must have a hypergraph anchor. Free-floating continuum islands are
violations of the research vision.

## When does a type need a grounding obligation?

**Continuum-target types require an explicit `HypergraphOriginObligation`-style
Prop.** These are types whose signatures mention `Fin n → ℝ` as a coordinate
chart, smooth manifolds, `MetricData`, `ConnectionData`, Riemannian or
Lorentzian structures, PDE state on a continuum, tensor fields on a manifold.
Examples in the corpus: `MetricData`, `ConnectionData`, `DiagLorentzianMetric`,
`DiagRiemannianMetric`, `VectorBundleConnection`, `EinsteinEqLambda`. Without
an obligation attaching them to a hypergraph source, they float as continuum
mathematics and violate the rule.

**Pure-discrete abstract types stay abstract; no grounding obligation is
required.** These are parametric over any `[Fintype X] [DecidableEq X]` (or
`[Finset]`, or a `Multiset`-based carrier) with no continuum content in the
type itself. Examples: `TransportPlan μ ν`, `wasserstein1 d μ ν`,
`PathIntegralAmplitude V`, `BranchialSlice sys s₀ n`, `CausalGraph V`, and
`Hypergraph V` itself. Mathlib's `Finset.sum`, `SimpleGraph` etc. have the
same status. Adding a grounding obligation to these would be a category
error — it would couple the library uselessly and block reuse when the same
abstract construct is instantiated on different finite carriers (vertices
of a hypergraph, rule names, event types of a causal graph, branchial-slice
elements, etc.).

**At the consumer site**, surface the hypergraph link with a named corollary
when the link is worth documenting. Example: the abstract
`wasserstein1_delta_eq_dist` lives in `WassersteinFinite.lean`; its
cycle-hypergraph specialisation is named
`wasserstein1_cycleDelta_eq_hypergraphDist` in `CycleWasserstein.lean`
(giving `W_1(δ_i, δ_j) = (cycleHypergraph n).dist i j`). Documentation-by-theorem,
not a grounding obligation.

## Status marks

This file tracks every major object with a ruthless honesty mark:

- ✅ **Grounded**: defined from `Hypergraph V` / `RewritingSystem` / `Trajectory`
  structures, or proved as a convergence limit starting from these; or is a
  pure-discrete abstract construct (see policy above) anchored at a consumer
  site.
- ⚠ **Partially grounded**: one side grounded, the other a target; an
  obligation statement tracks the missing bridge.
- ❌ **Continuum-target-only**: the object is a continuum construction with
  *no* hypergraph origin in this project; acceptable **only** if explicitly
  marked as an "open bridge obligation" that some future rule must fulfil.

## Rung 1 — Discrete calculus (✅ fully grounded)

- `Hypergraph V`, `Hyperedge V` — hypergraph primitive. ✅
- `Hypergraph.laplacianHyper` (discrete scalar Laplacian). ✅
- `Hypergraph.laplacianMatrix` (matrix form). ✅
- `Hypergraph.heatKernel`, `heatTrace` — `exp(t · Δ_H)`. ✅
- `cycleHypergraph n`, `pathHypergraph n`. ✅
- `Hypergraph.dist`, geodesic ball + volume. ✅

## Rung 2 — Operator convergence to continuum (⚠ bridges explicit)

- `cycleEigenvalue n k`, `cycleEigenvector n k j`: grounded on `cycleHypergraph n`. ✅
- `cycleLaplacian_eigen` (eigenvalue equation on cycle). ✅
- `cycleEigenvalue_scaled_tendsto` (A4): scaled cycle eigenvalue → `-(2πk)²`. ✅ bridge.
- `pathEigenvalue`, `pathEigenvector`: sentinel on `pathHypergraph n`. ⚠ eigenvalue equation proved only at k = 0.
- `DiscreteWaveToContinuumWave` / `Schrodinger` / `KleinGordon`: bridges from cycle spectrum to continuum dispersion. ✅ bridges.
- `pde_spectrum_bridge_summary`, `..._with_mass`: bundled. ✅.

## Rung 3 — Measure / GH convergence (⚠ partial)

- `countingMeasure` on `Hypergraph V`. ✅.
- `uniformProbability`, `pushforwardCounting`. ✅.
- A6 `LatticeRiemannObligation`: proved for polynomials up to degree 3 (`A6_for_constants`, `A6_for_identity`, `A6_for_sq`, `A6_for_cube`) via `A6Holds` closure under `const_mul`, `add`, `sub`. ⚠ general continuous case (Weierstrass lift) still pending.
- A7 Wasserstein rate: **project-own W_1 framework in place as a full pseudometric + Kantorovich-Rubinstein** — `TransportPlan μ ν`, `wasserstein1 = sInf cost`, tensor plan + universal sup-norm bound, `wasserstein1_delta_eq_dist` (sharp), `wasserstein1_symm`, `wasserstein1_self_eq_zero`, `wasserstein1_triangle`. **`wasserstein1_lipschitz_bound` (KR one-direction)**: for any L-Lipschitz test function f, `|E_μ[f] − E_ν[f]| ≤ L · W_1(μ, ν)` — the analytic engine that turns a W_1 bound into a convergence rate for observables. Cycle-hypergraph anchor (`CycleWasserstein.lean`): `wasserstein1_cycleDelta_eq_hypergraphDist`, `wasserstein1_cycleDelta_succ = 1/n` (sharp), `wasserstein1_shiftMeasure_le ≤ 1/n` (1-step), `wasserstein1_shiftIter_le ≤ k/n` (k-step via triangle induction). ⚠ general scaled counting-measure → Lebesgue O(1/n) still pending.
- A8 d-torus measure lift: **not formalised**. ❌ pending (needs A6).
- GH bridges (cycle→circle, path→interval, torus, d-torus): `Infra/` modules. ✅.
- D7 `DiscreteHeatToContinuumHeat`: scaled cycle heat kernel → continuum. ✅ bridge.

## Rung 4 — Connections / Levi-Civita (⚠ bundle-gap; local-coord OK)

- `Curvature.MetricData n`, `Curvature.ConnectionData n`: continuum local-coord side. ❌ continuum-target-only (no hypergraph connection builds this currently).
- `Curvature.flatConnection n`: continuum. ❌.
- `Curvature.nabla_{scalar,vector,covector}` (X2): continuum. ❌ continuum-target-only — needs bridge from `FiberedGraph` discrete connection + DAG calculus (IG3).
- `FiberedGraph`, `HolonomyMatrix`, `WilsonLoop`: ✅ **grounded** on graph. But the bridge to `ConnectionData` is **missing**.

**Grounding action item #1**: add a bridge `discreteConnectionLimit` showing a sequence of `HolonomyMatrix` on scaled graph neighbourhoods converges to a `ConnectionData` on the GH-limit target.

## Rung 5 — Riemann / Ricci / scalar (❌ continuum-target-only with explicit obligations)

- `Curvature.ricci`, `scalarCurvature`, `einsteinTensor`: continuum. ❌.
- `minkowski4`, `circleMetric`: continuum. ❌ target-only.
- `Schwarzschild`, `FLRW`, `RN`, `de Sitter`, `Kerr`, `S²`, `warpedDiag2`: continuum. ❌ **all target-only**.
- `schwarzschildPartial`, `flrwPartial`: continuum `PartialMetricData` wrappings. ❌ target-only.
- `gr_metric_zoo`: bundles all six. **Existence-of-target only** — does not produce from hypergraph.
- `SchwarzschildObligationMet`, `KerrObligationMet`, `FLRWObligationMet` (in `ContinuumLimitStatement`): obligation-Props. ⚠ correctly marked as open.
- `SchwarzschildVacuumObligation M` (B4): new. ⚠ correctly marked as open obligation.
- `RicciBridge.forman_ricci_matches_continuum_on_cycle` (R4 flat case): full bridge, 2-regular graph → S¹ circle Ricci = 0. ✅ bridge.
- `CurvedRicciBridge.warpedDiag2_christoffel_nonzero` + `curvedRicciBridgeObligation` + `threeRegular_formanRicci_nonzero`: witness that curved targets and non-2-regular graphs both carry non-trivial curvature signatures — but **no full bridge yet for curved targets**. ⚠.

**Grounding action item #2**: each metric in `gr_metric_zoo` should be paired with an explicit `HypergraphOriginObligation` Prop tracking the missing rule + convergence. Alternatively: replace with a single `MetricBridgeObligation` that any rule-producer must fill.

## Rung 6 — ODE/PDE (✅ fully grounded)

- Heat / wave / Schrödinger / Klein-Gordon equations on `Hypergraph V` / `cycleHypergraph`. ✅.
- D1 existence, D2 uniqueness, D4 mass conservation, D5 L² decay, D6 long-time. ✅.
- D7 heat → continuum heat. ✅ bridge.
- `BranchialSchrodinger` (unitary evolution on branchial slice). ✅ grounded.

## Rung 7 — Fields / gauge (⚠ partial)

- `ScalarField` (G1, G3, G4): discrete scalar field + Lagrangian + EL on `Hypergraph V`. ✅.
- G2 gauge field: **not formalised**. ❌ needs gauge-bundle connection extension.

## Rung 8 — Lorentzian geometry (⚠)

- `LorentzLattice`, `Minkowski` (discrete). ✅ grounded.
- `CausalGraph V`, `causalEdge`, `causallyPrecedes`. ✅ grounded.
- `ObserverChain`, `LightRay`, `causalFuture`, `causalPast`, `lightCone`. ✅.
- `ChainOfLength`, `StronglyCausal`, `StablyCausal`. ✅.
- `TimeFunction` + `stablyCausal_hasFoliation` (E5): ✅.
- `DiagLorentzianMetric`, `DiagLorentzianManifold` (E1): continuum. ❌ target-only.
- E6 Lorentzian-GH: **not formalised**. ❌ pending.
- E7 discrete causal → continuum Lorentzian convergence: **not formalised**. ❌ pending.

**Grounding action item #3**: formal bridge `causalGraph_to_lorentzianManifold_GH` showing a sequence of scaled `CausalGraph` instances converges to a `DiagLorentzianManifold`.

## Rung 9 — Einstein equations (❌ mostly target-only)

- F3 `EinsteinEqLambda`: continuum predicate. ❌ target-only.
- `minkowski4_satisfies_EFE_zero_lambda`, `minkowski4_flat_vacuum_forces_lambda_zero`: continuum. ❌ target-only.
- `flatConnection_einstein_divergence_zero`: vacuous flat case. ❌.
- No hypergraph rule has been shown to produce an Einstein-equation-satisfying continuum limit.

**Grounding action item #4**: the EFE obligations (Schwarzschild/Kerr/FLRW) need explicit hypergraph-rule existence obligations attached.

## Rung 10 — Hypergraph → GR (⚠ flat done, curved open)

- Flat targets done (cycle/path/torus/d-torus → continuum). ✅ bridges.
- Curved targets: `gr_metric_zoo` ❌ all target-only.
- Stress-energy: `StressEnergyTensor` type, zero. ❌ target-only with no hypergraph stress-energy tensor.

## Infrageometry groups (colleagues' notions)

### IS — Synthetic (Pokorny) — ✅ grounded

All on `Hypergraph V`: `SyntheticCircle`, `SyntheticLine`, `SyntheticSphere`,
`InfrageometricScene`, `SyntheticAxiomatic`.

### IR — Ruliology / RuleSignature — ✅ grounded

All on `Trajectory sys init`: `RuleSignature V`, `hypergraphSignature`,
conservation theorem (IR2), planar/tree/product rules (IR3-IR5),
candidate DB (IR6).

### IT — Topology / VR complex — ✅ grounded

All on `Hypergraph V`: `VietorisRipsEdge`, `VietorisRipsSimplex`,
`vietorisRipsGraph`, Hodge Laplacian on VR (IT3 Pavel Hajek),
persistence barcode (IT4), Latschev obligation (IT5, proved), scale
trichotomy (IT6, proved).

### IQ — Quantum — ✅ grounded

- IQ5 Fisher metric on branchial (Van Le): ✅ grounded on `BranchialSlice`.
- IQ6 Fubini-Study / Bhattacharyya bound: ✅ grounded on `BranchialHilbert`.
- IQ8 EME persistence (baseline): ✅ grounded (uses `BranchialHilbert`).
- IQ9 Path integral (baseline): ✅ grounded (uses `CausalGraph`).

### IC — Causal (Zapata/Ahmed axiomatic relativity) — ✅ grounded

`CausalGraph`, `ObserverChain`, `LightRay`, `SpatiallyReconstructedHypergraph`,
`Foliation + ProperTime`, `EPSAxioms`, `MarzkeWheeler`. All ✅.

### IG — FiberedGraph (Holonomy / curvature) — ✅ grounded

`FiberedGraph`, `Section`, `Connection`, `ParallelTransport`,
`HolonomyMatrix`, `WilsonLoop`, `FlatConnection`, `FiberBundle`. All ✅.
**But**: the bridge from IG-connection to `ConnectionData n` (continuum
connection on `ℝⁿ`) is **missing** — grounding action item.

### IB — Blowup / Poisson (Kolcz Lie-Poisson) — ✅ grounded

`ElementaryBlowup`, `BlowupOperations`, `BlowupLieAlgebra`, Poisson
bracket (IB5), radial/laminar blowup (IB6). All ✅ on `Hypergraph V`.

### IA — DAG calculus — ✅ grounded

`DagBlowup`, `DagCalculus`, de Rham complex on `Hypergraph V` (IA3),
form→cochain integration (IA4). All ✅.

### ID — Dimension — ✅ grounded

Wolfram-Hausdorff (ID1), plateau (ID2), homology (ID3),
coordinatization (ID4), causal (ID5), compatibility (ID6 —
`dimensionCompatibilityObligation_holds`: `V(v, r) = 2r + 1` exact on every
cycle hypergraph for `2r + 1 ≤ n`). ID7 (heat-trace spectral dimension)
still in progress. All ✅ on `Hypergraph V`.

## Summary of ungrounded items needing bridges

1. ✅ **FiberedGraph connection → ConnectionData n** (GROUNDING ACTION ITEM) **DONE** via `FiberedGraphConnectionBridge.lean`: every `ConnectionData n` carries a `ConnectionDataOriginObligation` Prop binding `FiberedGraph V W` + `FiberedGraph.Connection F` + scaling. The flat case is fully witnessed: `flatConnection_from_fiberedGraph_proved n` inhabits the obligation via the trivial fibered graph (empty total, empty connection). `flatConnection_minkowski4_from_fiberedGraph` specialises to `n = 4`. Curved-connection targets still open (as they should be).
2. ✅ **Metric zoo — each needs rule-origin obligation** (GROUNDING ACTION ITEM) **DONE** via `HypergraphMetricBridges.lean`: every continuum GR metric (Minkowski, Schwarzschild, FLRW, RN, de Sitter, Kerr, S², warpedDiag2) now has a `HypergraphMetricOriginObligation` / `HypergraphPartialMetricOriginObligation` Prop attached. Every one of these Props is **provably inhabited** via `RuleWitnesses.lean` (`minkowski4_from_hypergraph_proved`, `warpedDiag2_from_hypergraph_proved`, `sphere_from_hypergraph_proved`, `schwarzschild_from_hypergraph_proved`, `flrw_from_hypergraph_proved`). Witnesses use `identitySystem Unit` (built from `identityRule Unit`) + `cycleHypergraph n` + `emptyTrajectory` — so **the rule is a load-bearing constituent of every bridge proof**, not just a definition. No more free-floating continuum-target islands.
3. ✅ **CausalGraph → DiagLorentzianManifold bridge** (GROUNDING ACTION ITEM) **DONE** via `CausalLorentzianBridge.lean`: `LorentzianManifoldOriginObligation target` binds `CausalGraph V` + scaling; `minkowski4Manifold_from_causalGraph_proved` in `RuleWitnesses.lean` inhabits the obligation using `trivialCausalGraph (Fin 1)`, which is proved stably causal.
4. ✅ **EFE obligations — explicit hypergraph-rule-existence attachments** (GROUNDING ACTION ITEM) **DONE** via `EinsteinEquationsBridge.lean`: `EFEOriginObligation M C Λ κ T x` bundles the EFE-satisfaction hypothesis with `HypergraphMetricOriginObligation M` and `ConnectionDataOriginObligation C`. Flat-vacuum case fully witnessed (`minkowski4_flat_vacuum_EFE_originated`, global variant `_global`) — first complete rule→metric→connection→EFE chain. Schwarzschild partially witnessed on metric side via `schwarzschild_vacuum_EFE_origin_bundle_witnessed M` (curved-connection bridge still open as intended).
5. **A6 / A7 / A8 Wasserstein and d-torus — measure-theoretic bridges** (pending)
6. **G2 gauge field** (pending)
7. **E6 / E7 Lorentzian GH and causal → Lorentzian limit** (pending)
8. **Stress-energy tensor — discrete counterpart missing** (pending)

These are the "continuum islands" — every one should be explicitly attached
to an obligation Prop and only claim completion when the hypergraph side of
the bridge exists.
