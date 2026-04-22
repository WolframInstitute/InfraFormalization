# Status snapshot

Live document: what's proved, what's in progress, where we are on the
research programme ([`INFRAGEOMETRY.md`](INFRAGEOMETRY.md),
[`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md),
[`MILESTONES.md`](MILESTONES.md),
[`COVERAGE_MAP.md`](COVERAGE_MAP.md)).

**Single source of truth for coverage:** [`COVERAGE_MAP.md`](COVERAGE_MAP.md).
Protocol: on every commit, task completion, or new obligation, both
the task system and the coverage map are updated.

## Machine-verified theorems (axiom-clean)

**200+ `#print axioms` certifications** in
[`lean/InfraFormalization/AxiomCheck.lean`](lean/InfraFormalization/AxiomCheck.lean),
all depending only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). No `sorry`, no
`native_decide`, no `decide`, no custom axioms.

## Infrageometry program — task counters (current)

From [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md), 9 task groups with 57 items:

| Group | Done | Total |
|---|---|---|
| IA — Infraanalysis | 1 | 5 |
| IG — InfraGaugeTheory | 7 | 11 |
| IC — Infracausality | 5 | 8 |
| IT — Infratopology | 1 | 6 |
| ID — Infradimension | 2 | 7 |
| IB — Infrablowup | 1 | 6 |
| IQ — Branchial/QM | 1 | 4 |
| IS — Synthetic axiomatic | 1 | 3 |
| IR — Ruliology | 2 | 7 |
| **Total** | **21** | **57** (37%) |

Plus 14 legacy-group tasks (A1, B1, D1/4/5/8/9/10, G1/3/4, I1 = 12
directly; F1–F5 refutations = 5 more as theorem + axiom-clean).

**Concrete bridge extensions added post-initial-completion** (R-series
real-work items):

| R# | Theorem | Status |
|---|---|---|
| R1 | C² Taylor convergence of scaled second difference | ✅ (`CTwoTaylor.lean`) |
| R2 | laplacianMatrix + heatKernel via Matrix.exp | ✅ (`LaplacianMatrix.lean`) |
| R3 | ℓ²(BranchialSlice) as Hilbert space | ✅ partial (`BranchialHilbert.lean`: finite-dim ℂ-Hilbert alias, ℂ-linear adjacency operator + Hermitian self-adjointness for symmetric adj; + Born-rule `bornProbability` (I3) + uniform `branchialUniformWeight` (I2) + concrete slice `branchialSliceHilbert`) |
| R4 | Curved discrete-Ricci convergence beyond flat | pending |
| R5 | Cycle Laplacian spectrum closed form | ✅ (`CycleSpectrum.lean`; full wrap-around version) |

Plus additional proved legacy items: A2, A3, A4, D3.

## Rungs of the bridge ladder (see `BRIDGE_MACHINERY.md`)

| Rung | Topic | Status |
|---|---|---|
| 1 | Discrete calculus | ✅ graph Laplacian, inner product, self-adjointness, Dirichlet form, PSD, divergence theorem, Laplacian-as-LinearMap, cycle instance; matrix form + heat kernel via `Matrix.exp` (R2/D3), symmetric Laplacian matrix, row-sum zero, heat trace; **`Hypergraph.dist` triangle inequality + cycle connectivity (T3)** |
| 2 | Op. convergence to continuum | ✅ C² Taylor convergence of scaled second difference (R1/A2); ✅ scaled discrete → continuum f'' for all C² (A3); ✅ cycle spectrum closed form (R5) + eigenvalue → continuum (A4); **cycle spectrum in `HasEigenvalue` form (T4)**; **exp fixes eigenvectors (T2)** |
| 3 | Measure limits | ✅ counting measure + pushforward (A5); ⌛ weak convergence (A6), Wasserstein (A7) still pending |
| 4 | Connections / Levi-Civita | ⌛ Mathlib gap; local-coord route planned |
| 5 | Riemann / Ricci / scalar | ⌛ blocked by Rung 4; statement-only for Ollivier / Gray |
| 6 | ODE/PDE | ✅ discrete heat equation (D1/D4/D5) + existence/uniqueness (D2 forward-time); wave (D8); Klein-Gordon (D9); Schrödinger unitarity (D10); scalar field Lagrangian/EL (G1/G3/G4); **ODE ↔ matrix heat kernel unified (T1)**; matrix-level mass/L²/semigroup corollaries; **long-time heat decay of non-constant cycle modes (D6 partial, `HeatKernelDecay.lean`)** |
| 7 | Fields / gauge | Far |
| 8 | Lorentzian geometry | ✅ discrete (`LorentzLattice`, `Minkowski`); ⌛ continuum Lorentzian missing in Mathlib |
| 9 | Einstein equations | Far |
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

### Branchial skeleton (QM bridge groundwork)
- ✅ `BranchialRelated`, `NStep`, `BranchialSlice` + slice recursion (`Branchial.lean`).
- ✅ Finite-slice condition I1 (`BranchialFinite.lean`), ℓ²(slice) Hilbert space I4/R3 partial (`BranchialHilbert.lean`: ℂ-Hilbert + ℂ-linear adjacency + Hermitian).
- ✅ Branchial amplitudes I3 + Born rule (`BranchialHilbert.lean`), uniform branchial measure I2 (`branchialUniformWeight`).
- ⌛ I5 unitary evolution `exp(i·t·A)`; I8 Hilbert-space continuum limit; IQ6 FS←Fisher limit.

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
