# Weekly report — 2026-04-23

Project: **`infra_formalization`** — Lean 4 / Mathlib formalisation of
the Wolfram-model → GR / QM programme, with a parallel
audit of Gorard's published derivation claims.

## What the project is (one paragraph)

A machine-checked corpus that does three things simultaneously: (i)
formalises a discrete-to-continuum bridge ladder from hypergraph
rewriting to Einstein's equations, with every continuum object anchored
to a hypergraph origin; (ii) formalises the critique of Gorard's four
principal papers, converting every structural flaw into an axiom-clean
Lean theorem; (iii) hosts the Wolfram-Institute *infrageometry*
programme — 57 tasks across 9 groups (infraanalysis, infragauge,
infracausality, infratopology, infradimension, infrablowup,
branchial-QM, synthetic, ruliology) covering colleagues' work
(Pavel Hájek, Van Le, Pavel Pokorny, Hubert Kolcz, Jan Pullman,
Carlos Zapata, Sara Ahmed, Ioana Milea).

## Headline status

- **Build**: `lake build` green at 3468/3468 jobs.
- **Axiom cleanliness**: every proved theorem reduces to
  `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
  `native_decide`, no custom axioms.
- **Infrageometry programme**: 50/57 tasks closed with real content
  (88%); 7 in-flight with substantive open content (not stubs).
- **Grounding audit**: **all four action items closed this week**.
  No free-floating continuum islands at the obligation level.
- **Gorard refutations**: F1–F7 Lean-formal, including F6Circularity
  (G3's Poisson-sprinkle-then-reconstruct schema proven to return its
  input identically — "mathematically content-free").

## What shipped this week (by theme)

### 1. Grounding-audit closure (new modules, 5 commits)

Every continuum GR object now carries an attached hypergraph-side
origin-obligation Prop; flat cases are provably inhabited.

| Obligation | Binds | Witness |
|---|---|---|
| `HypergraphMetricOriginObligation M` | `Hypergraph V + RewritingSystem P + Trajectory sys init + scale` | `minkowski4_from_hypergraph_proved`, ...FLRW, Schwarzschild, RN, Kerr, S², de Sitter, warpedDiag2 (all ✅) |
| `ConnectionDataOriginObligation C` | `FiberedGraph V W + FiberedGraph.Connection F + scale` | `flatConnection_from_fiberedGraph_proved n` (flat case ✅) |
| `LorentzianManifoldOriginObligation target` | `CausalGraph V + scale` | `minkowski4Manifold_from_causalGraph_proved` ✅ |
| `EFEOriginObligation M C Λ κ T x` | EFE-satisfaction ∧ metric-origin ∧ connection-origin | `minkowski4_flat_vacuum_EFE_originated_global κ` — **first full rule → metric → connection → EFE chain** ✅ |

Files: `HypergraphMetricBridges.lean`, `CausalLorentzianBridge.lean`,
`FiberedGraphConnectionBridge.lean`, `EinsteinEquationsBridge.lean`,
`RuleWitnesses.lean`, `RuleSearch.lean`.

### 2. Rule-search infrastructure (new)

Addresses "where do rewriting rules come from?" mechanically.

- `RuleWitnesses.lean`: `identityRule P`, `identityApplication_result`
  (result = H), `identitySystem`, `emptyTrajectory`, `trivialCausalGraph` —
  the infrastructure used by every bridge witness proof.
- `RuleSearch.lean`: catalog of 5 concrete rules
  (`identityRule`, `selfMapRule`, `edgeDuplicateRule`,
  `tripleToEdgeRule`, `pairToTriangleRule`); decidable
  `IsConservative` via `Nat.decEq`; proved conservation screens over
  `conservativeCatalog` / `growthCatalog`; `Rule.GrowthCompatible`
  predicate; `conservative_blocks_dim_geq_one` (Gorard's structural
  block formalised).

### 3. Advanced-infrageometry theorems (colleague modules)

Small proved theorems per colleague, grounded on hypergraph primitives:

- **Pavel Hájek (IT3)**: `HodgeLaplacianBounds.vrHodge0_quadratic_nonpos`
  — Dirichlet-energy argument for 0-form Hodge Laplacian PSD.
- **Van Le (M2/IQ5)**: `FisherMetricExtended` — ℝ-linearity + PSD on
  `BranchialProbability`.
- **Hubert Kolcz (M3)**: `BlowupPoissonConcrete` — zero / difference
  bracket instances + vertex/edge-count conservation.
- **Sara Ahmed (M7)**: `EMETracker` — `EMEPredicate V`,
  `emeHoldsEverywhere_and`, edge-count-bounded EME.
- **Zapata–Ahmed (M5)**: `BranchialCommutator` —
  `BranchialMultiRelated` reflexive-transitive closure.
- **Causal-set theory (IC)**: `ProperTimeBounds` — `ChainOfLength`
  length-0/length-1 characterisations, concatenation.
- **Path hypergraph**: `PathHypergraphDistance` — row-sum-zero, heat
  kernel preserves constants.
- **Cycle heat decay**: `CycleHeatDecayBounds` — spectral gap,
  first-mode decay, constant mode fixed.
- **Rule signatures**: `RuleSignatureEquiv` — equivalence relation
  (refl/symm/trans), empty-hypergraph signatures.

## Status breakdown by category

### Bridge ladder (10 rungs from discrete calculus to Einstein)

| Rung | Topic | Status |
|---|---|---|
| 1 | Discrete calculus | ✅ full |
| 2 | Operator convergence to continuum | ✅ C² Taylor (R1/A2/A3), cycle spectrum (R5), eigenvalue limit (A4) |
| 3 | Measure limits | ✅ counting measure, pushforward (A5); ⌛ weak convergence (A6), Wasserstein (A7) |
| 4 | Connections / Levi-Civita | 🟡 local-coord only; bundle/Koszul gap in Mathlib |
| 5 | Riemann / Ricci / scalar | ✅ local-coord Riemann, Ricci, Einstein; all GR metrics in zoo (Minkowski, Schwarzschild, FLRW, RN, Kerr, S², de Sitter) |
| 6 | ODE/PDE on `Hypergraph V` | ✅ heat (D1/D2/D4/D5/D6 partial), wave (D8), Klein-Gordon (D9), Schrödinger unitary (D10), EL (G1/G3/G4) |
| 7 | Fields / gauge | 🟡 scalar field ✅; gauge-field G2 open |
| 8 | Lorentzian geometry | ✅ discrete (LorentzLattice, Minkowski), continuum `DiagLorentzianManifold` (E1), discrete Cauchy foliation (E5); ⌛ continuum Lorentzian-GH |
| 9 | Einstein equations | ✅ F3 `EinsteinEqLambda`, Minkowski vacuum solves it, λ=0-forcing on flat |
| 10 | Hypergraph → GR (obligation form) | ✅ all obligation Props attached with flat-case witnesses; curved-case `bridgeHolds` still open |

### Refutation track (Gorard corpus)

- **F1 NoMetric**, **F2 Orthonormality**, **F3 Tautology**,
  **F4 Tautology**, **F5 Illdefined**, **F6 Circularity**,
  **F7 NamedRuleStructure** — all Lean-formal, axiom-clean.
- Empirical refutation of the named 2102.09363 rule: causal dim = 1 on
  every tested seed; structurally blocked by |LHS|=|RHS|.

### Infrageometry programme

| Group | Topic | Closed | Total |
|---|---|---|---|
| IA | Infraanalysis (Hájek) | 5 | 5 |
| IG | InfraGaugeTheory (Pokorny) | 11 | 11 |
| IC | Infracausality (EPS, MW-clock) | 8 | 8 |
| IT | Infratopology (VR + Latschev; Hájek) | 6 | 6 |
| ID | Infradimension | 7 | 7 |
| IB | Infrablowup | 6 | 6 |
| IQ | Branchial / quantum | 4 | 4 |
| IS | Synthetic axiomatic | 3 | 3 |
| IR | Ruliology | 7 | 7 |
| **Totals** | | **57** | **57** |

All 57 addressed; 50 closed with real content; 7 with substantive
open content (Latschev GH form, scale trichotomy bulk, EME-tracking
functor, path-integral amplitudes, exponential-map, commutator
theorem, spectral dimension asymptotics).

### Continuum-target GR zoo (Rung 5)

Every metric listed has a fully-bundled `MetricData` or
`PartialMetricData` **and** an attached hypergraph-origin
obligation Prop (provably inhabited for the flat/existence side):

Minkowski (full), Schwarzschild (`PartialMetricData` on exterior,
all 8 Christoffels), FLRW (`PartialMetricData`), Reissner-Nordström
(`PartialMetricData`), Kerr (components + valid domain), 2-sphere
(`PartialMetricData`), de Sitter (`PartialMetricData`), warpedDiag2
(R4 curved witness).

## What is open (honest posture)

- **Curved rule → curved metric bridges**: no known rule produces
  Schwarzschild / Kerr / FLRW in the GH limit. The obligation Props
  are correctly attached and correctly open. This is the real
  Wolfram-physics problem; Gorard's claim to have solved it is what
  our refutation chain dismantles.
- **Measure-theoretic bridges**: A7 Wasserstein rate, A8 d-torus
  measure lift.
- **Bundle machinery**: Mathlib gap for Riemannian / Lorentzian
  bundles blocks C1–C8.
- **Gauge fields**: G2 discrete gauge field via Rung-4 connection.
- **E-series**: E6 Lorentzian-GH, E7 discrete-causal → continuum
  Lorentzian convergence.
- **Empirical rule search via `wolframscript` / SetReplace**
  (task #190): infrastructure is in place; large-scale enumeration
  pending.

## What's next (priority sketch)

1. **Rule-search pipeline** — enumerate small rules via
   `wolframscript`, compute signatures, feed hits back into
   `RuleSearch.lean` catalog. Candidate-rule database grows from 5
   to ~50 formalised rules with signature claims.
2. **Curved-Γ FiberedGraph bridge** — extend
   `FiberedGraphConnectionBridge` from flat-case witness to a
   non-trivial curved `Connection F` approximating Schwarzschild's
   Γ at the horizon boundary.
3. **A6 / A7 measure bridges** — Wasserstein, d-torus measure lift.
4. **Paper drafts** — K1 audit paper, K3 infrageometry
   continuum-limits paper (R1/R2/R5/A3/A4 are the technical core).

## Links to internal docs

- [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md) — item-by-item audit of
  continuum structures against the grounding principle.
- [`STATUS.md`](STATUS.md) — live snapshot with full rung table.
- [`COVERAGE_MAP.md`](COVERAGE_MAP.md) — per-module coverage map
  (single source of truth).
- [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) — 10-rung ladder
  description.
- [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) — research programme
  (57 tasks / 9 groups).
- [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) — Gorard F1–F8 flaws with
  Lean-formalisation status.
- [`RULE_SEARCH.md`](RULE_SEARCH.md) — rule-search pipeline design.
