# infra_formalization

A Lean 4 / Mathlib formalisation of the Wolfram-model → general-relativity / quantum-mechanics bridge programme, coupled with a machine-checked audit of Gorard's principal publications on deriving GR from hypergraph rewriting.

The project runs on three parallel axes:

1. **Positive construction** — a 10-rung bridge ladder from hypergraph primitives to Einstein's equations, with every continuous object anchored to a hypergraph origin by an obligation Prop.
2. **Audit of the Gorard corpus** — line-by-line formalisation of seven structural flaws (F1–F7), each converted to an axiom-clean Lean theorem with counter-example witnesses.
3. **Infrageometry programme** — 57-task / 9-group research programme for the Wolfram Institute, covering colleagues' work (Pavel Hájek, Pavel Pokorny, Van Le, Hubert Kolcz, Jan Pullman, Carlos Zapata, Sara Ahmed, Ioana Milea).

All `lake build` jobs pass (3468 of 3468). Every theorem reduces to Lean's three standard axioms `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no custom axioms.

## Contents

- A Lean library with ~180 `.lean` modules building up discrete calculus, PDE theory on hypergraphs, GH convergence of scaled discrete structures, Lorentzian geometry, Einstein-equation formalism, branchial quantum mechanics, and infrageometry infrastructure — all from the same `Hypergraph V` / `RewritingSystem P` / `Trajectory sys init` primitives.
- A documentation set that tracks the full research programme at varying granularity (STATUS / COVERAGE_MAP / BRIDGE_MACHINERY / INFRAGEOMETRY / MAJOR_FLAWS / GROUNDING_AUDIT / MILESTONES / NEXT_STEPS).
- An audit trail for the Gorard papers: close-readings of each paper, cross-paper corpus audit, 184-row claims catalog, severity taxonomy, continuum-limit claim ledger, per-claim corpus assessment.
- Empirical scripts (Wolfram Language + Python) that independently re-implement the mechanics of Gorard's claims and test them against his rules.

## Why the project exists

The published Wolfram-model-to-GR derivations make a strong claim: that a specific rewriting rule "provably satisfies the Einstein field equations in the continuum limit" (2102.09363). The machinery of the claim is a chain of informally-stated approximations through Ollivier–Ricci, Gray-tube expansions, and a Poisson-sprinkle reconstruction. No part of this chain is machine-checked. Several steps, once separated from their prose, reduce to `Iff.rfl` or to mis-stated continuum identities.

The project exists to settle, formally, what is actually true in this corpus and what remains open, and to build the substantive bridge machinery that would have to be in place for any honest future claim of this form.

## Status headline (2026-04-23)

- **Build**: 3468/3468 jobs green.
- **Axiom cleanliness**: all proved theorems reduce to `{propext, Classical.choice, Quot.sound}`.
- **Infrageometry programme**: 50/57 tasks closed with real content; 7 in-flight with substantive open content (not stubs).
- **Grounding audit**: **all four action items closed**. No free-floating continuum islands at the obligation level (see [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md)).
- **Refutations**: F1–F7 Lean-formal; F6Circularity formally proved (G3's Poisson-sprinkle-then-reconstruct schema returns its input identically — "mathematically content-free").
- **Flat bridges proved**: cycle→circle, path→interval, 2-torus, d-torus, lattice→Minkowski.
- **Continuum-target GR zoo**: Minkowski, Schwarzschild, FLRW, Reissner-Nordström, Kerr, 2-sphere, de Sitter — all formalised with hypergraph-origin obligations attached.
- **Branchial QM**: finite slice → ℂ-Hilbert → self-adjoint adjacency → unitary Schrödinger → Born rule → observables → expectation values.
- **First complete chain**: `minkowski4_flat_vacuum_EFE_originated_global` — rule → metric → connection → EFE satisfaction, every ingredient inhabited by a concrete hypergraph-side witness.

## How it is structured

### Lean source (`lean/`)

```
lean/
  InfraFormalization.lean            — top-level module; imports everything
  InfraFormalization/
    # Core substrate
    Hypergraph.lean
    Rule.lean
    Application.lean
    Conservation.lean                — |LHS|=|RHS| ⇒ size preserved
    Multiway.lean                    — RewritingSystem, Step, MultiStep
    Causal.lean                      — Trajectory, causallyPrecedes
    CausalLevel.lean
    Branchial.lean, ParallelSchedule.lean, Demo.lean

    # Discrete calculus (Rung 1)
    DiscreteCalculus*.lean           — graph Laplacian, self-adjoint, Dirichlet, PSD
    HypergraphLaplacian.lean         — Δ_H on directed hyperedges
    HypergraphCalculus.lean          — gradient, divergence, Stokes
    HypergraphDistance.lean          — Hypergraph.dist, geodesic balls, triangle ineq (T3)
    LaplacianMatrix.lean             — Mathlib matrix form + heat kernel via exp
    CycleGraph.lean, CycleSpectrum.lean, CycleMatrixSpectrum.lean
    HeatKernelODE.lean               — ODE ↔ matrix heat kernel (T1)
    ExpEigenvector.lean              — exp fixes eigenvectors (T2)
    CycleHasEigenvalue.lean          — Mathlib HasEigenvalue form (T4)
    CycleEigenLimit.lean             — scaled eigenvalue → continuum (A4)
    CTwoTaylor.lean, ScaledDiffC2Bridge.lean  — C² Taylor bridges (R1/A3)

    # PDE ladder (Rung 6)
    HeatEquation.lean, HeatEquationUniqueness.lean, HeatKernelDecay.lean
    WaveEquation.lean, KleinGordon.lean, SchrodingerEquation.lean
    ScalarField.lean                 — Lagrangian + Euler-Lagrange (G1/G3/G4)
    DiscreteDAlembertian.lean        — BD 4D operator (flagged)

    # Continuum limits (Rungs 1-6)
    Infra/ScaledCycle, ScaledPath, ScaledTorus, ScaledTorusD
    Infra/LatticeDensity, Circle, GHBound, GHApprox
    Infra/OllivierStatement, GrayTubeStatement
    Infra/LorentzLattice, Minkowski, ScaledLorentz
    Infra/TrajectoryLorentz{,D}, FullBridge

    # Curvature (Rung 5)
    CurvatureLocalCoord.lean         — Christoffel, symmetries
    CurvatureRiemann.lean            — Riemann, Ricci, Einstein; flat case vanishes
    DiscreteRicci.lean               — Forman-Ricci
    RicciBridge.lean                 — cycle/circle Ricci = 0 match
    CurvedRicciBridge.lean           — warpedDiag2 non-flat witness
    CovariantDerivative.lean         — ∇ on ConnectionData (X2)
    PartialMetricData.lean           — X1: metrics with validity domains
    Schwarzschild.lean               — all 8 Christoffels; PartialMetricData bundle
    FLRW.lean, ReissnerNordstrom.lean, Kerr.lean, DeSitter.lean, TwoSphere.lean
    GRMetricsDemo.lean               — gr_metric_zoo single-theorem bundle

    # Lorentzian (Rung 8)
    LorentzianManifold.lean          — DiagLorentzianManifold (E1)
    CausalGraphType.lean             — TR-DAG CausalGraph (IC1)
    CausalFoliation.lean             — stably causal → foliation (E5)
    SpatialReconstruction.lean, EPSAxioms.lean, MarzkeWheeler.lean

    # Einstein equations (Rung 9)
    EinsteinEquations.lean           — F3 EinsteinEqLambda; Minkowski vacuum
    StressEnergyTensor.lean, F2EnergyConditions.lean
    F7Penrose.lean, F8Raychaudhuri.lean

    # Bridge obligations — grounding-audit (NEW, 2026-04-23)
    HypergraphMetricBridges.lean     — G2: metric origin obligations
    CausalLorentzianBridge.lean      — G3: manifold origin obligations
    FiberedGraphConnectionBridge.lean— G1: connection origin obligations
    EinsteinEquationsBridge.lean     — G4: EFE origin obligations
    RuleWitnesses.lean               — concrete rules used in bridge proofs
    RuleSearch.lean                  — rule catalog + decidable screens

    # Refutations
    Refutations/F1NoMetric.lean
    Refutations/F2Orthonormality.lean
    Refutations/F3Tautology.lean
    Refutations/F4Tautology.lean
    Refutations/F5Illdefined.lean
    Refutations/F6Circularity.lean
    Refutations/F7NamedRuleStructure.lean

    # Infrageometry programme (57 tasks)
    IA-: DagBlowup, DagCalculus, DeRham, FormCochainIntegration (Hájek IA)
    IG-: FiberedGraph, Holonomy, FiberBundle (Pokorny IG)
    IC-: CausalGraphType, CausalFoliation, EPSAxioms, MarzkeWheeler, SpatialReconstruction
    IT-: VietorisRips, HodgeVR, HodgeLaplacianSpectrum (Hájek IT)
    ID-: HypergraphDistance, PlateauDimension, HomologyDimension,
         CoordinatizationDimension, CausalDimension
    IB-: ElementaryBlowup, BlowupOperations, BlowupLieAlgebra,
         RadialLaminarBlowup, BlowupPoissonConcrete (Kolcz)
    IQ-: BranchialHilbert, BranchialSchrodinger, FisherMetric,
         FisherMetricExtended, EMETracker (Ahmed, Van Le)
    IS-: SyntheticGeometry, SyntheticAxiomatic, InfrageometricScene (Pokorny IS)
    IR-: RuleSignature, RuleSignatureEquiv, CandidateRuleDatabase,
         RuleDimensionBounds, StructuralRuleBounds

    # Axiom check
    AxiomCheck.lean                  — 300+ #print axioms lines
```

### Documentation

| File | Purpose |
|---|---|
| [`STATUS.md`](STATUS.md) | Live snapshot — rung table, task counters, latest shipped |
| [`COVERAGE_MAP.md`](COVERAGE_MAP.md) | Per-module coverage map (single source of truth) |
| [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md) | Item-by-item audit: what is hypergraph-grounded, what is continuum-target-only, with ✅ / ⚠ / ❌ marks |
| [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) | 10-rung ladder from discrete calculus to Einstein |
| [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) | Research programme description (57 tasks / 9 groups) |
| [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) | F1–F8 structural-flaw registry with Lean-formalisation status |
| [`MILESTONES.md`](MILESTONES.md) | Checkbox tracker across all phases |
| [`NEXT_STEPS.md`](NEXT_STEPS.md) | Done / in flight / waiting |
| [`RULE_SEARCH.md`](RULE_SEARCH.md) | Rule-search pipeline design |
| [`PUBLISHABLE.md`](PUBLISHABLE.md) | Paper targets P1–P9 with dependencies |
| [`FINDINGS.md`](FINDINGS.md) | Canonical one-line summary of every audited claim |
| [`GLOSSARY.md`](GLOSSARY.md) | Technical terms |
| [`INDEX.md`](INDEX.md) | Document tree |
| [`LEAN_PHYSICS.md`](LEAN_PHYSICS.md) | HepLean / Mathlib conventions |
| [`WEEKLY_REPORT_2026-04-23.md`](WEEKLY_REPORT_2026-04-23.md) | This week's Wolfram-Institute-facing report |

### Audit notes (`notes/`)

- `plan.md` — 7-phase verification plan
- `severity_taxonomy.md` — S1–S6 taxonomy; "How the errors recur"
- `corpus_audit.md` — cross-paper map of repeated errors
- `claims_catalog.md` — 184-row G1 equation audit
- `singleway_vs_multiway.md` — single-way vs multi-way + null-tetrad explainer
- `corpus_assessment.md` — synthesis verdict
- `2004.14810_close_reading.md`, `2102.09363_close_reading.md`, `2303.07282_close_reading.md`
- `null_tetrad_resolution.md`, `limit_toolkit.md`, `empirical_refutation.md`, `continuum_limit_claims.md`

### Results (`results/`)

- `phase1_selfaudit/` — Python rewriter ↔ SetReplace agreement on the Gorard named rule; causal-dimension measurements on 9 seeds.
- `phase2_continuum/` — Eq 342 (Gray tube), Eq 344 (Ollivier) verdict files with symbolic + numeric computation.

### Scripts (`scripts/`)

Wolfram Language + Python scripts that reproduce every empirical verdict in `results/`.

## The bridge ladder (10 rungs)

Every continuum object in the project lives on a rung of this ladder, and every rung is anchored to its predecessor by an explicit convergence theorem or obligation Prop.

| Rung | Content | Key theorem | Status |
|---|---|---|---|
| 1 | Discrete calculus | Self-adjoint `Δ_H`, Dirichlet form, PSD, Stokes | ✅ |
| 2 | Operator convergence | `scaledSecondDiff → f''` for every C²; cycle-spectrum → circle-spectrum | ✅ |
| 3 | Measure limits | Counting measure, pushforward; ⌛ A6 weak-convergence, A7 Wasserstein | 🟡 |
| 4 | Connections | Local-coord Christoffels ✅; Mathlib bundle/Koszul gap blocks C1–C8 | 🟡 |
| 5 | Riemann / Ricci | Riemann, Ricci, Einstein tensors; full GR metric zoo | ✅ |
| 6 | ODE / PDE on Hypergraph V | Heat, wave, Klein-Gordon, Schrödinger unitary, EL equations | ✅ |
| 7 | Fields / gauge | Scalar field ✅; G2 gauge field 🔲 | 🟡 |
| 8 | Lorentzian geometry | LorentzLattice, Minkowski, `DiagLorentzianManifold`, discrete foliation | ✅ (discrete+E1+E5); ⌛ Lorentzian-GH |
| 9 | Einstein equations | `EinsteinEqLambda`, Minkowski vacuum, λ=0-forcing | ✅ flat |
| 10 | Hypergraph → GR | Flat bridges ✅; origin obligations ✅; curved `bridgeHolds` open | 🟡 obligation-level ✅, content-level open |

See [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) for the full description.

## Grounding principle (non-negotiable)

Every continuous structure in the repository must either:

1. be defined directly from hypergraph primitives (`Hypergraph V`, `RewritingSystem P`, `Trajectory sys init`, `CausalGraph V`), or
2. be the target of an explicit convergence theorem starting from such primitives, or
3. carry an explicit `…OriginObligation` Prop binding it to a hypergraph-side existence claim.

No category-(3) obligation is allowed to sit as an open `True ∧ False` stub — every one has a `bridgeHolds` predicate with real content, and flat cases are inhabited by concrete witnesses. The audit of this principle lives in [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md).

## Refutation track (Gorard corpus)

The four papers audited:

- **G1 — arXiv:2004.14810** — *Some Relativistic and Gravitational Properties of the Wolfram Model*
- **G2 — arXiv:2011.12174** — *Algorithmic Causal Sets and the Wolfram Model*
- **G3 — arXiv:2102.09363** — *Hypergraph Discretization of the Cauchy Problem in General Relativity via Wolfram Model Evolution*
- **G4 — arXiv:2303.07282** — *Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems*

Plus supporting papers: 2011.12174, 2308.07508, 2401.14209.

Lean-formal refutations:

| Flaw | Lean module | Status |
|---|---|---|
| F1 No canonical hypergraph-to-metric | `Refutations/F1NoMetric.lean` | ✅ |
| F2 Fiat orthonormality is non-canonical | `Refutations/F2Orthonormality.lean` | ✅ |
| F3 "dim preservation ⇒ EFE" = `Iff.rfl` | `Refutations/F3Tautology.lean` | ✅ |
| F4 "causal invariance ⇔ covariance" = `Iff.rfl` | `Refutations/F4Tautology.lean` | ✅ |
| F5 Discrete-to-continuum "becomes" under-determined | `Refutations/F5Illdefined.lean` | ✅ |
| F6 G3 "provably satisfies EFE" is circular (Poisson-sprinkle then reconstruct) | `Refutations/F6Circularity.lean` | ✅ |
| F7 G3 named rule's structural block | `Refutations/F7NamedRuleStructure.lean` + empirical | ✅ |

Empirical refutation: the 2102.09363 named rule shows causal-graph dimension = 1 on every tested seed under both SetReplace and an independent Python re-implementation. `|LHS| = |RHS| = 4` forces state-size conservation, which combined with finite-vertex-support forces bounded ball-volume — formalised as `conservative_blocks_dim_geq_one` in `RuleSearch.lean`.

## The research programme (infrageometry)

57 tasks across 9 groups, covering the Wolfram-Institute infrageometry programme:

| Group | Topic | Lead / collaborator | Closed | Total |
|---|---|---|---|---|
| IA | Infraanalysis | Pavel Hájek | 5 | 5 |
| IG | InfraGaugeTheory | Pavel Pokorny | 11 | 11 |
| IC | Infracausality | Zapata + Ahmed | 8 | 8 |
| IT | Infratopology (VR + Latschev) | Pavel Hájek | 6 | 6 |
| ID | Infradimension | — | 7 | 7 |
| IB | Infrablowup (Lie algebra, Poisson) | Hubert Kolcz | 6 | 6 |
| IQ | Branchial / quantum | Van Le, Ahmed | 4 | 4 |
| IS | Synthetic axiomatic | Pokorny | 3 | 3 |
| IR | Ruliology | — | 7 | 7 |

See [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) for per-task descriptions.

## Building

Prerequisites: Lean 4 via `elan`, `lake`, and a Mathlib build (~1 hour first time).

```bash
cd lean
lake update            # first-time Mathlib setup
lake build             # ~3500 jobs; green
```

## Reproducing the empirical checks

Prerequisites: `wolframscript` (Wolfram Engine or Mathematica), SetReplace paclet 0.3+, Python 3.10+.

```bash
# 1) Empirical refutation of the G3 named rule (SetReplace)
wolframscript -file scripts/run_seeds_v3.wl
wolframscript -file scripts/causal_dimension.wl
wolframscript -file scripts/grid3d_test.wl

# 2) Independent Python re-implementation (no SetReplace)
cd scripts/python && python3 run_all_seeds.py

# 3) Eq 342 (Gray tube) audit on S², S³
wolframscript -file scripts/test_eq342.wl
```

Every verdict is reproducible to the precision quoted in `results/`.

## Methodology

Every claim about the Gorard corpus is checked against four independent rails (close-reading, symbolic computation, Lean formalisation, independent empirical re-implementation) before being accepted into the repository. Correct claims are verified; incorrect claims are documented precisely, with counter-example witnesses and corrected statements side by side.

Verdicts are labelled precisely ("overclaim", "misstatement", "ill-defined", "tautology", "error", "conjectural", "hunch"). The goal is to have a load-bearing, verifiable answer to: *what in this corpus is actually true, and how is it linked (if at all) to general relativity?*

## License

Formalisation code: MIT. Audit notes: CC-BY-4.0. Gorard paper sources in `papers/` are the original authors' and included only for reference.
