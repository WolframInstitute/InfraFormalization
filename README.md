# InfraFormalization

A Lean 4 / Mathlib formalisation of the Wolfram-model → general-relativity / quantum-mechanics bridge programme, coupled with a machine-checked audit of Gorard's principal publications on deriving GR from hypergraph rewriting.

The project runs on three parallel axes:

1. **Positive construction** — a 10-rung bridge ladder from hypergraph primitives to Einstein's equations, with every continuous object anchored to a hypergraph origin by an obligation Prop.
2. **Audit of the Gorard corpus** — line-by-line formalisation of seven structural flaws (F1–F7), each converted to an axiom-clean Lean theorem with counter-example witnesses.
3. **Infrageometry programme** — 57-task / 9-group research programme for the Wolfram Institute, covering colleagues' work (Pavel Hájek, Pavel Pokorny, Van Le, Hubert Kolcz, Jan Pullman, Carlos Zapata, Sara Ahmed, Ioana Milea).

`lake build` is fully green. Every theorem reduces to Lean's three standard axioms `{propext, Classical.choice, Quot.sound}` — no `sorry`, no `native_decide`, no custom axioms, certified by `#print axioms` in `AxiomCheck.lean`.

## Contents

- A Lean library built on the primitives `Hypergraph V`, `RewritingSystem P`, and `Trajectory sys init`, with every downstream object (graph Laplacian, discrete PDEs, metric/connection data, Lorentzian structures, causal foliations, branchial Hilbert spaces, Ricci and Einstein machinery) reduced to those primitives or to an explicit hypergraph-origin obligation Prop.
- A documentation set: [`ROADMAP.md`](ROADMAP.md) (phase-sorted full-program sequencing), [`STATUS.md`](STATUS.md), [`NEXT_STEPS.md`](NEXT_STEPS.md), [`INDEX.md`](INDEX.md), [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md), [`COVERAGE_MAP.md`](COVERAGE_MAP.md), [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md), [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md), [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md), [`MILESTONES.md`](MILESTONES.md).
- An audit trail for the Gorard papers (G1 2004.14810, G2 2011.12174, G3 2102.09363, G4 2303.07282): close-readings, cross-paper corpus audit, row-level claims catalog, severity taxonomy, continuum-limit claim ledger, per-claim corpus assessment.
- Empirical scripts (Wolfram Language + Python) that independently re-implement the mechanics of Gorard's claims and test them against his rules, including a SetReplace-vs-Python cross-check on the named EFE rule.

## Motivation

The published Wolfram-model-to-GR derivations make a strong claim: that a specific rewriting rule "provably satisfies the Einstein field equations in the continuum limit" (2102.09363). The machinery of the claim is a chain of informally-stated approximations through Ollivier–Ricci, Gray-tube expansions, and a Poisson-sprinkle reconstruction. No part of this chain is machine-checked. Several steps, once separated from their prose, reduce to `Iff.rfl` or to mis-stated continuum identities.

The project exists to settle, formally, what is actually true in this corpus and what remains open, and to build the substantive bridge machinery that would have to be in place for any future claim of this form.

## Status headline (2026-04-26 — late)

**Sprint critical path closed (`#234` W_1 obligation discharged) + first formal exec ↔ abstract bridge (`#231`) + d²=0 cochain-complex axiom + Hodge PSD foundation.** Headline landings since the previous status:

- **`d ∘ d = 0`** — `KnillCore.dSquared_eq_zero` proves the cochain-complex axiom for the signed boundary on oriented simplices, axiom-clean (#277). Plus `(d*)² = 0` codual, Hodge PSD (`hodgeOnG_psd`), Hodge ↔ Dirac kernel iff (`isDiracKernel`), Hodge diagonal sum-of-squares. Foundation for KN14 McKean-Singer, KN15 Atiyah-Singer, KN16 Cartan, KN18 Brouwer-Lefschetz.
- **First W_1 obligation discharge** — `#234` `subdivisionDiscrepancy n := 1/2^n ≤ 1/n` discharges `WassersteinRateObligation` for the canonical subdivision-rule trajectory (`#284 / Route D`). First end-to-end machine-checked rule-trajectory → continuum-target convergence certificate.
- **First formal exec ↔ abstract bridge** — `MultiwayExecBridge.lean` (#231): `ExecRule.toRule`, `Fin.embedSuffix`, single-rule `ExecSystem` cast. Closes the architectural gap between the executable engine (`MultiwayExec`) and the abstract `Rule P` / `Step` / `MultiStep` track.
- **KN3/KN8** — Wu inclusion-exclusion identity + Euler-Poincaré f-vector identity proven in `KnillCore.lean`.
- **Synthetic-geometry framing** — INFRAGEOMETRY.md gains a Tarski-reduction / spectral-angles / parallel-postulate-as-branching framing for SIG2/SIG3.
- **ROADMAP.md** — full-program sequencing (Phase A → B → C → D → BBH merger from hypergraph IC).

- **Size** (rough): ~150 Lean files, ~25k LOC; ~900 theorems, ~440 definitions. Numbers move every session; build is fully green (3526 jobs).
- **Axiom cleanliness**: every `#print axioms`-certified theorem reduces to `{propext, Classical.choice, Quot.sound}` (many to `{propext, Quot.sound}` only). No `sorry`, no `native_decide`, no custom axioms.
- **Infrageometry obligations — all seven proved**. `RemainingObligations.lean` bundles them in `all_obligations_hold`: IT5 Latschev, IT6 scale trichotomy, ID6 cycle compatibility (`V(v,r) = 2r + 1` exact), IQ6 Fubini-Study / Bhattacharyya bound, IQ8 EME persistence, IQ9 path-integral baseline, IR7 realisability-restricted reverse-engineering. The over-strong unrefined IR7 is provably false (`not_reverseEngineeringObligation`). Remaining open infrageometry tasks are IG10 (exponential map via weighted shortest-path counts) and IB2 (causal-branchial commutator theorem, predicate-level).
- **Substantive new results since the weekly report** (187 commits, 24k LOC):
    - **ID6 `cycleHypergraph_ballVolume_exact`**: `V(v, r) = 2r + 1` on every cycle hypergraph for all `r` with `2r + 1 ≤ n`. Upper bound via walk-structural induction — every walk-endpoint lands in the forward/backward shift set — plus composition lemmas `F^[j] ∘ F`, `G^[j] ∘ G`, cross-cancellations. Lower bound via disjoint shift-family Finsets with left-cancellation injectivity.
    - **`dimensionCompatibilityObligation_holds`**: lifts that to the obligation Prop for every `n ≥ 3`.
    - **C7 `HypergraphConnection`**: discrete connection on a hypergraph with group-valued transport, flat baseline, walk-transport as a monoid homomorphism (`transportWalk_append`), holonomy, `IsFlat` predicate; hypergraph analog of `FiberedGraph.Connection`.
    - **C1 `DiagRiemannianMetric` / C2 `DiagLorentzianMetric`**: positive-definite and `(−,+,+,+)` predicates on `MetricData n` with Euclidean and Minkowski witnesses.
    - **J1 `MultiwayCausalGraph`**: joint structure bundling a rewriting system, initial hypergraph, and causal DAG on events — the "multiway causal graph" of Wolfram physics at the formalization level.
    - **H1 `CandidateRuleCatalog`**: Gorard's named rule (arXiv:2102.09363) plus four other literature rules as concrete `Rule P` instances with `LiteratureSource` citations and machine-checked conservation theorems.
    - **Cycle-hypergraph distance infrastructure**: closed-form `.val` for iterated ±1 shifts, injectivity on admissible ranges, forward/backward disjointness, parallel-transport walk composition — feeds C8 (scaled → Levi-Civita).
- **Grounding audit**: all four action items closed. No free-floating continuum islands at the obligation level (see [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md)).
- **Refutations**: F1–F7 Lean-formal; F6 (circular G3 derivation) formally proved as `circular_procedure_is_identity`; F8 documentary.
- **Flat bridges proved**: cycle → circle, path → interval, 2-torus, d-torus, discrete Lorentz → Minkowski.
- **Continuum-target GR zoo**: Minkowski, Schwarzschild, FLRW, Reissner-Nordström, Kerr, 2-sphere, de Sitter — all formalised with hypergraph-origin obligations attached.
- **Branchial QM**: finite slice → ℂ-Hilbert → self-adjoint adjacency → unitary Schrödinger → Born rule → observables → expectation values.
- **First complete chain**: `minkowski4_flat_vacuum_EFE_originated_global` — rule → metric → connection → EFE satisfaction, every ingredient inhabited by a concrete hypergraph-side witness.

## How it is structured

### Lean source (`lean/InfraFormalization/`)

```
lean/
  InfraFormalization.lean            — top-level module; imports everything
  InfraFormalization/
    # Core substrate
    Hypergraph.lean                  — Hypergraph V; Adj, degree, geodesicBall
    Rule.lean                        — Rule P; IsConservative
    Application.lean                 — Application r; size preservation
    Conservation.lean                — |LHS|=|RHS| ⇒ size preserved on trajectories
    Multiway.lean                    — RewritingSystem, Step, MultiStep
    Causal.lean                      — Trajectory sys init, causallyPrecedes
    CausalLevel.lean                 — level function, antichain at each level
    Branchial.lean, BranchialCanonical.lean
    ParallelSchedule.lean, Demo.lean
    RuleSearch.lean, RuleWitnesses.lean
    CandidateRuleCatalog.lean        — H1: literature rules as Rule P (gorardNamedRule, etc.)
    CandidateRuleDatabase.lean       — IR6: CandidateRule + decidable screens
    MultiwayCausalGraph.lean         — J1: combined causal + branchial structure

    # Discrete calculus & spectral theory (Rungs 1–2)
    DiscreteCalculus.lean, DiscreteCalculusSymm.lean  — graph Laplacian, self-adjoint, Dirichlet, PSD
    HypergraphLaplacian.lean         — Δ_H on directed hyperedges
    HypergraphCalculus.lean          — gradient, divergence, Stokes
    HypergraphDistance.lean          — dist, geodesic balls, triangle ineq; cycle-hypergraph walk infrastructure (ID6 machinery)
    HypergraphConnection.lean        — C7: discrete connection, transport along walks, holonomy, IsFlat
    PathHypergraph.lean, PathHypergraphDistance.lean
    RodkeyClassification.lean        — P20 (partial): BallVolumeVertexUniform, DistTransitive, Regular
    LaplacianMatrix.lean             — Mathlib matrix form + heat kernel via Matrix.exp (R2)
    LaplacianBridge.lean, HypergraphCycleBridge.lean
    CycleGraph.lean, CycleSpectrum.lean, CycleMatrixSpectrum.lean
    CycleHeatDecayBounds.lean
    HeatKernelODE.lean               — ODE ↔ matrix heat kernel (T1)
    ExpEigenvector.lean              — exp fixes eigenvectors (T2)
    CycleHasEigenvalue.lean          — Mathlib HasEigenvalue form (T4)
    CycleEigenLimit.lean             — scaled eigenvalue → continuum (A4)
    SecondDifference.lean, CTwoTaylor.lean, ScaledDiffC2Bridge.lean  — C² Taylor bridges (R1/A3)
    SymmEigenOrthogonal.lean

    # PDE ladder (Rung 6)
    HeatEquation.lean, HeatEquationUniqueness.lean
    HeatKernelDecay.lean             — long-time convergence to uniform (D6 partial)
    WaveEquation.lean, KleinGordon.lean, SchrodingerEquation.lean
    ScalarField.lean                 — Lagrangian + Euler-Lagrange (G1/G3/G4)
    DiscreteDAlembertian.lean

    # Continuum limits (Rungs 1–6)
    Infra/ScaledCycle, ScaledPath, ScaledTorus, ScaledTorusD
    Infra/LatticeDensity, Circle, GHBound, GHApprox
    Infra/OllivierStatement, GrayTubeStatement
    Infra/LorentzLattice, Minkowski, ScaledLorentz
    Infra/TrajectoryLorentz{,D}, FullBridge

    # Metrics, connections, curvature (Rung 5)
    CurvatureLocalCoord.lean         — MetricData n, Christoffel, symmetries
    CurvatureRiemann.lean            — Riemann, Ricci, Einstein; flat case vanishes
    DiscreteRicci.lean               — Forman-Ricci
    RicciBridge.lean, CurvedRicciBridge.lean
    CovariantDerivative.lean         — ∇ on ConnectionData (X2)
    PartialMetricData.lean           — X1: metrics with validity domains
    RiemannianManifold.lean          — C1: DiagRiemannianMetric + Euclidean witness
    LorentzianManifold.lean          — C2/E1: DiagLorentzianMetric + Minkowski witness
    Schwarzschild.lean, FLRW.lean, ReissnerNordstrom.lean, Kerr.lean
    DeSitter.lean, TwoSphere.lean
    GRMetricsDemo.lean               — single-theorem bundle over the GR zoo

    # Lorentzian structure & causal foliation (Rung 8)
    CausalGraphType.lean             — TR-DAG CausalGraph (IC1)
    CausalFoliation.lean             — stably causal → foliation (E5 in progress)
    SpatialReconstruction.lean, EPSAxioms.lean, MarzkeWheeler.lean
    ProperTimeBounds.lean

    # Einstein equations (Rung 9)
    EinsteinEquations.lean           — F3 EinsteinEqLambda; Minkowski vacuum
    StressEnergyTensor.lean
    # F2 energy conditions, F7 Penrose statement, F8 Raychaudhuri
    # all live under CurvatureRiemann + StressEnergyTensor + EinsteinEquations

    # Hypergraph-origin obligations (grounding-audit bridges)
    HypergraphMetricBridges.lean     — G2: every GR metric ↔ hypergraph origin obligation
    CausalLorentzianBridge.lean      — G3: manifold-from-causal-graph obligation
    FiberedGraphConnectionBridge.lean— G1: connection-from-fibered-graph obligation
    EinsteinEquationsBridge.lean     — G4: EFE origin obligation bundling the above

    # Fibered-graph machinery (IG)
    FiberedGraph.lean, Holonomy.lean, FiberBundle.lean
    MultiFibrationProjection.lean, CoordinatizationDimension.lean

    # Infradimension (ID)
    HomologyDimension.lean, PlateauDimension.lean, CausalDimension.lean

    # Infratopology + VR (IT)
    VietorisRips.lean, HodgeVR.lean
    HodgeLaplacianSpectrum.lean, HodgeLaplacianBounds.lean

    # Branchial / quantum (IQ) + measure (A5)
    BranchialHilbert.lean, BranchialSchrodinger.lean, BranchialFinite.lean
    BranchialCommutator.lean
    FisherMetric.lean, FisherMetricExtended.lean
    EMETracker.lean
    HypergraphMeasure.lean

    # Blowup / Lie / Poisson (IB)
    ElementaryBlowup.lean, BlowupOperations.lean, BlowupLieAlgebra.lean
    RadialLaminarBlowup.lean, BlowupPoissonConcrete.lean

    # Analysis on DAGs / forms (IA)
    DagBlowup.lean, DagCalculus.lean, DeRham.lean, FormCochainIntegration.lean

    # Synthetic axiomatic infrageometry (IS)
    SyntheticGeometry.lean, SyntheticAxiomatic.lean, InfrageometricScene.lean

    # Rule signatures and dimension bounds (IR)
    RuleSignature.lean, RuleSignatureEquiv.lean
    RuleDimensionBounds.lean, StructuralRuleBounds.lean

    # Final-obligation Props + master closure
    RemainingObligations.lean        — all seven infrageometry obligations; all_obligations_hold

    # Continuum-limit Props for targets currently open
    ContinuumLimitStatement.lean     — Schwarzschild/Kerr/FLRW obligations (guarded ∧ False)
    ContinuumBridgeDemo.lean, WolframPhysicsBridgeDemo.lean, GrandTour.lean

    # Refutations
    Refutations/F1NoMetric.lean, F2Orthonormality.lean, F3Tautology.lean
    Refutations/F4Tautology.lean, F5Illdefined.lean, F6Circularity.lean
    Refutations/F7NamedRuleStructure.lean

    # Axiom-cleanliness certification
    AxiomCheck.lean                  — #print axioms over every theorem cited above
```

### Documentation

| File | Purpose |
|---|---|
| [`STATUS.md`](STATUS.md) | Live snapshot — rung table, obligation status, latest closures |
| [`COVERAGE_MAP.md`](COVERAGE_MAP.md) | Per-module coverage map (single source of truth for what's in each file) |
| [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md) | Item-by-item audit: what is hypergraph-grounded, what is continuum-target-only, with per-object status |
| [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) | 10-rung ladder from discrete calculus to Einstein equations |
| [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) | Infrageometry programme description (9 groups IA–IR) |
| [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) | F1–F8 structural-flaw registry with Lean-formalisation status |
| [`MILESTONES.md`](MILESTONES.md) | Phase-level checkbox tracker |
| [`NEXT_STEPS.md`](NEXT_STEPS.md) | Done, in progress, waiting — including P-group mapping of colleague work |
| [`RULE_SEARCH.md`](RULE_SEARCH.md) | Rule-search pipeline design |
| [`PUBLISHABLE.md`](PUBLISHABLE.md) | Paper targets with dependencies |
| [`FINDINGS.md`](FINDINGS.md) | Canonical one-line summary of every audited claim |
| [`GLOSSARY.md`](GLOSSARY.md) | Technical terms |
| [`INDEX.md`](INDEX.md) | Full document tree |
| [`LEAN_PHYSICS.md`](LEAN_PHYSICS.md) | HepLean / Mathlib conventions |
| [`INFRAFORMALIZATION_WEEKLY_REPORT_2026-04-23.md`](INFRAFORMALIZATION_WEEKLY_REPORT_2026-04-23.md) | Most recent Wolfram-Institute-facing weekly report (full; `_SHORT` and `_PARAGRAPH` variants also present) |
| [`POST_WEEKLY_UPDATES_2026-04-23.md`](POST_WEEKLY_UPDATES_2026-04-23.md) | Post-weekly-report delta log (current running list of closures since the weekly) |

### Audit notes (`notes/`)

- `plan.md` — 7-phase verification plan
- `severity_taxonomy.md` — S1–S6 taxonomy; "How the errors recur"
- `corpus_audit.md` — cross-paper map of repeated errors
- `claims_catalog.md` — 184-row G1 equation audit
- `singleway_vs_multiway.md` — single-way vs multi-way
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

Legend for the Status column:

- **proved** — the content of the rung is a machine-checked theorem.
- **partial** — some of the rung's content is proved; specific sub-items remain open.
- **flat case proved; curved case open** — proved when the underlying spacetime is flat (Minkowski, cycle, torus, lattice); the proof for a curved target (Schwarzschild, Kerr, FLRW) is open.
- **flat case proved end-to-end; curved case has the obligation Prop attached but the curved bridge theorem is open** — every continuum GR target has a hypergraph-side obligation Prop; flat-case witnesses are inhabited; curved-case witnesses are not.

| Rung | Content | Key theorem | Status |
|---|---|---|---|
| 1 | Discrete calculus | Self-adjoint `Δ_H`, Dirichlet form, PSD, discrete Stokes | proved |
| 2 | Operator convergence | `scaledSecondDiff → f''` for every C²; cycle-spectrum → circle-spectrum | proved |
| 3 | Measure limits | Counting measure + pushforward (A5); A6 weak convergence complete for polynomials ≤ deg 3; **A7 Wasserstein-1 concrete rates landed** — project-own W_1 on `TransportPlan` supports with cycle-hypergraph anchor; `W_1_scaled(δ_v, δ_{v+1}) = 1/n` (sharp) and `W_1_scaled(μ, μ∘shift) ≤ 1/n` for any probability measure μ; A8 d-torus lift open | partial |
| 4 | Connections | Local-coordinate Christoffel proved; project-own bundle formulation in `VectorBundleConnection.lean` — C1, C2, C3, C4, C6, C7 substantive; C5 (Koszul existence/uniqueness) and C8 (curved convergence) tracked as own open tasks | partial |
| 5 | Riemann / Ricci | Riemann, Ricci, Einstein tensors; full GR metric zoo | proved |
| 6 | ODE / PDE on Hypergraph V | Heat, wave, Klein-Gordon, Schrödinger unitary, Euler-Lagrange | proved |
| 7 | Fields / gauge | Scalar field proved; discrete gauge field (G2) substantive via `DiscreteGaugeField` + Wilson-loop holonomy | partial |
| 8 | Lorentzian geometry | LorentzLattice, Minkowski, `DiagLorentzianManifold` (E1), discrete Cauchy foliation (E5); continuum Lorentzian Gromov-Hausdorff open | flat case proved; curved case open |
| 9 | Einstein equations | `EinsteinEqLambda`; Minkowski + flat connection solves vacuum EFE; flat connection forces Λ = 0 | flat case proved; curved case open |
| 10 | Hypergraph → GR | Flat bridges proved end-to-end (cycle → circle, path → interval, 2-torus, d-torus, lattice → Minkowski); every continuum GR target has an origin-obligation Prop; flat-case witnesses are inhabited; curved-case witnesses are not | flat case proved end-to-end; curved case has the obligation Prop attached but the curved bridge theorem is open |

See [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) for the full description.

## Grounding principle (non-negotiable)

Every continuous structure in the repository must either:

1. be defined directly from hypergraph primitives (`Hypergraph V`, `RewritingSystem P`, `Trajectory sys init`, `CausalGraph V`), or
2. be the target of an explicit convergence theorem starting from such primitives, or
3. carry an explicit `…OriginObligation` Prop binding it to a hypergraph-side existence claim.

No category-(3) obligation is allowed to sit as an open `True ∧ False` stub — every one carries a predicate with real mathematical content, and flat-case witnesses are inhabited by concrete hypergraph-side constructions. The audit of this principle lives in [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md).

## Refutation track (Gorard corpus)

### The four audited papers

- **G1 — arXiv:2004.14810** — *Some Relativistic and Gravitational Properties of the Wolfram Model.* Foundational. §3.3 is the claimed Einstein-equations derivation; §3.1 states the Ollivier–Ricci identity; §3.2 introduces the fiat-orthonormality convention.
- **G2 — arXiv:2011.12174** — *Algorithmic Causal Sets and the Wolfram Model.* Reuses G1 §5; introduces Eq 126 (tube-volume coefficient) used later in G3 Eq 342.
- **G3 — arXiv:2102.09363** — *Hypergraph Discretization of the Cauchy Problem in GR via Wolfram Model Evolution.* Contains the "provably satisfies EFE" claim and the named rule. Relies on a Poisson-sprinkle-then-reconstruct schema (TeX lines 6080, 6152).
- **G4 — arXiv:2303.07282** — *Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems.* Title-body gap: no discrete Raychaudhuri, no discrete expansion scalar, no discrete energy condition, no discrete stress-energy tensor, no "shear" or "vorticity" in the text.

Supporting papers referenced: 2308.07508, 2401.14209.

### General patterns

- **Objects introduced by analogy, not by construction.** Discrete metric `g^{ab}`, volume form `d\mu_g`, functional derivative `δ/δg^{ab}`, orthonormal hyperedges — all named, none defined.
- **Mis-stated cited continuum identities.** Ollivier's theorem uses directional `Ric(v,v)`; the papers write scalar `R`. Gray's tube coefficient is `(R + Ric(u,u))/(6(d+1))`; the papers write `(d−1)(R − Ric(u,u))/(d+1)`. Factor-2 off on S², factor-6 off on S³.
- **Definitions restated as theorems.** "Causal invariance ⇔ discrete general covariance" and "asymptotic dimensionality preservation ⇒ EFE" both unfold to `Iff.rfl`.
- **Informal bridge prose.** "Becomes" (which topology?), "weak ergodicity" (precise definition?), "provably" (applied to an open Sorkin–Benincasa–Dowker conjecture).
- **Circularity in G3.** The initial hypergraph is built by Poisson-sampling vertices from the known target spacetime; the subsequent reconstruction then recovers that spacetime from the sample. Target-as-input.
- **Structural block on the named rule.** `|LHS| = |RHS| = 4` forces edge-count conservation, hence linear cone growth; cone dimension ≈ 1 on every tested seed in two independent implementations.

### Lean-formal refutations

| Flaw | Lean module | Key theorem |
|---|---|---|
| F1 — discrete `g^{ab}` never constructed | `Refutations/F1NoMetric.lean` | `metric_construction_is_never_unique`; `no_canonical_metric_from_hypergraph_alone`; `action_depends_on_construction_choice` |
| F2 — fiat orthonormality | `Refutations/F2Orthonormality.lean` | `orthonormality_depends_on_form`; `orthonormalising_form_not_unique`; `gorard_orthonormality_is_non_canonical` |
| F3 — "dim preservation ⇒ EFE" is tautology | `Refutations/F3Tautology.lean` | `gorard_dim_preservation_is_euler_lagrange := Iff.rfl`; `gorard_section_3_3_contentless` |
| F4 — "causal invariance ⇔ general covariance" is tautology | `Refutations/F4Tautology.lean` | `gorard_causal_invariance_is_general_covariance := Iff.rfl` — certified to depend on **zero axioms** |
| F5 — "becomes" ill-defined | `Refutations/F5Illdefined.lean` | `becomes_is_underdetermined`; `claim_is_vacuous_without_convergence_notion`; `different_notions_give_different_limits` |
| F6 — G3 circular derivation | `Refutations/F6Circularity.lean` | `circular_reconstruction_has_no_content` (0 axioms); `circular_procedure_is_identity` — any Poisson-sprinkle-then-reconstruct returns its input |
| F7 — named rule is structurally 1-D | `Refutations/F7NamedRuleStructure.lean` + empirical | `namedRule_trajectory_edge_count_fixed`; `isConservative_implies_structurallyOneDim`; `conservative_blocks_dim_geq_one` (in `RuleSearch.lean`) |

**F8** (G4 title-body gap): not a formal claim but a documentary finding; Gorard concedes the gap in the paper's conclusion.

### Empirical refutation

- 2102.09363 named rule: `{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}`.
- SetReplace + an independent Python re-implementation agree on 9 seeds: causal-cone dimension ≈ 1 on each.
- The corresponding structural theorem: `|LHS|=|RHS|` ⇒ state size is conserved along every trajectory ⇒ ball volume is bounded by `Fintype.card V` ⇒ no `r^d` growth with `d ≥ 1` on any fixed finite vertex type.

### Summary verdict

Overclaim in multiple load-bearing places, with embedded arithmetic errors. The §3.3 Einstein-equations derivation uses objects that are never constructed (F1, F2). The logical spine reduces, in multiple places, to `Iff.rfl` (F3, F4). The continuum-limit step is left informal (F5). The G3 argument that a rule satisfies EFE is circular (F6). The named rule is empirically and structurally 1-dimensional (F7). The cited continuum identities are mis-stated by non-trivial factors on simple test manifolds. All errors are in the public record and checkable.

See [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md), [`FINDINGS.md`](FINDINGS.md), [`notes/corpus_assessment.md`](notes/corpus_assessment.md), and the close-reading notes for paper-by-paper detail.

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

MIT — see [`LICENSE.md`](LICENSE.md). Gorard paper sources in `papers/` are the original authors' and included only for reference.
