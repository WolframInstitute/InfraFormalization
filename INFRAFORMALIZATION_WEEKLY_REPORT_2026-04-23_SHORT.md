# Weekly report — 2026-04-23 (short version)

**Project.** `infra_formalization` — Lean 4 / Mathlib formalisation of the Wolfram-model → GR / QM bridge programme, plus a machine-checked audit of Gorard's published derivation claims (arXiv 2004.14810, 2011.12174, 2102.09363, 2303.07282). Comprehensive version attached.

## Numbers

- 140 Lean files, ~20k LOC, 3468 of 3468 `lake` build jobs succeed.
- 679 theorems + 17 lemmas + 17 examples proved; 381 definitions, 57 structures.
- 497 `#print axioms` certifications; every theorem reduces to `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no custom axioms.
- Infrageometry programme: 52 of 57 tasks closed with real content; 5 still open (IG10 exponential map; ID6 dimension compatibility; ID7 spectral dimension asymptotics; IB2 commutator theorem; IR7 reverse-engineer rule from signature).
- Grounding audit: 4 of 4 action items closed (no free-floating continuum objects at the obligation level).

## Why (audit of the Gorard corpus)

Gorard's headline claim: a specific hypergraph rewriting rule "provably satisfies the Einstein field equations in the continuum limit" (G3 abstract). Load-bearing flaws:

- **F1** — the discrete metric `g^{ab}` used in G1 §3.3 is never constructed, and any construction built from the hypergraph alone is non-canonical. Formalised in Lean as `Refutations/F1NoMetric.lean`.
- **F2** — "non-parallel hyperedges are orthonormal" declares a property of an unconstructed bilinear form. Formalised in `Refutations/F2Orthonormality.lean`.
- **F3** — "asymptotic dimensionality preservation ⇒ Einstein equations" unfolds to `Iff.rfl`; the preservation condition *is* the Euler-Lagrange equation of the Einstein-Hilbert action. Formalised in `Refutations/F3Tautology.lean`.
- **F4** — "causal invariance ⇔ discrete general covariance" is `Iff.rfl` (the two terms are defined as the same thing); the Lean certificate shows the proposition depends on **zero axioms**. Formalised in `Refutations/F4Tautology.lean`.
- **F5** — "discrete sum becomes continuum integral" is convergence-notion-dependent; no notion is specified. Formalised in `Refutations/F5Illdefined.lean`.
- **F6** — G3's "derivation" is the Poisson-sprinkle-then-reconstruct schema: the target spacetime is input, not output. `circular_procedure_is_identity` in Lean proves that any such procedure returns its input. Formalised in `Refutations/F6Circularity.lean`.
- **F7** — the named rule has `|LHS| = |RHS| = 4`, which forces state-size conservation, hence linear causal-cone growth, hence dimension ≤ 1 on every tested seed (confirmed in SetReplace and in an independent Python re-implementation). Formalised in `Refutations/F7NamedRuleStructure.lean`.
- **F8** — the G4 title promises "Discrete Singularity Theorems" that the body does not contain (no discrete Raychaudhuri, expansion scalar, energy condition, or stress-energy tensor; no "shear" or "vorticity" in the text). Documentary finding, not Lean-formalised.
- **Plus arithmetic errors.** Eq 342 (tube-volume coefficient): wrong by factor 2 on S², factor 6 on S³. Eq 344 (Ollivier Wasserstein): uses scalar `R` where Ollivier's cited theorem has directional `Ric(v,v)`.

**Verdict.** Systematic overclaim with embedded mathematical errors. Nothing fabricated; every error public and checkable.

## State of the discrete-continuum bridge

Legend for the State column:
- **proved** — the content of the rung is a machine-checked theorem.
- **partial** — some of the rung's content is proved; specific sub-items are listed open in the Content column.
- **flat case proved; curved case open** — the rung is proved when the underlying spacetime is flat (Minkowski / cycle / torus / lattice); the proof for a curved target (Schwarzschild, Kerr, FLRW) is open.
- **flat case proved end-to-end; curved case has the obligation Prop attached but the curved bridge theorem is open** — for Rung 10 specifically: every continuum GR target has an obligation Prop binding it to a hypergraph-side witness, flat-case witnesses are inhabited, curved-case witnesses are not.

| Rung | Topic | State | Content |
|---|---|---|---|
| 1 | Discrete calculus / Laplacian / heat kernel | proved | `Δ_H` on hypergraphs, self-adjoint, Dirichlet form, heat kernel `exp(t·Δ)` |
| 2 | Operator convergence | proved | Scaled second difference → `f''` for every C² function; scaled cycle eigenvalue → continuum circle Laplacian spectrum |
| 3 | Measure-theoretic limits | partial | Counting measure and pushforward proved; A6 weak convergence, A7 Wasserstein, A8 d-torus lift open |
| 4 | Connections / Levi-Civita | partial | Local-coordinate Christoffel and covariant derivative proved; bundle-theoretic formulation blocked by missing Mathlib infrastructure |
| 5 | Riemann / Ricci / Einstein tensors; GR metric zoo | proved | Local-coordinate curvature tensors; Minkowski, Schwarzschild, FLRW, Reissner-Nordström, Kerr, 2-sphere, de Sitter all bundled as `MetricData` / `PartialMetricData` |
| 6 | ODE / PDE on `Hypergraph V` | proved | Heat, wave, Klein-Gordon, Schrödinger (unitary), scalar-field Lagrangian + Euler-Lagrange; discrete heat → continuum heat on GH-limit |
| 7 | Fields / gauge | partial | Scalar field proved; discrete gauge field (G2) open |
| 8 | Lorentzian geometry | flat case proved; curved case open | Discrete Lorentzian lattice, Minkowski, `DiagLorentzianManifold`, causality conditions, Cauchy foliation from stably-causal time function; continuum Lorentzian Gromov-Hausdorff and curved-causal convergence open |
| 9 | Einstein equations | flat case proved; curved case open | `EinsteinEqLambda` predicate; Minkowski + flat connection solves vacuum EFE; flat connection forces Λ = 0; stress-energy type; energy conditions; Penrose and Raychaudhuri statements; Schwarzschild / FLRW / Kerr vacuum-EFE proofs pending |
| 10 | Hypergraph → GR | flat case proved end-to-end; curved case has the obligation Prop attached but the curved bridge theorem is open | Flat bridges proved: cycle → circle, path → interval, 2-torus, d-torus, discrete Lorentz → Minkowski; every continuum GR target carries an origin-obligation Prop; flat-case witnesses are inhabited; curved-case witnesses are not |

## Open items

Every item below is an active task; full per-task breakdown in [`NEXT_STEPS.md`](NEXT_STEPS.md) and [`COVERAGE_MAP.md`](COVERAGE_MAP.md).

- **Curved-target GR (Rungs 5 / 9).** Schwarzschild Riemann / Ricci / vacuum EFE (B2–B4), FLRW metric + Ricci + Einstein with perfect fluid (B6 in progress, B7), Reissner-Nordström (B8 in progress), Kerr (B9), Ricci symmetry (B10), second Bianchi (B11); explicit vacuum / matter solutions (F4 / F5 / F6); curved discrete-Ricci convergence (R4 in progress). Over the whole track: no known rewriting rule produces a curved target in the continuum limit; obligations attached, bridge theorems open.
- **Measure-theoretic limits (Rung 3).** A6 weak convergence counting → Lebesgue (in progress), A7 Wasserstein-1 rate O(1/n), A8 d-torus measure lift.
- **Bundle machinery / Levi-Civita (Rung 4).** C1 Riemannian bundle, C2 Lorentzian bundle, C3 vector-bundle connection, C4 torsion + curvature at bundle level, C5 Levi-Civita existence-uniqueness (Koszul), C6 bundle Γ consistency, C7 discrete connection on a hypergraph, C8 scaled discrete connection → Levi-Civita — blocked by missing Mathlib infrastructure.
- **PDE and Einstein evolution (Rungs 6 / 9).** D6 long-time heat → uniform convergence (in progress), D11 Choquet-Bruhat Cauchy problem; discrete stress-energy counterpart.
- **Fields and gauge (Rung 7).** G2 discrete gauge field via Rung-4 connection, G5 continuum limits of discrete fields, G6 HepLean integration.
- **Lorentzian geometry (Rung 8).** E5 full ADM lapse-shift decomposition (in progress; foliation existence done), E6 Lorentzian Gromov-Hausdorff, E7 discrete-causal-DAG → continuum Lorentzian convergence.
- **Numerical relativity (H-series).** Candidate-rule catalog, empirical signature pipeline + screens, scaled-trajectory convergence, curved RicciBridge extensions, BBH initial data / evolution / Ψ₄ extraction / merger convergence (H1–H9).
- **Combined / emergent frameworks (J-series).** Combined causal + branchial (J1), path integral over causal graphs (J2), emergent gravity à la Jacobson / Verlinde (J3), causal-set-theory comparison (J4), LQG spin-foam comparison (J5), AdS/CFT-analog (J6).
- **Quantum / branchial continuum (I-series).** I8 continuum limit of branchial Hilbert space, I10 full path-integral formulation.
- **Infrageometry programme open tasks.** IG10 exponential map via weighted shortest-path counts (pending); ID6 dimension compatibility on regular lattices (in progress); ID7 spectral-dimension small-`t` asymptotics (in progress); IB2 causal-branchial-trivial commutator (in progress); IR7 reverse-engineer rule from target signature (in progress). Separately, several infrageometry tasks are marked closed at a baseline but have substantive full forms still open as future work: IT5 Latschev GH-form, IT6 scale-trichotomy bulk, IQ6 Fubini-Study refinement limit, IQ8 EME-tracking functor, IQ9 path-integral amplitudes. T5 (path and d-torus Laplacian spectrum closed forms, in progress) sits outside the infrageometry programme but in the same spirit.
- **Rule search.** Large-scale empirical enumeration via `wolframscript` / SetReplace (task #190); Lean-side `RuleSearch.lean` catalog infrastructure in place.
- **Support (X-series).** X3 Mathlib Taylor integration (uniform C^k-on-compacts), X4 multi-way engine integration from `efficient_rewriting_final`.
- **Colleague-work (M-series).** M1 Ioana Milea IG-intern coordination, M3 Kolcz Lie-Poisson MBQC, M4 Pullman IBL-∞ / BV, M6 Pokorny paclet parity, M7 Ahmed EME community post, M8 Pokorny diffusion-geometry bridge, M9 tropical geometry, M10 3BP / dynamical-systems dimension signature.
- **Pavel Hájek planning items (P-series, P1–P19).** Simplicial machinery, cup product, discrete Chern-Simons amplitude, ribbon graphs + Whitehead moves, sheaves on hypergraphs, Koszul signs, homotopy colimit, filtrations of multiway systems, action principle, n-Lie extension of insertion bracket, interaction diagrams from causal graphs, chaos theory, Utkarsh twisted-difference operators, RG flow, observability tools, Knill geodesics, homotopy algebra scaffold, holography / Unruh, (1-skeleton, clique-cochain) decomposition. Mapping in [`NEXT_STEPS.md`](NEXT_STEPS.md) § "Pavel Hájek planning items (P-group)".
- **Paper drafts (K-series).** K1 audit paper, K2 corrected identities, K3 infrageometry continuum-limits, K4 structural library, K5 Wolfram → GR bridge, K6 branchial QM audit, K7 BBH via hypergraph, K8 discrete d'Alembertian + BD flag, K9 refutation-chain.

## Near-term priorities

1. **Rule-search pipeline**: enumerate small rules via `wolframscript`; compute their signatures; add hits to the Lean `RuleSearch.lean` catalog with signature-property theorems attached.
2. **Curved-Γ FiberedGraph bridge**: extend `FiberedGraphConnectionBridge` from the flat-connection witness to a non-trivial curved `Connection` approximating Schwarzschild's Γ at the horizon boundary.
3. **Measure bridges** A6 / A7 / A8.
4. **Paper drafts**: K1 (audit) and K3 (infrageometry continuum-limits; R1 / R2 / R5 / A3 / A4 form the technical core).
