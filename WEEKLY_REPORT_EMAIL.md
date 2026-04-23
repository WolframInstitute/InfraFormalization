# Weekly report — 2026-04-23 (email summary)

**Project.** `infra_formalization` — Lean 4 / Mathlib formalisation of the Wolfram-model → GR / QM bridge programme, plus a machine-checked audit of Gorard's published derivation claims (arXiv 2004.14810, 2011.12174, 2102.09363, 2303.07282). Comprehensive version attached.

## Numbers

- 140 Lean files, ~20k LOC, 3468/3468 `lake` build jobs green.
- 679 theorems + 17 lemmas + 17 examples proved; 381 definitions, 57 structures.
- 497 `#print axioms` certifications; every theorem reduces to `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no custom axioms.
- Infrageometry programme: 50 / 57 tasks closed with real content; 7 in-flight.
- Grounding audit: 4 / 4 action items closed.

## Why (audit of the Gorard corpus)

Gorard's headline claim: a specific hypergraph rewriting rule "provably satisfies the Einstein field equations in the continuum limit" (G3 abstract). Load-bearing flaws, each now a Lean theorem:

- **F1** — discrete metric `g^{ab}` used in G1 §3.3 is never constructed; any construction is non-canonical.
- **F2** — "non-parallel hyperedges are orthonormal" declares a property of an unconstructed bilinear form.
- **F3** — "asymptotic dimensionality preservation ⇒ EFE" unfolds to `Iff.rfl`; the condition *is* the Euler-Lagrange equation.
- **F4** — "causal invariance ⇔ discrete general covariance" = `Iff.rfl` (the two terms are defined as the same thing); certified "does not depend on any axioms".
- **F5** — "discrete sum becomes continuum integral" is convergence-notion-dependent; no notion specified.
- **F6** — G3's "derivation" is the Poisson-sprinkle-then-reconstruct schema: target spacetime is input, not output. `circular_procedure_is_identity` proves any such procedure returns its input.
- **F7** — named rule `|LHS|=|RHS|=4` forces state-size conservation, hence linear cone growth, hence dimension ≤ 1 on every tested seed (SetReplace + independent Python).
- **F8** — G4 title promises discrete singularity theorems that the body does not contain.
- Plus arithmetic errors: Eq 342 tube coefficient wrong by factor 2 on S², factor 6 on S³; Eq 344 uses scalar `R` where Ollivier's theorem has directional `Ric(v,v)`.

Verdict: systematic overclaim with embedded mathematical errors. Nothing fabricated; every error public and checkable.

## State of the discrete-continuum bridge

| Rung | Topic | State |
|---|---|---|
| 1 | Discrete calculus / Laplacian / heat kernel | ✅ |
| 2 | Operator convergence (scaled Δ → d²/dx², cycle spectrum → circle spectrum) | ✅ |
| 3 | Measure limits (counting measure ✅; A6 weak, A7 Wasserstein, A8 d-torus open) | ⚠ |
| 4 | Connections / Levi-Civita (local-coord ✅; Mathlib bundle gap) | ⚠ |
| 5 | Riemann / Ricci / Einstein tensors; GR metric zoo (Minkowski, Schwarzschild, FLRW, RN, Kerr, S², de Sitter) | ✅ |
| 6 | Heat / wave / Klein-Gordon / Schrödinger-unitary / scalar-field EL on `Hypergraph V`; discrete heat → continuum heat | ✅ |
| 7 | Fields (scalar ✅; gauge open) | 🟡 |
| 8 | Lorentzian (discrete ✅; continuum `DiagLorentzianManifold` ✅; Cauchy foliation ✅; Lorentzian GH open) | ✅ flat |
| 9 | Einstein equations (`EinsteinEqLambda` ✅; Minkowski vacuum ✅; flat forces Λ=0) | ✅ flat |
| 10 | Hypergraph → GR (flat bridges proved; curved obligations attached, `bridgeHolds` open) | ✅ flat / obligation-level |

Flat bridges proved: cycle → circle, path → interval, 2-torus, d-torus, discrete Lorentz → Minkowski.

## What's new since 2026-04-22

Grounding-audit closure — every continuum GR object now carries an attached hypergraph-side origin-obligation Prop, with flat-case witnesses proved:

- `HypergraphMetricOriginObligation M` — every metric in the zoo.
- `ConnectionDataOriginObligation C` — flat connection case witnessed via a trivial fibered graph.
- `LorentzianManifoldOriginObligation target` — Minkowski manifold witnessed via trivial causal graph.
- `EFEOriginObligation M C Λ κ T x` — bundles EFE satisfaction + metric origin + connection origin. `minkowski4_flat_vacuum_EFE_originated_global` is the first complete rule → metric → connection → EFE chain.
- `RuleSearch.lean` — 5-rule catalog (identity, self-map, edge-duplicate, triple-to-edge, pair-to-triangle); decidable `IsConservative`; `conservative_blocks_dim_geq_one` formalises the F7 structural obstruction.

## Open items

Curved rule → curved metric bridges (Schwarzschild, Kerr, FLRW) — no known rule; correctly open. Measure theory A6/A7/A8. Mathlib bundle gap blocks C1–C8. G2 gauge field. E6/E7 Lorentzian GH. Discrete stress-energy. Large-scale empirical rule search via wolframscript.

## Near-term priorities

1. Rule-search pipeline — wolframscript enumeration, signatures, hits back into `RuleSearch.lean`.
2. Curved-Γ FiberedGraph bridge — extend from flat witness to non-trivial curved `Connection F`.
3. Measure bridges A6 / A7 / A8.
4. Paper drafts K1 (audit) and K3 (infrageometry continuum-limits).
