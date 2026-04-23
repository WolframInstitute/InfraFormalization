# Weekly report — 2026-04-23 (email summary)

**Project.** `infra_formalization` — Lean 4 / Mathlib formalisation of the Wolfram-model → GR / QM bridge programme, plus a machine-checked audit of Gorard's published derivation claims (arXiv 2004.14810, 2011.12174, 2102.09363, 2303.07282). Comprehensive version attached.

## Numbers

- 140 Lean files, ~20k LOC, 3468 of 3468 `lake` build jobs succeed.
- 679 theorems + 17 lemmas + 17 examples proved; 381 definitions, 57 structures.
- 497 `#print axioms` certifications; every theorem reduces to `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no custom axioms.
- Infrageometry programme: 50 of 57 tasks closed with real content; 7 in progress with substantive open content.
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

## Research directions on file

Items from Pavel Hájek's weekly update and Discord core dump (2025-10-06 to 2026-04-14) have been mapped against the library and tracked as tasks **P1–P19**. Highlights: P1 delta / simplicial machinery on hypergraphs; P3 discrete Chern-Simons amplitude (overlaps M4 Pullman IBL-∞); P4 ribbon (hyper)graph structure + Whitehead moves; P5 sheaves on hypergraphs; P6 Koszul signs; P7 homotopy colimit of multiway systems; P9 action principle for rewriting; P10 n-Lie extension of the insertion bracket; P13 Utkarsh Bajaj twisted-difference operators (ring-of-functions reconstruction); P16 Knill geodesics approximating Riemannian geodesics. Full item-by-item mapping in [`RESEARCH_DIRECTIONS.md`](RESEARCH_DIRECTIONS.md).

## Open items

- Curved rule → curved metric bridges (Schwarzschild, Kerr, FLRW): no known rewriting rule produces these in the continuum limit; the obligation is attached, the bridge theorem is open.
- Measure theory A6 (weak convergence of the counting measure to Lebesgue), A7 (Wasserstein-1 rate O(1/n)), A8 (d-torus measure lift).
- Mathlib gap for Riemannian / Lorentzian vector bundles blocks the bundle-theoretic Levi-Civita track (C1–C8).
- G2 discrete gauge field via a Rung-4 connection.
- E6 Lorentzian Gromov-Hausdorff; E7 discrete-causal → continuum-Lorentzian convergence.
- Discrete stress-energy tensor counterpart.
- Large-scale empirical rule search via `wolframscript` / SetReplace: the Lean-side infrastructure is in place in `RuleSearch.lean`; large-scale enumeration is pending.

## Near-term priorities

1. **Rule-search pipeline**: enumerate small rules via `wolframscript`; compute their signatures; add hits to the Lean `RuleSearch.lean` catalog with signature-property theorems attached.
2. **Curved-Γ FiberedGraph bridge**: extend `FiberedGraphConnectionBridge` from the flat-connection witness to a non-trivial curved `Connection` approximating Schwarzschild's Γ at the horizon boundary.
3. **Measure bridges** A6 / A7 / A8.
4. **Paper drafts**: K1 (audit) and K3 (infrageometry continuum-limits; R1 / R2 / R5 / A3 / A4 form the technical core).
