# Publishable outputs — target list

Working list of concrete publishable units the infrageometry programme is heading toward. Each is a real paper or technical note with an identifiable audience; each names the sufficient condition on our work for the paper to be ready.

Grouped from most-immediate (parts already done) to most-ambitious.

## P1 — Audit and formal refutation of the Gorard corpus

**One-line pitch.** A machine-checked audit of arXiv:2004.14810, 2011.12174, 2102.09363, 2303.07282 showing that the central claim — that general relativity has been derived from Wolfram-model hypergraph rewriting — has not been established. Each specific error and structural flaw is documented at citation-precision and **formally refuted in Lean**.

**Status.** Ready *now* as a v1 arXiv preprint.

**Sufficient conditions.**
- [x] S1/S2/S6 error taxonomy with TeX line references
- [x] F1–F5 structural flaws **formally refuted in Lean** (`Refutations/F1-F5*.lean`), all axiom-clean
- [x] Corpus-wide cross-paper propagation map
- [x] Continuum-limit claims catalog
- [x] Line-by-line close readings of all four Gorard papers
- [x] Edge conservation proved in Lean (underpins F7 refutation)
- [x] Named rule empirically refuted (SetReplace + independent Python rewriter)
- [ ] A short (≤ 15 page) technical-comment-style PDF
- [ ] External review by Wolfram Institute colleagues

**Audience.** *Complex Systems* (published G1, G2); arXiv math-ph + gr-qc cross-listing.

**Load-bearing Lean theorems:**
- F1: `Refutations.F1NoMetric.hypergraph_does_not_determine_metric`
- F2: `Refutations.F2Orthonormality.orthonormality_depends_on_form`
- F3: `Refutations.F3Tautology.gorard_dim_preservation_is_euler_lagrange` (Iff.rfl)
- F4: `Refutations.F4Tautology.gorard_causal_invariance_is_general_covariance` (axiom-free)
- F5: `Refutations.F5Illdefined.becomes_is_underdetermined`
- F6: `DiscreteDAlembertian.BenincasaDowkerConjecture` (explicit unproven-load-bearing flag)
- F7: `Application.size_result_of_conservative`

## P2 — Corrected continuum identities formalised

**One-line pitch.** The correct versions of the Ollivier–Ricci identity and the Gray tube formula, expressed as Lean definitions, with their disagreement with Gorard's forms machine-verified at concrete test manifolds.

**Status.** Statement-level formalisation complete; proofs of the correct identities pending Mathlib's Riemannian + optimal-transport infrastructure.

**Sufficient conditions.**
- [x] `OllivierStatement.OllivierIdentityLeading` + `GorardMisstatedForm` + coincidence theorem
- [x] `GrayTubeStatement.GrayTubeLeading` + `gray_vs_gorard_disagree_on_S2/S3`
- [ ] Full proofs of the correct identities (Mathlib Ricci/Wasserstein dependency)

**Audience.** arXiv math.DG + math-ph.

## P3 — Infrageometry continuum-limit templates (cycle, path, torus, Lorentz)

**One-line pitch.** A Lean library of discrete-to-continuum Gromov-Hausdorff bounds: cycle → circle, path → interval, (d+1)-lattice → (d+1)-torus, and int-lattice → Minkowski. Unified under a common `GHApproximation` structure.

**Status.** Complete up to flat-space targets; curved-target extensions await Mathlib Ricci.

**Sufficient conditions.**
- [x] `cycle_circle_gh_bound`
- [x] `path_interval_gh_bound`
- [x] `torus_gh_bound` (2D) and `dTorus_gh_bound` (arbitrary d)
- [x] `lorentzIntEmbed_preserves_causal_iff` (exact Minkowski causal correspondence)
- [x] `scaledLorentzEmbed_dense` + `_spaceDist_eq_cast` (scaled isometry + density)
- [ ] 25-page paper with the Lean library as appendix

**Audience.** arXiv math.MG + math-ph + formal-methods.

## P4 — Wolfram-model structural theorems library

**One-line pitch.** A Lean library of structural theorems about hypergraph rewriting — edge conservation, degree sums, causal-DAG level monotonicity, same-level antichain, hypergraph calculus — all axiom-clean.

**Status.** Substantially more than earlier. 200+ theorems across the Lean corpus, all axiom-clean.

**Sufficient conditions.**
- [x] Edge conservation, degree sums, balance
- [x] Level monotonicity + same-level antichain (forward)
- [x] **Hypergraph Laplacian** + self-adjointness + Dirichlet form + PSD + divergence theorem
- [x] **Forman-Ricci** (simple + hypergraph) + cycle=0 bridge
- [x] **Cycle Laplacian = central second difference** (interior-point identification)
- [x] **Scaled-second-difference = f''** (polynomial case, Mathlib `deriv`-level)
- [ ] Trajectory-structure lemma (consumed expressions ≤ earlier produced)
- [ ] Full parallel-layer bound `|layer_s| ≤ N/k`
- [ ] 25-page paper

**Audience.** arXiv cs.LO + math.CO + formal-methods.

## P5 — First provable Wolfram-to-GR bridge

**One-line pitch.** A rewriting rule whose evolution is proved to converge in Gromov–Hausdorff sense to a specific Lorentzian manifold; with discrete curvature on the causal graph converging to the continuum Ricci. The first such rigorous result.

**Status.** **Open research problem** (candidate rule). But substantial infrastructure in place.

**Sufficient conditions.**
- [x] `Infra/LorentzLattice.lean` + `Infra/Minkowski.lean` + `Infra/FullBridge.lean` — discrete causal-graph ↔ continuum Minkowski, exact isometry + bridge theorems.
- [x] **`DiscreteDAlembertian`** — Benincasa-Dowker operator on trajectories, `discreteAction`, `discreteEL`. The Gorard-attempted-but-failed operator, now formalised.
- [x] **`BenincasaDowkerConjecture`** explicitly flagged as an open `Prop`-level hypothesis.
- [x] **Forman-Ricci → continuum Ricci** bridge on the cycle/circle (`RicciBridge.lean`) — first discrete-to-continuum curvature match.
- [x] **`leviCivitaConnection : MetricDataC2 → ConnectionData`** — full local-coord curvature derivation.
- [x] **Schwarzschild components + Γ^1_{00} computation** (`Schwarzschild.lean`).
- [ ] At least one candidate rule identified (or engineered).
- [ ] Convergence theorem for that rule.

**Audience.** arXiv gr-qc + math-ph (*Physical Review D* / *Classical and Quantum Gravity* / *Foundations of Physics*). This would be the headline result.

## P6 — Branchial quantum mechanics audit + formalisation

**One-line pitch.** Gorard's claim that branchial structure recovers quantum mechanics, audited with the same methodology as P1, with corrected and formalised versions in Lean where the claim survives.

**Status.** Partial infrastructure.

**Sufficient conditions.**
- [x] `Branchial.lean` — `BranchialRelated`, `NStep`, `BranchialSlice`. Basic structure.
- [ ] Complete S1–S6 audit of Gorard's QM paper (arXiv:2004.14808)
- [ ] Branchial measure: uniform probability on finite slices.
- [ ] Branchial amplitudes; ℓ² Hilbert-space limit.
- [ ] State / prove the branchial → QM bridge claim (or refute it).

**Audience.** arXiv quant-ph + math-ph.

## P7 — Binary-black-hole merger via hypergraph rewriting

**One-line pitch.** Hypergraph-level BBH initial data, evolved under an established Wolfram-to-GR rule (from P5), with proved convergence to the merger spacetime.

**Status.** **Depends on P5.** The scientific prize advertised (but not delivered) in G3.

**Sufficient conditions.**
- [ ] P5 completed
- [ ] Discrete Brill–Lindquist initial data on a hypergraph
- [ ] Evolution under the P5 rule
- [ ] Discrete Ψ₄ extraction matching BBH waveforms
- [ ] Lorentzian-GH convergence to a merger spacetime

**Audience.** Same as P5.

## P8 — Formalised discrete d'Alembertian + Benincasa-Dowker conjecture flag

**One-line pitch.** A Lean formalisation of the Benincasa-Dowker discrete d'Alembertian on a Wolfram-model trajectory's causal DAG, with the continuum-limit `B_ρ → □ − ½R` explicitly recorded as an open `Prop`-level conjecture. This closes the F6 "Gorard's circular EFE derivation" gap on the discrete side: the operator is fully defined, its linearity is proved, and the unproven load-bearing claim is machine-flagged.

**Status.** Core done (`DiscreteDAlembertian.lean`). Ready as a short technical note.

**Sufficient conditions.**
- [x] `openInterval`, `intervalSize`, `layer τ k i`, `discreteDAlembertian4` defined and proved linear.
- [x] `discreteAction` (Gorard Eq 86 analog), `discreteEL` (EL equation).
- [x] `BenincasaDowkerConjecture` structure; `gorardF6_carries_BD_assumption`.
- [x] `layer_disjoint`, `mem_layer_isCausalPred` structural lemmas.
- [ ] General-dimension `discreteDAlembertian_d` (coefficients indexed by `d`).
- [ ] 10-page note with motivations + connection to F6 + BD literature review.

**Audience.** arXiv gr-qc + hep-th (*Classical and Quantum Gravity* as a Letter).

## P9 — Machine-checked refutation of Gorard's EFE derivation chain

**One-line pitch.** A self-contained paper walking through Gorard's prose derivation of the Einstein field equations from Wolfram-model dynamics, showing at each step which move is tautological (F3, F4), ill-defined (F5), circular (F6), or unsupported (F1, F2). Every refutation is a cited Lean theorem.

**Status.** All pieces formalised; drafting ready to begin.

**Sufficient conditions.**
- [x] F1 refuted: `hypergraph_does_not_determine_metric`.
- [x] F2 refuted: `orthonormality_depends_on_form`.
- [x] F3 refuted: `gorard_dim_preservation_is_euler_lagrange` (Iff.rfl).
- [x] F4 refuted: `gorard_causal_invariance_is_general_covariance` (axiom-free).
- [x] F5 refuted: `becomes_is_underdetermined`.
- [x] F6 flagged: `BenincasaDowkerConjecture`.
- [x] Positive construction (hypergraph anchor) exists for each "what Gorard should have formalised" move.
- [ ] 15-page paper draft

**Audience.** arXiv gr-qc + cs.LO. This is the direct counter-paper.

## Dependencies and ordering

```
P1 (audit) ──────────────────┐
P2 (correct identities) ─────┤
P3 (continuum templates) ────┤
P4 (structural library) ─────┤
P8 (discrete d'Alembertian) ─┤
P9 (refutation chain) ───────┘
                             │
                             ▼
                            P5 (Wolfram → GR)
                           /       \
                          ▼         ▼
                         P7 (BBH)   P6 (QM branchial)
```

P1–P4, P8, P9 are independent; most content exists. P5 is the research gate for the physics prize; P7 depends on P5; P6 is orthogonal but necessary for quantum gravity.

## Conventions and process

- Every paper target names at least one Lean theorem it cites. Papers are **proof-assistant-backed**.
- Each paper's draft PDF lives under `reports/`.
- *No paper leaves the lab without passing internal review.*
- The project exists to correct overclaim in Wolfram physics; we do not add to it.
