# Publishable outputs — target list

Working list of concrete publishable units the infrageometry programme is heading toward. Each is a real paper or technical note with an identifiable audience; each names the sufficient condition on our work for the paper to be ready.

Grouped from most-immediate (parts already done) to most-ambitious.

## P1 — Audit and refutation of the Gorard corpus

**One-line pitch.** A machine-checked audit of arXiv:2004.14810, 2011.12174, 2102.09363, 2303.07282 showing that the central claim — that general relativity has been derived from Wolfram-model hypergraph rewriting — has not been established, with each specific error and each specific structural flaw documented at citation-precision and backed by Lean proofs where applicable.

**Status.** Ready *now* as a v1 arXiv preprint. We have the S1–S6 taxonomy, the F1–F8 major-flaw list, the corpus-wide propagation map, the continuum-limit claim catalog, line-by-line close-readings, and Lean machine-verification of the structural lemmas ($|LHS|=|RHS|$ conservation + the named-rule 1-D refutation).

**Sufficient conditions.**
- [x] S1/S2/S6 errors documented with TeX line references
- [x] Edge conservation proved in Lean (underpins F7 refutation)
- [x] Named rule empirically refuted (two independent implementations)
- [ ] A short (≤ 10 page) technical-comment-style PDF compiling the above
- [ ] External review by Wolfram Institute colleagues

**Audience.** Complex Systems (journal that published G1, G2, G3-companion); arXiv math-ph + gr-qc cross-listing. The audit is not hostile to the programme — it is a correction + foundation.

**Why this paper exists.** People downstream are citing the Gorard corpus as having established the result. There is no single public reference articulating where it falls short. This paper is it.

## P2 — Corrected continuum identities formalised

**One-line pitch.** The correct versions of the Ollivier–Ricci identity and the Gray tube formula, expressed as Lean definitions, with their disagreement with the forms in Gorard's corpus machine-verified at concrete test manifolds.

**Status.** `OllivierStatement.lean` and `GrayTubeStatement.lean` carry the statements; `gray_vs_gorard_disagree_on_S2/S3` prove the disagreement. Full *proofs* of the correct identities are pending Mathlib Riemannian + optimal-transport infrastructure.

**Sufficient conditions.**
- [x] Correct identities stated in Lean
- [x] Disagreement proven at specific test manifolds
- [ ] Full Lean proofs of the correct identities (Mathlib-contribution-scale)
- [ ] Short note (≤ 15 pages) explaining the two corrections

**Audience.** arXiv math.DG + math-ph + formal-methods cross-listing. Secondary: a Mathlib contribution.

## P3 — Infrageometry continuum-limit templates formalised

**One-line pitch.** A reusable Lean template `GHApproximation` for discrete-to-continuum Gromov–Hausdorff convergence, instantiated for three examples (scaled cycle → unit circle, scaled path → unit interval, scaled $n \times n$ lattice → flat 2-torus), with all proofs machine-verified and axiom-clean.

**Status.** Complete at the present-instance level. Three instances done, abstract structure done.

**Sufficient conditions.**
- [x] Three instances proved (cycle, path, torus)
- [x] Common abstraction (`GHApproximation`)
- [ ] At least one of: scaled $d$-dim lattice → flat $d$-torus, or random geometric graph → manifold
- [ ] Formal ε-density ⇒ GH-convergence bridge theorem via Mathlib's `GromovHausdorff`
- [ ] Short note (≤ 20 pages) introducing the library

**Audience.** arXiv math.MG + math-ph + formal-methods cross-listing.

## P4 — Wolfram-model structural theorems library

**One-line pitch.** A Lean library of structural theorems about hypergraph rewriting — edge conservation, degree sums, causal-DAG level monotonicity, same-level antichain property — all axiom-clean, with implications for the structural limits of any Wolfram-model-style rule.

**Status.** 15 theorems currently proved; the full parallel-layer bound and the trajectory-structure lemma are still pending.

**Sufficient conditions.**
- [x] Edge conservation, degree sums, balance
- [x] Level monotonicity along causal edges (T13)
- [x] Same-level antichain (forward direction)
- [ ] Trajectory-structure lemma (consumed expressions ≤ earlier produced)
- [ ] Full parallel-layer bound `|layer_s| ≤ N/k`
- [ ] Short note (≤ 25 pages), with the Lean library as an appendix

**Audience.** arXiv cs.LO + math.CO + formal-methods.

## P5 — First provable Wolfram-to-GR bridge

**One-line pitch.** A rewriting rule whose evolution is proved to converge in Gromov–Hausdorff sense to a specific Lorentzian manifold. The first such rigorous result.

**Status.** **Open research problem.** Candidates under the infrageometry programme:
- Rules implementing random-geometric-graph constructions on a manifold
- Causal-set-adjacent rules relying on Benincasa–Dowker convergence (which is itself open)
- Causal Dynamical Triangulation-style rules

**Sufficient conditions.**
- [ ] At least one candidate rule identified (or engineered)
- [ ] Convergence proof (with Lean machine-verification optional but strongly preferred)
- [ ] Comparison of the limit against the claimed Einstein-equation solution

**Audience.** arXiv gr-qc + math-ph (*Physical Review D* / *Classical and Quantum Gravity* / *Foundations of Physics*). This would be the headline result of the programme.

## P6 — Quantum-mechanical branchial-structure formalisation

**One-line pitch.** Gorard's claim that branchial structure recovers quantum mechanics, audited with the same S1–S6 methodology, with corrected and formalised versions in Lean where the claim survives audit.

**Status.** Gorard's companion QM paper (arXiv:2004.14808) *has not been audited by this project yet*. Included here because, if the branchial-structure-to-QM bridge is real, it is the other half of the programme — without it, even a successful Wolfram-to-GR bridge (P5) leaves QM unexplained.

**Sufficient conditions.**
- [ ] Complete S1–S6 audit of Gorard's QM paper
- [ ] Formalise `MultiwayEvolution` and `BranchialGraph` in Lean (cross-reference `../efficient_rewriting_final/`)
- [ ] State / prove the branchial → QM bridge claim (or refute it)

**Audience.** arXiv quant-ph + math-ph.

## P7 — Binary-black-hole merger via hypergraph rewriting

**One-line pitch.** Hypergraph-level representation of BBH initial data, evolved under an established Wolfram-to-GR rule (from P5), with proved convergence to the merger spacetime and quantitative comparison against analytical / numerical BBH ringdown.

**Status.** **Depends on P5**. Without a proved Wolfram-to-GR rule, P7 has no starting point. It is the scientific prize sub-goal that was advertised (but not delivered) in G3.

**Sufficient conditions.**
- [ ] P5 completed
- [ ] Discrete representation of Brill–Lindquist-type initial data on a hypergraph
- [ ] Evolution of said data under the P5 rule
- [ ] Discrete Ψ₄ extraction matching BBH waveforms
- [ ] Lorentzian-GH convergence of the trajectory to a known merger spacetime

**Audience.** Same as P5. This would be the headline *physics* result.

## Dependencies and ordering

```
P1 (audit) ──────────┐
P2 (correct identities) ─┤
P3 (continuum templates) ──────── P4 (structural library)
                                       │
                                       ▼
                                      P5 (Wolfram → GR)
                                     /       \
                                    ▼         ▼
                                   P7 (BBH)   P6 (QM branchial)
```

P1–P4 are independent; most of their content already exists. P5 is the research gate: until we have a candidate rule with provable GR limit, P7 (BBH) cannot begin. P6 (QM) is orthogonal but ultimately necessary because a theory of quantum gravity can't derive only GR.

## Conventions and process

- Every paper target above names at least one Lean theorem it cites. Papers are *proof-assistant-backed*, not just expository.
- Each paper's draft PDF lives under `reports/` (currently empty; first draft pending).
- Reviews and external feedback threads live under `reports/reviews/`.
- *No paper leaves the lab without passing an internal review*; we are committed to not adding to the body of overclaim-in-Wolfram-physics that this programme exists to correct.
