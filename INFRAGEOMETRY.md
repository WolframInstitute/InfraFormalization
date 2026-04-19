# Infrageometry program — research roadmap

This file articulates the long-term research program within which the `infra_formalization` repository sits. The near-term phases (audit, refutation, corrections) are under active work; the long-term phases (positive infrageometry results) are the actual scientific goal.

## Framing

**Infrageometry**, as articulated at the Wolfram Institute, is the study of *discrete analogues of continuous geometric notions* — curvature, metric, volume, differential operators, connection, holonomy, parallel transport — constructed directly on discrete combinatorial structures (hypergraphs, causal sets, directed multigraphs) and made rigorous by *convergence theorems* connecting the discrete to the classical continuum.

The work in this repository has three components, in ascending difficulty and ambition:

1. **Audit and refutation.** Document where current claims in the Wolfram-physics literature (particularly the Gorard corpus) do not hold up to scrutiny. Produce precise counter-references.
2. **Correction.** For each identified error, state and (where possible) formalise the correct statement. Contribute to Mathlib where the correct statements require new infrastructure.
3. **Positive construction.** Build genuine discrete-to-continuum bridges: define discrete geometric structures rigorously, prove convergence theorems linking them to their classical continuum counterparts, and ultimately establish the first rigorous connections between *specific Wolfram-model rewriting dynamics* and *classical manifold geometry*.

The Gorard audit reveals that component (3) has been *claimed* but never actually executed in the Wolfram-physics literature. It is the serious scientific goal.

## Timescale, honestly

| Phase | Output | Realistic timescale |
|---|---|---|
| 0 | Audit complete, refutations documented | done |
| 1 | Lean formalisation of refutation-adjacent structural theorems (Edge Conservation, parallel-layer bound, in-degree bound) | 1–2 months |
| 2 | Lean formalisation of the *correct* continuum identities (Gray, Ollivier) with proofs | 3–6 months |
| 3 | First genuine continuum-limit theorem in Lean (e.g. $C_n \to S^1$ in Gromov–Hausdorff) | 3–6 months |
| 4 | Systematic Lean library of discrete geometric structures (metric-measure Ollivier–Ricci on directed hypergraphs with convergence theorems) | 6–12 months |
| 5 | First rigorous Wolfram-specific theorem: identify a family of hypergraph rewriting rules whose causal graphs provably GH-converge to a manifold with a specified metric | 1–2 years |
| 6 | Causal-set infrageometry: full Lean formalisation of Benincasa–Dowker action convergence (currently a conjecture in causal-set theory, would be a notable contribution) | 1–3 years |

No single phase can be rushed by "writing more tactic code." Each requires new mathematics or Lean-library infrastructure or both.

## Current status by phase

### Phase 0 — Audit
- Full claims catalog for G1 (arXiv:2004.14810) — [`notes/claims_catalog.md`](notes/claims_catalog.md)
- Cross-paper corpus audit — [`notes/corpus_audit.md`](notes/corpus_audit.md)
- Severity taxonomy S1–S6 — [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md)
- Close readings of G1, G3, G4 — [`notes/*_close_reading.md`](notes/)
- Single-way vs multi-way explainer — [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md)

**Phase 0: ✅ done.**

### Phase 1 — Structural Lean theorems

- Theorem A (edge conservation): ✅ machine-verified.
- Parallel-layer bound (real antichain theorem): ⏳ proof design drafted, implementation 2–4 days of focused Lean work.
- In-degree-exactly-k for conservative rules: ⏳ trivial once we have the predecessor-counting lemma.

**Phase 1: in progress. Next ship: parallel-layer bound, then in-degree theorem.**

### Phase 2 — Correct continuum identities

- Gray tube formula audit — ✅ done analytically (`results/phase2_continuum/eq342_verdict.md`).
- Ollivier identity audit — ✅ done (`results/phase2_continuum/eq344_verdict.md`).
- Lean formalisation of the correct Gray tube formula — ⏳ requires Fermi-normal-coordinates in Mathlib (partial; may require contribution).
- Lean formalisation of Ollivier's theorem — ⏳ requires optimal-transport + Riemannian-geometry bridge in Mathlib (currently in early stages; may require contribution).

**Phase 2: analytical correction done, Lean formalisation pending Mathlib maturity.**

### Phase 3 — First continuum-limit theorem in Lean

Candidate target: for $C_n$ (cycle graph on $n$ vertices) with metric scaled by $1/n$, the sequence GH-converges to the unit circle $S^1$ with its intrinsic metric.

Mathlib has:
- `Metric.HausdorffDist`
- partial `GromovHausdorff` API
- `Metric.Circle`

Missing:
- explicit ε-isometry construction $C_n \hookrightarrow S^1$
- Hausdorff-distance bound between image and $S^1$
- ε → 0 limit lemma

**Phase 3: not started. ~2–4 weeks of focused Lean work to complete one such theorem.**

### Phase 4 — Discrete geometric structures library

Targets:
- Rigorous `DirectedHypergraph` class with metric-measure-space instance.
- `OllivierRicci.directedHyperedge` definition with Lin–Lu–Yau normalisation.
- Convergence theorem: for iid-sampled random geometric graphs on a Riemannian manifold, the discrete Ollivier–Ricci converges to the Riemannian directional Ricci. (Trillos–Slepčev-style, adapted for Ollivier.)

**Phase 4: not started.**

### Phase 5 — First Wolfram-specific infrageometry theorem

**This is the goal.** Find (or construct) a class of hypergraph rewriting rules $\mathcal{R}$ with the property: for any initial seed in a specified class $\mathcal{S}$, the causal graphs produced by applying rules from $\mathcal{R}$ GH-converge to a specific manifold $(M, g)$. Prove it in Lean.

Candidates:
- Rules that approximate random geometric graph constructions. Convergence would follow from the discrete-to-continuum random-graph-limit theorems.
- Rules corresponding to known subdivision schemes (triangulations of surfaces, Penrose-type tilings, approximate lattices). Convergence could be via classical surface-approximation results.
- Rules with iterated-function-system interpretations, giving fractal limits.

**Phase 5: not started. This is the scientific prize.**

### Phase 6 — Causal-set infrageometry

The Sorkin–Benincasa–Dowker conjecture says: for a Poisson-sampled causal set in a Lorentzian spacetime, the expectation of the Benincasa–Dowker discrete action converges to the Einstein–Hilbert action. This is still conjectural in causal-set theory, supported by Cunningham-style numerical experiments.

A full Lean proof would:
- Require pseudo-Riemannian-GH infrastructure in Mathlib (currently absent).
- Proves a long-standing conjecture.
- Would be a notable result *independent* of the Wolfram-model framing.

**Phase 6: aspirational. Research-problem-level.**

## What's substantial and actionable *now*

In the next few weeks/months, the concrete deliverables are:

1. **Parallel-layer bound in Lean** (Phase 1). Completes the second real Lean theorem and makes the structural antichain argument precise.
2. **Short technical-comment preprint** summarising the Gorard-corpus audit for external circulation. Pre-requisite: decide whether we publish before, during, or after the Lean formalisation track lands.
3. **First continuum-limit theorem** ($C_n \to S^1$). Phase 3. Serves two purposes: first actual infrageometry theorem in Lean, plus template for subsequent discrete-to-continuum proofs.
4. **Discrete Ollivier–Ricci formalisation** for directed hypergraphs, following Eidi–Jost. Phase 4. The audit already identifies Gorard's Def 33; we state it correctly and (partially) prove its properties.
5. **Correct-Ollivier statement** in Lean as a named theorem, tied to Mathlib's Riemannian-geometry API. Phase 2. Even a *statement-only* Lean formalisation that matches Ollivier's JFA 2009 formula would be useful — it becomes the canonical reference against which subsequent Wolfram-physics papers can be checked.

## Principles

1. **Every theorem in the Lean library has zero `sorry`, zero `native_decide`, zero custom axioms.** Dependencies only on `propext`, `Classical.choice`, `Quot.sound`.
2. **Every claim has an audit trail.** If we're refuting something, the refutation is four-rail (independent derivation + symbolic + numerical + hand).
3. **Every convergence theorem names its topology.** "Continuum limit" is too vague; we commit to GH / spectral / pointwise / Γ-convergence explicitly.
4. **Every rule-specific result is rule-specific.** We do not claim structural theorems that are actually consequences of rule-plus-seed-specific combinatorics.
5. **Public-facing summaries distinguish what's proved from what's conjectured.** Tautology, refuted, ill-defined, open, proved — each is a distinct verdict in our taxonomy.

## Positioning

This work contributes to the Wolfram Institute's infrageometry program by:
- Providing a *verified baseline* of what can and cannot be proved in the current Wolfram-physics corpus.
- Building the *first formally-verified* discrete-to-continuum theorems in this tradition.
- Establishing a *repeatable template* for subsequent infrageometry claims to be evaluated against.

Ideally the result is not *just* a correction of Gorard but a foundation on which the Wolfram-physics community can build forward — with the confidence that structural claims can be formally verified, and that when they can't, the gap is documented precisely.
