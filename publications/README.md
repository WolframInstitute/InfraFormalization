# Publications

Each subfolder is, eventually, one paper — a LaTeX manuscript backed by Lean-verified theorems. **Right now we are upstream of that.** We are generating the *results* — theorems, corrections, continuum-limit bridges — and a paper will be written only when a subfolder has genuine significant content that is *ready*. The abstracts in place today are aspirational targets ("this is what this paper will claim when we draft it"); they are not manuscripts.

**Principle.** No paper enters draft stage until:
1. its Lean-side support is complete and axiom-clean (per `MILESTONES.md`);
2. its distinct contribution over existing literature is clear (not "this classical result, but in Lean");
3. at least one Wolfram Institute colleague agrees the result is worth writing up.

Until then, this directory is a *planning artifact*. Paper-significant progress means Lean theorems landing on our side of the `MILESTONES.md` ledger, not paragraphs in `abstract.md`.

---

## Original framing (kept for reference)

## Architecture

Two tiers, built as a tower — each major paper rests on several incremental ones that each stand alone:

### Incremental papers (focused, self-contained)

Each is a single mathematical-physics result — a corrected continuum identity, a continuum-limit theorem, a structural theorem about hypergraph rewriting, a refined empirical observation about a specific rule. Small: usually ≤ 20 pages, single-thesis. Publishable in isolation.

### Major papers (synthesis-level)

Each collects multiple incremental results to make a larger claim. The major paper on the JGORARD audit cites each incremental technical correction. The major paper on Wolfram-to-GR would rest on several Phase-4 infrageometry incremental papers.

## Framing

The programme is about **reframing traditional continuous notions in a discrete manner that is rigorous, Lean-verified, and convergent**. Every incremental paper is an instance of this: we take a continuum concept (Ricci, metric, volume, action, gauge, connection) and (a) refute any incorrect prior discretisation, (b) provide the correct one, (c) prove convergence, (d) formalise in Lean.

## Planned subfolders

Each folder contains:
- `paper.md` or `paper.tex` — the manuscript draft
- `abstract.md` — one-paragraph pitch
- `lean-dependencies.md` — which theorems from `lean/InfraFormalization/` support the claims
- `reviews/` — internal and external review notes
- `figures/` — if any

### Incremental papers (targets)

- [`publications/I01-edge-conservation/`](I01-edge-conservation/) — Edge conservation and structural bounds on conservative Wolfram-model rules (*draftable now from T1–T10 + T13–T15*).
- [`publications/I02-cycle-circle-gh/`](I02-cycle-circle-gh/) — Formally-verified cycle-to-circle Gromov–Hausdorff convergence (*draftable now from T19 + T20 + T21*).
- [`publications/I03-path-interval-gh/`](I03-path-interval-gh/) — Path-to-interval variant, or combined with I02.
- [`publications/I04-torus-gh/`](I04-torus-gh/) — 2D lattice-to-torus, same template generalised.
- [`publications/I05-ollivier-correction/`](I05-ollivier-correction/) — Correction of the Ollivier-Ricci identity for discrete hypergraphs, with directional-vs-scalar distinction preserved. *Draftable now as a short note from T27 + T28 + T30 + T31.*
- [`publications/I06-gray-tube-correction/`](I06-gray-tube-correction/) — Correction of the Gray tube formula with concrete disagreement proofs.
- [`publications/I07-named-rule-refutation/`](I07-named-rule-refutation/) — Empirical + structural refutation of the arXiv:2102.09363 named rule.

### Major papers (targets)

- [`publications/M01-gorard-corpus-audit/`](M01-gorard-corpus-audit/) — The full JGORARD-corpus audit, synthesising the incremental corrections I05, I06, I07 and the S1–S6 + F1–F8 structural-flaw classifications. **The major refutation paper.**
- [`publications/M02-infrageometry-foundations/`](M02-infrageometry-foundations/) — Foundations of the infrageometry programme: what it means for a discrete structure to converge to a continuum geometric one, unified via `GHApproximation`. Synthesises I02, I03, I04.
- [`publications/M03-wolfram-gr-bridge/`](M03-wolfram-gr-bridge/) — **The scientific prize**: the first provable Wolfram-rewriting-to-GR bridge. Depends on open research — see `MILESTONES.md` Phase 5.
- [`publications/M04-bbh-hypergraph-merger/`](M04-bbh-hypergraph-merger/) — Binary-black-hole hypergraph evolution to merger. Depends on M03.

## Workflow per paper

1. Decide paper (add folder above with skeleton).
2. Write `abstract.md` first.
3. Map `lean-dependencies.md` against existing theorems in `lean/InfraFormalization/`. *If* gaps exist, add them to `MILESTONES.md` and prove before writing.
4. Draft `paper.md`.
5. Internal review (2+ reviewers marked in `reviews/`).
6. Polish to LaTeX.
7. Submit.
