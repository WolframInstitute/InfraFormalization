# Project index

Complete navigation for `infra_formalization`. This file is hand-maintained; every document in the repo appears below with a one-line description. New readers: start at [`README.md`](README.md), then read sections in the order suggested.

## Start here

| Document | Purpose |
|---|---|
| [`README.md`](README.md) | Entry point — project posture, verdict status table, reproduction instructions, layout. |
| [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) | Research program: long-term roadmap (audit → correction → positive construction); phases 0–6 with honest timescales. |
| [`GLOSSARY.md`](GLOSSARY.md) | Definitions of every technical term used in this project (causal invariance, branchial graph, tetrad, Ollivier–Ricci, infrageometry, etc.). |
| [`FINDINGS.md`](FINDINGS.md) | Canonical one-line summary of every refuted / verified / open claim, grouped by severity. |
| [`NEXT_STEPS.md`](NEXT_STEPS.md) | What's done, what's in flight, what's waiting for a decision. |

## Methodology and synthesis

| Document | Purpose |
|---|---|
| [`notes/plan.md`](notes/plan.md) | 7-phase verification methodology with quadruple-rail rules. |
| [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) | S1–S6 classification of all 16 distinct errors, with a discussion of how the errors recur. |
| [`notes/corpus_audit.md`](notes/corpus_audit.md) | Cross-paper map: which errors originate in which paper and propagate to which others. |
| [`notes/claim_assessment.md`](notes/claim_assessment.md) | Per-claim synthesis (True / Conjectural / Hunch / Tautology / Error) with overall verdict: "the texts claim more than their arguments establish, and contain no fabricated data." |
| [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) | Why Gorard uses single-way evolution, why this is inconsistent, why our refutations still hold, where the null tetrad and GR machinery actually live. |

## Per-paper close-readings

| Document | Paper | Focus |
|---|---|---|
| [`notes/2004.14810_close_reading.md`](notes/2004.14810_close_reading.md) | G1 — *Some Relativistic and Gravitational Properties* | Gap analysis of §2 (Space/Time) and §3 (Geometry/EFE). The original source of the main "derivation." |
| [`notes/2102.09363_close_reading.md`](notes/2102.09363_close_reading.md) | G3 — *Hypergraph Discretization of the Cauchy Problem* | The circularity chain: Poisson-sprinkle the known target manifold, apply Benincasa–Dowker, "recover" the manifold. |
| [`notes/2303.07282_close_reading.md`](notes/2303.07282_close_reading.md) | G4 — *Non-Vacuum Solutions, Gravitational Collapse, Discrete Singularity Theorems* | Title promises discrete Raychaudhuri + singularity theorems; body delivers continuum collapse + mesh validation, no discrete theorem. |
| [`notes/claims_catalog.md`](notes/claims_catalog.md) | G1 | 184-row audit of every equation, align, definition, with per-row status verdict. |

## Topic notes

| Document | Topic |
|---|---|
| [`notes/null_tetrad_resolution.md`](notes/null_tetrad_resolution.md) | The null tetrad is built on the CCZ4 continuum metric, not on the hypergraph. See also [`singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) §5. |
| [`notes/limit_toolkit.md`](notes/limit_toolkit.md) | Inventory of convergence theorems in the mathematical literature (Ollivier, Gray, Benincasa–Dowker, Gromov–Hausdorff, Noldus-Suhr, spectral, graphon) and which are proved vs conjectural. |
| [`notes/empirical_refutation.md`](notes/empirical_refutation.md) | Empirical refutation of the "EFE-satisfying" rule using SetReplace; cone dimension ≈ 1 on all 9 seeds. |

## Results

Every `results/<phase>/*.md` is a verdict file with triple-or-more-rail verification for a single claim.

| Document | Verdict |
|---|---|
| [`results/phase1_selfaudit/README.md`](results/phase1_selfaudit/README.md) | **PASSED.** Python rewriter matches SetReplace on events fired, state size, causal |V|, |E| (7/9 exactly; 2/9 off by ≤ 4 edges in scheduler tiebreakers). |
| [`results/phase1_selfaudit/setreplace_reference.md`](results/phase1_selfaudit/setreplace_reference.md) | Raw SetReplace output that the Python rewriter is audited against. |
| [`results/phase2_continuum/eq342_verdict.md`](results/phase2_continuum/eq342_verdict.md) | **✗ REFUTED.** Tube volume coefficient. Four rails agree: correct value on $S^2$ is 1/6, Gorard says 1/3 (off by 2); on $S^3$ correct is 1/3, Gorard says 2 (off by 6). |
| [`results/phase2_continuum/eq344_verdict.md`](results/phase2_continuum/eq344_verdict.md) | **✗ REFUTED.** Ollivier Wasserstein. Direct contradiction of the Ollivier 2009 theorem that Gorard cites: directional $\mathrm{Ric}(v,v)$ vs scalar $R$. |

## Scripts (reproducibility)

All scripts are runnable and reproducible; each lists its intended invocation at the top.

| Script | Purpose |
|---|---|
| [`scripts/run_seeds_v3.wl`](scripts/run_seeds_v3.wl) | SetReplace evolution of the named rule on 7 seeds (cycles, paths, figure-8). |
| [`scripts/causal_dimension.wl`](scripts/causal_dimension.wl) | Cone-dimension log-log fit for evolved causal graphs. |
| [`scripts/grid3d_test.wl`](scripts/grid3d_test.wl) | Named rule on 3×3×3, 4×4×4, 5×5×5 grid seeds. |
| [`scripts/test_eq342.wl`](scripts/test_eq342.wl) | Eq 342 verification on $S^2$ and $S^3$: exact area, Taylor series, Gorard's formula side-by-side. |
| [`scripts/python/rewriter.py`](scripts/python/rewriter.py) | Independent Python re-implementation of Gorard's named rule (no SetReplace, no Wolfram Language). |
| [`scripts/python/run_all_seeds.py`](scripts/python/run_all_seeds.py) | Runs Python rewriter on all 9 seeds and compares to SetReplace reference. |
| [`scripts/python/test_eq344.py`](scripts/python/test_eq344.py) | Best-effort MC estimation of $W_1$ on $S^2$ (noise-limited; see `eq344_verdict.md` for why structural refutation is preferred). |

## Lean formalization

Every Lean file has a doc comment describing its role. Built on Mathlib via Lake.

| File | Purpose |
|---|---|
| [`lean/lakefile.toml`](lean/lakefile.toml) | Lake project file (Mathlib 4.29.1 dependency). |
| [`lean/InfraFormalization.lean`](lean/InfraFormalization.lean) | Top-level module importing the submodules. |
| [`lean/InfraFormalization/Hypergraph.lean`](lean/InfraFormalization/Hypergraph.lean) | Directed (multi-)hyperedges and hypergraphs. |
| [`lean/InfraFormalization/Rule.lean`](lean/InfraFormalization/Rule.lean) | Rewriting rules with `IsConservative` predicate (`\|LHS\| = \|RHS\|`). |
| [`lean/InfraFormalization/Application.lean`](lean/InfraFormalization/Application.lean) | Rule applications with embedded-LHS invariant. |
| [`lean/InfraFormalization/Conservation.lean`](lean/InfraFormalization/Conservation.lean) | **Theorem A (proved, draft):** conservative rules preserve state size. |
| [`lean/InfraFormalization/GraphMetric.lean`](lean/InfraFormalization/GraphMetric.lean) | Graph distance + `ScaledHypergraph` for continuum-limit framing. |
| [`lean/InfraFormalization/Growth.lean`](lean/InfraFormalization/Growth.lean) | Ball/cone counting + linear-cone theorem (stated, proof pending). |
| [`lean/InfraFormalization/Limit.lean`](lean/InfraFormalization/Limit.lean) | Scaffolding for GH / spectral / measure-space convergence. |
| [`lean/InfraFormalization/Multiway.lean`](lean/InfraFormalization/Multiway.lean) | Abstract rewriting systems, confluence, local confluence. |
| [`lean/InfraFormalization/Causal.lean`](lean/InfraFormalization/Causal.lean) | Trajectories and causal-precedence relation. |
| [`lean/InfraFormalization/Branchial.lean`](lean/InfraFormalization/Branchial.lean) | Placeholder interface for branchial structure. |

## Primary sources (read-only)

The papers themselves are under [`papers/`](papers/) — PDFs plus extracted TeX for each. Not part of our authorship; included for reproducibility of line references.

| Directory | Paper |
|---|---|
| `papers/gorard_2004.14810.pdf` + `papers/tex_2004/` | G1 — Some Relativistic and Gravitational Properties |
| `papers/gorard_2011.12174.pdf` + `papers/tex_2011/` | G2 — Algorithmic Causal Sets and the Wolfram Model |
| `papers/gorard_2102.09363.pdf` + `papers/tex_2102/` | G3 — Hypergraph Discretization of the Cauchy Problem |
| `papers/gorard_2303.07282.pdf` + `papers/tex_2303/` | G4 — Non-Vacuum Solutions, Gravitational Collapse, Discrete Singularity Theorems |

## Suggested reading paths

**"I want the 5-minute verdict."**
1. [`README.md`](README.md) status table.
2. [`FINDINGS.md`](FINDINGS.md) one-line summaries.
3. [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) S1–S6 gallery.

**"I want to check the math myself."**
1. [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) to pick which error you want to scrutinize.
2. The corresponding [`results/phase2_continuum/*.md`](results/phase2_continuum/) or [`results/phase1_selfaudit/*.md`](results/phase1_selfaudit/) verdict file.
3. The corresponding script under [`scripts/`](scripts/). Re-run.

**"I want to see if Gorard's original paper is as bad as claimed."**
1. [`notes/claims_catalog.md`](notes/claims_catalog.md) — per-equation verdict for all of 2004.14810.
2. [`notes/2004.14810_close_reading.md`](notes/2004.14810_close_reading.md) — prose discussion of §3.
3. [`notes/corpus_audit.md`](notes/corpus_audit.md) — cross-paper propagation.

**"I want to contribute a Lean proof."**
1. [`README.md`](README.md) layout section for Lean.
2. [`lean/InfraFormalization.lean`](lean/InfraFormalization.lean) and its submodules.
3. [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) §6 for the six items a honest formalization would require.

**"I want to understand the single-way vs multi-way issue."**
1. [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) top to bottom.
2. Appendix about the null tetrad in the same file.

**"I want to know which claims are established."**
1. [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) — "How the errors recur" section.
2. [`notes/claim_assessment.md`](notes/claim_assessment.md) — "The honest verdict" section.
