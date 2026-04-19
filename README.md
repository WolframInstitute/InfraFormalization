# infra_formalization — a critical audit of the Gorard "GR-from-rewriting" papers

An independent audit of the four principal Gorard papers on the Wolfram-model program for deriving general relativity from hypergraph rewriting:

- **G1 — arXiv:2004.14810** — *Some Relativistic and Gravitational Properties of the Wolfram Model*
- **G2 — arXiv:2011.12174** — *Algorithmic Causal Sets and the Wolfram Model*
- **G3 — arXiv:2102.09363** — *Hypergraph Discretization of the Cauchy Problem in General Relativity via Wolfram Model Evolution*
- **G4 — arXiv:2303.07282** — *Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems*

The stated program: derive GR from hypergraph rewriting. The stated claim in G3: a specific named rewriting rule "provably satisfies the Einstein field equations in the continuum limit." This repo verifies, line by line and claim by claim, what is actually true.

## Navigation

| | Document |
|---|---|
| ⭐ Start here | [`FINDINGS.md`](FINDINGS.md) — canonical one-line summary of every claim audited |
| 📑 Index | [`INDEX.md`](INDEX.md) — full document tree, one line per file |
| 📘 Glossary | [`GLOSSARY.md`](GLOSSARY.md) — every technical term used |
| 📋 Next steps | [`NEXT_STEPS.md`](NEXT_STEPS.md) — what's done, in flight, waiting |
| 🔭 Research program | [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) — the long-term infrageometry program (audit → correction → positive construction) |
| 🗺 Methodology | [`notes/plan.md`](notes/plan.md) — 7-phase verification plan |
| 🧮 Severity | [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) — S1–S6 taxonomy; "is it a lie?" discussion |
| 🧩 Corpus | [`notes/corpus_audit.md`](notes/corpus_audit.md) — cross-paper map of repeated errors |
| 🧭 Framework | [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) — single-way vs multi-way + null-tetrad explainer |
| 🧠 Synthesis | [`notes/claim_assessment.md`](notes/claim_assessment.md) — "overclaim or hunch?" verdict |

### Reading paths

- **5-minute verdict**: [`FINDINGS.md`](FINDINGS.md) → this README status table → [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md).
- **Check the math**: [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) → [`results/phase2_continuum/*.md`](results/phase2_continuum/) → re-run the script in [`scripts/`](scripts/).
- **See if G1 is as bad as claimed**: [`notes/claims_catalog.md`](notes/claims_catalog.md) → [`notes/2004.14810_close_reading.md`](notes/2004.14810_close_reading.md) → [`notes/corpus_audit.md`](notes/corpus_audit.md).
- **Contribute Lean**: [`lean/InfraFormalization.lean`](lean/InfraFormalization.lean) → [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) §6 (the "six items").
- **Which claims are established?**: [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) §"How the errors recur" → [`notes/claim_assessment.md`](notes/claim_assessment.md).

## Status table

| # | Claim | Paper | Status | Verdict file |
|---|---|---|---|---|
| S1 #1 | Ollivier Wasserstein uses directional $\mathrm{Ric}(v,v)$, Gorard writes scalar $R$ | G1 line 604; G2 lines 1668/1699/1882; G3 Eq 344 | **✗ REFUTED** | [eq344_verdict.md](results/phase2_continuum/eq344_verdict.md) |
| S1 #2 | Tube-volume coefficient is $(R{+}\mathrm{Ric}(u,u))/(6(d{+}1))$, Gorard writes $(d{-}1)(R{-}\mathrm{Ric})/(d{+}1)$ | G2 Eq 126; G3 Eq 342 | **✗ REFUTED** (factor 2 on $S^2$, factor 6 on $S^3$) | [eq342_verdict.md](results/phase2_continuum/eq342_verdict.md) |
| S2 #3 | "Discrete action" $S = \sum d\mu_g R$ with $g, d\mu_g$ never constructed on a discrete state | G1 Eq 86; G2 §5; G3 §5 | ⚠ ILL-DEFINED | [claims_catalog.md](notes/claims_catalog.md) |
| S2 #4 | "$\delta / \delta g^{ab}$" applied to a discrete sum | G1 Eq 87; G2 §5; G3 §5 | ⚠ ILL-DEFINED | [claims_catalog.md](notes/claims_catalog.md) |
| S2 #5 | "Non-parallel hyperedges are orthonormal" (declaration without inner product) | G1 line 840; G2 §5; G3 §5 | ⚠ ILL-DEFINED | [2004.14810_close_reading.md](notes/2004.14810_close_reading.md) |
| S2 #6 | $\varepsilon = \delta = 1$ applied to asymptotic expansion valid as $\varepsilon \to 0$ | G1 line 840; G2 §5; G3 §5 | ⚠ ILL-DEFINED | [2004.14810_close_reading.md](notes/2004.14810_close_reading.md) |
| S3 #7 | "Causal invariance ⇔ general covariance" | G1 §2.3 | ⊘ TAUTOLOGY | [2004.14810_close_reading.md](notes/2004.14810_close_reading.md) |
| S3 #8 | "Causal invariance ⇒ Lorentz covariance" (with $c$ axiomatised in) | G1 §2.3 | ⊘ TAUTOLOGY | [2004.14810_close_reading.md](notes/2004.14810_close_reading.md) |
| S3 #9 | "Asymptotic dim preservation ⇒ Einstein equations" (premise = conclusion of variation) | G1 §3.3 | ⊘ TAUTOLOGY | [severity_taxonomy.md](notes/severity_taxonomy.md) |
| S4 #10 | Discrete sum → continuum EH action | G1 Eq 88; G2 §5; G3 §5 | ○ OPEN (Sorkin–BD conjecture) | [limit_toolkit.md](notes/limit_toolkit.md) |
| S4 #11 | "Provably satisfies EFE in continuum limit" | G3 abstract, line 6202 | **✗ REFUTED** (circular: Poisson-samples known target) | [2102.09363_close_reading.md](notes/2102.09363_close_reading.md) |
| S4 #12 | Hypergraph Ollivier–Ricci → continuum Ricci in the limit | G1 §3.1; G2 §3; G3 §5 | ○ OPEN | [limit_toolkit.md](notes/limit_toolkit.md) |
| S5 #13 | Named rule `{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` gives 3+1-dim causal graph | G3 line 6202 | **✗ REFUTED** (1D on 9 seeds; structural $\|LHS\|=\|RHS\|$ argument) | [empirical_refutation.md](notes/empirical_refutation.md), [phase1_selfaudit](results/phase1_selfaudit/) |
| S5 #14 | Discrete $N(r)$ expansion by analogy with Riemannian | G1 Eq 65 | ✗ NOT DERIVED | [2004.14810_close_reading.md](notes/2004.14810_close_reading.md) |
| S6 #15 | Title "Discrete Singularity Theorems" promises discrete theorems | G4 | ✗ NOT DELIVERED | [2303.07282_close_reading.md](notes/2303.07282_close_reading.md) |
| S6 #16 | "Provably" applied to an unproven conjecture | G3 abstract | ✗ OVERCLAIM | [2102.09363_close_reading.md](notes/2102.09363_close_reading.md) |

### Positive findings

| # | Finding | Status |
|---|---|---|
| P1 | $|LHS| = |RHS|$ rule ⇒ state size preserved under any application. | **✅ Machine-verified in Lean 4 + Mathlib 4.29.1**: `Application.size_result_of_conservative` in [`lean/InfraFormalization/Conservation.lean`](lean/InfraFormalization/Conservation.lean). Plus corollary `size_preserved_by_applications` (trajectory-level). |
| P2 | $|LHS| = |RHS|$ rule ⇒ causal graph has linear cone growth (dim ≤ 1). | Empirical + proof stub: [`lean/InfraFormalization/Growth.lean`](lean/InfraFormalization/Growth.lean) |
| P3 | Gorard's §3.3 argument cannot apply to any conservative rule. | Consequence of P2. Lean proof pending. |

See [`FINDINGS.md`](FINDINGS.md) for the full canonical list.

## Repository layout

```
infra_formalization/
├── README.md                          — this file
├── INDEX.md                           — complete document index
├── GLOSSARY.md                        — technical terms
├── FINDINGS.md                        — canonical one-line summary
├── NEXT_STEPS.md                      — what's done, in flight, waiting
├── notes/                             — close-readings, analyses, synthesis
│   ├── plan.md
│   ├── severity_taxonomy.md
│   ├── corpus_audit.md
│   ├── claims_catalog.md              — 184-row G1 equation audit
│   ├── singleway_vs_multiway.md
│   ├── claim_assessment.md
│   ├── 2004.14810_close_reading.md
│   ├── 2102.09363_close_reading.md
│   ├── 2303.07282_close_reading.md
│   ├── null_tetrad_resolution.md
│   ├── limit_toolkit.md
│   └── empirical_refutation.md
├── results/
│   ├── phase1_selfaudit/              — Python rewriter ↔ SetReplace agreement
│   └── phase2_continuum/              — eq342, eq344 verdicts
├── scripts/                           — reproducible .wl and Python scripts
│   └── python/
├── lean/                              — formal skeleton, Mathlib-based
│   └── InfraFormalization/
│       ├── Hypergraph.lean
│       ├── Rule.lean
│       ├── Application.lean
│       ├── Conservation.lean          — Theorem A (proved, draft)
│       ├── GraphMetric.lean
│       ├── Growth.lean                — Theorem B stub
│       ├── Limit.lean                 — continuum-limit scaffolding
│       ├── Multiway.lean
│       ├── Causal.lean
│       └── Branchial.lean
└── papers/                            — source PDFs + extracted TeX (read-only)
    ├── tex_2004/   (G1)
    ├── tex_2011/   (G2)
    ├── tex_2102/   (G3)
    └── tex_2303/   (G4)
```

See [`INDEX.md`](INDEX.md) for per-file descriptions.

## Reproducing

### Prerequisites

- **Wolfram Language** via `wolframscript` (uses Windows-side install via WSL: `/mnt/c/Program Files/Wolfram Research/WolframScript/wolframscript.exe`), with the SetReplace paclet 0.3+ installed.
- **Python 3.10+** (stdlib only; `numpy + scipy` used for Eq 344 script).
- **Lean 4** via `elan`, for Mathlib builds.

### Running a verification script

```bash
# 1) Empirical refutation of the named rule (SetReplace)
wolframscript -file scripts/run_seeds_v3.wl
wolframscript -file scripts/causal_dimension.wl
wolframscript -file scripts/grid3d_test.wl

# 2) Independent Python re-implementation (no SetReplace)
cd scripts/python && python3 run_all_seeds.py

# 3) Eq 342 audit on S^2, S^3 (symbolic + numeric)
wolframscript -file scripts/test_eq342.wl

# 4) Lean (one-time Mathlib build, ~1 hour first run)
cd lean && lake update && lake build
```

Every verdict is reproducible to the precision quoted.

## Project posture

Every claim we make about Gorard is checked on four independent rails before being accepted. Correct claims get verified and formalised in Lean; incorrect claims are documented precisely, with counterexamples and correct-statement side-by-side. "Overclaim," "hunch," and "overclaim" are distinct verdicts — we use them precisely.

The goal is not to discredit but to have a load-bearing, verifiable answer to: **what, in this corpus, is actually true, and how is it linked (if at all) to general relativity?** The question matters because papers in this corpus are being cited as if they had *established* the derivation — they have not.

See [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) §"How the errors recur" for the most delicate classification.
