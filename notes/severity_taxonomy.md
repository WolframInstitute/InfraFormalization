# Severity taxonomy of errors in the Gorard corpus

A graded classification of the errors found across Gorard's Wolfram-physics papers (arXiv:2004.14810 / 2011.12174 / 2102.09363 / 2303.07282). Severity is ordered from highest to lowest.

## Terminology

We distinguish four terms carefully:

- **False statement**: a mathematical claim that contradicts a known, cited, published theorem. The author is *wrong* as a matter of fact.
- **Ill-defined statement**: a claim that refers to objects or operations that have not been constructed or defined. It is *neither true nor false* — it is *not a mathematical statement* in its own right.
- **Tautology**: a claim that is formally true because it restates a definition, but is presented with the rhetoric of a derived theorem.
- **Unsupported bridge claim**: a claim about a limit, convergence, or correspondence between a discrete and continuum object that is asserted without proof and not proved in the cited literature.

A **false statement** below is a statement that is mathematically false. Where it also contradicts a source that the author cites, the entry says so. The classification concerns the statements, not the intent of the author.

## Severity scale

### S1 — FALSE STATEMENTS contradicting cited sources

Highest severity. The claim is mathematically wrong, is visibly wrong to anyone who reads the cited source carefully, and is repeated verbatim across multiple papers without repair.

| # | Error | Papers | Severity marker | Evidence |
|---|---|---|---|---|
| 1 | **Ollivier's theorem stated with scalar $R$ instead of directional $\mathrm{Ric}(v,v)$.** Gorard cites Ollivier's JFA 2009 paper (ref [ollivier]/[ollivier2]/[ollivier3]) throughout and states a formula that contradicts the cited theorem by a factor of 2 on $S^2$. | G1 (line 604), G2 (lines 1668, 1699, 1882), G3 (Eq 344, line 2645) | **4 instances, 3 papers, verbatim** | `results/phase2_continuum/eq344_verdict.md` |
| 2 | **Tube-volume expansion with the wrong coefficient.** Coefficient $(d-1)/(d+1)$ given; correct value is $1/(2(d+1))$ with a different algebraic form inside. Off by factor 2 on $S^2$, factor 6 on $S^3$ — verified by four-rail (analytic, symbolic, numerical, manual) audit. | G2 (Eq 126), G3 (Eq 342) | 2 instances, 2 papers | `results/phase2_continuum/eq342_verdict.md` |

Why these are S1: Both are computational equalities that can be checked against standard Riemannian geometry in ten minutes by any trained reader. Both appear in papers published in peer-reviewed venues (Complex Systems) or as frequently-cited arXiv preprints. Both are repeated in later papers without anyone (author, coauthors, reviewers) catching them.

### S2 — ILL-DEFINED load-bearing claims

The central "derivations" rest on objects that are written down but never constructed. These aren't false — they can't even be evaluated for truth — but they are presented as if evaluable.

| # | Error | Where | Why this is S2 |
|---|---|---|---|
| 3 | **Discrete Einstein–Hilbert action $S[g^{ab}] = \sum d\mu_g R$** with $g^{ab}$ and $d\mu_g$ never defined on a discrete state. | G1 Eq 86, G2 §5, G3 §5 | Nowhere in the corpus is a "discrete metric tensor $g_{ab}$ on a causal graph" constructed with explicit components; nowhere is the "discrete volume form $d\mu_g$" defined as anything computable. |
| 4 | **Functional derivative $\delta S / \delta g^{ab}$ applied to a discrete sum.** Continuum variational calculus is invoked on a discrete object. | G1 Eq 87, G2 §5, G3 §5 | $\delta/\delta g^{ab}$ is defined for functionals of smooth metric fields. On a discrete state it has no meaning unless a discrete analog is specified — it is not. |
| 5 | **Fiat orthonormality:** "all pairs of hyperedges which are not parallel can be considered to be orthonormal." | G1 line 840, G2 §5, G3 §5 | Declares orthonormality without an inner product. To be orthonormal with respect to *what* bilinear form? None is constructed. |
| 6 | **Asymptotic expansions at $\varepsilon = \delta = 1$.** Riemannian ball-volume expansions valid as $\varepsilon \to 0$ are used at unit edge length. | G1 line 840, G2 §5, G3 §5 | Category error: an asymptotic expansion is not a formula that can be evaluated at finite values of its small parameter without quantitative error bounds, which are not provided. |

Why these are S2 (severity below S1 but still structural): Without these five items, §3.3 has no content. They are the hinges of the Einstein-equations derivation. None is false, because none is *evaluable*. A careful referee would return the paper with "define these objects first."

### S3 — TAUTOLOGIES presented as derivations

Claims whose "proof" consists of restating the definition as the theorem.

| # | Error | Where | Nature of the tautology |
|---|---|---|---|
| 7 | **"Causal invariance implies discrete general covariance."** | G1 §2.3 (around line 466) | Both are *defined* as update-order independence of the causal structure. The biconditional is literally the two sides of a definition. |
| 8 | **"Causal invariance implies discrete Lorentz covariance."** | G1 §2.3 (line 466ff) | The constancy of the speed of light is built into the model axiomatically via the definition of edge length in the causal graph, then "recovered" as a consequence. |
| 9 | **"Asymptotic dimensionality preservation ⇒ Einstein equations."** | G1 §3.3 | The condition is *defined* as $\delta S/\delta g^{ab} \to 0$ (Eq 87), which is the Euler-Lagrange equation of the action. Defining the premise *as* the conclusion of the variational argument. |

Why S3: These are not false (they are trivially true). But the paper presents them as substantive physical/mathematical derivations when they are relabelings. A reader who thinks a theorem has been proved has been misled by the *framing*, not by the *math*.

### S4 — UNSUPPORTED BRIDGE CLAIMS

Claims about discrete-to-continuum convergence asserted as facts, with either no proof or an appeal to the open Sorkin–Benincasa–Dowker conjecture.

| # | Error | Where | Proof status |
|---|---|---|---|
| 10 | **"The discrete sum $\sum d\mu_g R$ becomes the integral $\int d^4x \sqrt{-g} R$ in the continuum limit."** | G1 Eq 88, G2 §5, G3 §5 | Asserted "subject to a weak ergodicity assumption on the dynamics of the causal graph." Neither "becomes" (what topology?) nor "weak ergodicity" (what precise definition?) is specified. The cited supporting result is the Sorkin–Benincasa–Dowker conjecture, which is open in the causal-set literature. |
| 11 | **"Named rule $\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \to \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$ provably satisfies the Einstein field equations in the continuum limit."** | G3 abstract + line 6202 | "Provably" is traced to the Sorkin–Benincasa–Dowker construction under an assumed Poisson sampling of the known target manifold. No Wolfram-model dynamics enters the proof. And the named rule is empirically 1-dimensional (see S5 #13). |
| 12 | **"Ollivier–Ricci scalar on directed hypergraphs converges to Riemannian Ricci in the continuum limit."** | G1 §3.1 end, G2 §3, G3 §5 | Asserted without a convergence theorem. In the literature (Lin–Lu–Yau, Trillos–Slepčev) such theorems exist only for specific random-geometric-graph constructions under hypotheses that Wolfram-model rewriting does not obviously satisfy. |

Why S4: These are unproven conjectures that Gorard's papers treat as settled facts. The asymmetry between "stated" and "proved" is the defect.

### S5 — REFUTED SPECIFIC CLAIMS

Claims that are concretely false on inspection or by direct computation — not just contradicting the literature but contradicting what the paper's own setup implies.

| # | Error | Where | Refutation |
|---|---|---|---|
| 13 | **Named rule "provably satisfying EFE" produces a 1-dimensional causal graph on every tested seed**, including 3D-grid seeds. $\|LHS\|=\|RHS\|=4$ forces edge-count conservation ⇒ cone growth is at most linear ⇒ causal dimension ≤ 1. Gorard's own §3.3 argument needs $n = 4$ for 3+1-dim GR. | G3 line 6202 | Verified by SetReplace on 9 seeds *and* by independent Python rewriter (`results/phase1_selfaudit/`). |
| 14 | **Eq 65, the discrete $N(r)$ ball-expansion**, carries the factor $R/(6(n+2))$ "by analogy" with the Riemannian formula. The analogy is not a derivation. Downstream it is used to "compute" hypergraph Ricci scalars. | G1 Eq 65, G2 §5 | The claim is not that a specific formula is wrong but that the "derivation" is by verbal analogy rather than by convergence theorem. Combined with S1 #1 and S2 #5–6, the computed "curvatures" from hypergraphs are calibrated against a formula that is itself either unjustified or wrong. |

### S6 — TITLE AND ABSTRACT CLAIMS NOT DELIVERED IN THE BODY

| # | Error | Where |
|---|---|---|
| 15 | **"Discrete Singularity Theorems in Wolfram Model Systems"** (paper title). Body contains zero discrete singularity theorems; zero occurrences of "shear" or "vorticity"; no discrete Raychaudhuri equation, no discrete energy condition, no discrete stress-energy tensor, no discrete trapped surface. The paper's own conclusion acknowledges these as open problems. | G4 (2303.07282) |
| 16 | **"Provably satisfies the Einstein field equations in the continuum limit"** — the word *provably* applied to a claim whose only published support is a conjecture about Poisson-sampled causal sets, and which is refuted for the one specific rule named. | G3 (2102.09363) abstract, §5 |

## Summary: severity distribution across the corpus

- **S1 (False statements)**: 6 verbatim instances across 3 papers, 2 distinct errors (Ollivier R/Ric, tube coefficient). These are the clearest errors in the corpus.
- **S2 (Ill-defined)**: 4 distinct errors, each recurring across G1/G2/G3. Kill the main §3.3 argument unless rescued.
- **S3 (Tautologies)**: 3 instances. Inflate the perceived content of §2.3–§3.3.
- **S4 (Unsupported bridge claims)**: 3 major ones. The load-bearing bridges that the *main theorem* rests on.
- **S5 (Refuted specifics)**: 2 instances. Strongest in the empirical direction — the named rule cannot produce GR.
- **S6 (Claims not delivered in the body)**: 2 instances — the "provably" and "discrete singularity theorems" claims.

**Total distinct errors catalogued: 16.** Repetition count (same error reused unchanged in a later paper): Errors 1, 2, 3, 4, 5, 6, 10, 11 all reappear across papers.

## How the errors recur

The record shows how the errors recur:
- **Repetition.** The same error appears verbatim in three papers over four years, so the statement was not re-checked between them.
- **Misstated cited sources.** Ollivier's 2009 theorem is cited but misstated, and the cited source shows the discrepancy.
- **Verbatim copy-paste.** Whole paragraphs of G2 §5 and G3 §5 are near-verbatim restatements of G1 §3.3. This explains how an error could copy-propagate without re-examination.

Our project's charter is to use precise language. We therefore stop at:
- **S1 errors are mathematically false, verified by independent computation, and the author had access to sources that refute them.** These are *false statements*.
- **S2 items are not truth-apt statements. They are failures of rigour.**
- **S3 items are formally true. They are failures of presentation.**
- **S4 items are assertions stated without proof, which the author may well believe. They are unsupported assertions.**
- **S6 items are promises in titles and abstracts that the body does not deliver, a common failing in physics papers.**

The corpus as a whole is best described as **systematic overclaim with embedded mathematical errors** — with no fabricated data, but a pattern of insufficient rigour that makes the advertised program (derive GR from Wolfram-model rewriting) an unsettled question rather than the accomplished fact the papers' abstracts claim it to be.

## Where to look

Every S1–S6 item above is linked to a detailed write-up in this repo:

- S1 #1: `results/phase2_continuum/eq344_verdict.md`
- S1 #2: `results/phase2_continuum/eq342_verdict.md`
- S2–S4: `notes/2004.14810_close_reading.md`, §3 analysis
- S5 #13: `results/phase1_selfaudit/README.md`, `notes/empirical_refutation.md`
- S6 #15: `notes/2303.07282_close_reading.md`
- Cross-paper: `notes/corpus_audit.md`
- Full catalog of equations: `notes/claims_catalog.md`
