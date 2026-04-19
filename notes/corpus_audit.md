# Corpus audit: repeated errors across Gorard's Wolfram-physics papers

This document maps errors across the four principal Gorard papers on the Wolfram-model/GR program, so that the repetition of each error is visible.

## The corpus

| ID | Year | Title | arXiv | Pages |
|---|---|---|---|---|
| G1 | 2020 | Some Relativistic and Gravitational Properties of the Wolfram Model | 2004.14810 | ~50 |
| G2 | 2020 | Algorithmic Causal Sets and the Wolfram Model | 2011.12174 | ~100 |
| G3 | 2021 | Hypergraph Discretization of the Cauchy Problem in GR via Wolfram Model Evolution | 2102.09363 | ~131 |
| G4 | 2023 | Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems | 2303.07282 | ~109 |

## Error-propagation map

### Error 1 — "Ollivier–Ricci scalar κ(p,q) reduces to Ricci scalar R(p,q)"

The directional-vs-scalar Ricci conflation. Ollivier's JFA 2009 theorem gives **$\mathrm{Ric}(v,v)$** (directional along $v=(q-p)/|q-p|$), Gorard writes **scalar $R$**.

| Paper | Location | Quote |
|---|---|---|
| G1 | RelativityAndGravitation.tex line 604 (Eq 48) | $\delta(1 - \varepsilon^2/(2(n+2))\,R + O(\varepsilon^3+\varepsilon^2\delta))$ |
| G1 | line 637 (prose) | "Ollivier-Ricci scalar curvature $\kappa(p,q)$ reduces … to the standard Riemannian Ricci scalar curvature $R(p,q)$" |
| G2 | CausalSetPaper.tex line 1668 | $W(B_\varepsilon(p),B_\varepsilon(q))=\delta(1-\varepsilon^2/(2(d+2))\,R + O(\varepsilon^3+\varepsilon^2\delta))$ |
| G2 | line 1699 (prose) | "Ollivier-Ricci scalar $\kappa(p,q)$ reduces to the ordinary Riemannian Ricci scalar $R(p,q)$" |
| G2 | line 1882 | $\delta(1 - \varepsilon^2/(2(d+2))\,R + O(\varepsilon^3+\varepsilon^2\delta))$ (third instance in this paper) |
| G3 | NumericalRelativity.tex line 2626 (Eq 344) | $W(B_\varepsilon(p),B_\varepsilon(q))=\delta(1-\varepsilon^2/(2(d+2))\,R + O(\varepsilon^3+\varepsilon^2\delta))$ |
| G3 | line 2645 (prose) | "Ollivier-Ricci curvature scalar $\kappa(p,q)$ reduces to the usual Riemannian Ricci curvature scalar $R(p,q)$" |

Verdict **✗ refuted** — contradicts Ollivier 2009 Example 7. Full analysis: `results/phase2_continuum/eq344_verdict.md`.

**4 instances across 3 papers.** Same error copied verbatim.

### Error 2 — Tube-volume coefficient

$(d-1)/(d+1) \cdot (R - \mathrm{Ric}(u,u))$ vs the correct $(R + \mathrm{Ric}(u,u))/(6(d+1))$.

| Paper | Location | Coefficient |
|---|---|---|
| G1 | (tube formula absent) | N/A |
| G2 | CausalSetPaper.tex line 1165 (Eq 126) | $(d-1)/(d+1) \cdot (R - \mathrm{Ric}(u,u))$ ✗ |
| G3 | NumericalRelativity.tex line 2607 (Eq 342) | $(d-1)/(d+1) \cdot (R - \mathrm{Ric}(u,u))$ ✗ |
| G4 | (no tube formula in body; inherits from G3 by reference) | inherited |

Verdict **✗ refuted** — off by factor 2 on $S^2$, factor 6 on $S^3$. Full analysis: `results/phase2_continuum/eq342_verdict.md`.

**2 instances across 2 papers; inherited in a third.**

### Error 3 — Main §3.3 "derivation" of Einstein field equations

Ill-defined discrete action $\sum d\mu_g R$, ill-defined $\delta/\delta g^{ab}$ on a discrete state, unproven "weak ergodicity ⇒ sum becomes integral" convergence, tautological "asymptotic dimension preservation" definition.

| Paper | Location | Status |
|---|---|---|
| G1 | §3.3 (lines 882–990, Eqs 86–102) | original instance |
| G2 | §5 (lines 1910–1980) | same argument, expanded |
| G3 | §5 (lines 5240–6200) | further expanded with Benincasa–Dowker (which Poisson-samples the target manifold — structurally circular) |
| G4 | §4 | builds on G3's construction |

Verdict **⚠ ill-defined / ○ open**. The overall conclusion (Einstein field equations emerge) inherits all the failures of its component steps. No single step has been repaired by any successor paper; each new paper reuses the broken argument.

### Error 4 — "Asymptotic dimensionality preservation" is tautological

Gorard defines this condition by Eq 87 (G1), which is "$\delta S/\delta g^{ab} \to 0$" — the very equation needed to derive Einstein's equations by calculus of variations. This is not a verifiable physical/combinatorial condition; it's a pre-written conclusion.

Appears in G1 (line 890), G2 (§5), G3 (§5). **All three papers.**

### Error 5 — Fiat orthonormality on hypergraphs

"We also assume that all pairs of hyperedges which are not parallel (i.e. incident to the same set of vertices) can be considered to be orthonormal" — declaring orthonormality without constructing an inner product.

Appears in G1 (line 840), G2 (§5), G3 (§5). **All three papers.**

### Error 6 — $\varepsilon = \delta = 1$ in asymptotic expansions

Using Riemannian expansions valid as $\varepsilon \to 0$ at the discrete edge length $\varepsilon = 1$ — breaks the very expansion it claims to apply.

Appears in G1 (line 840), G2 (§5), G3 (§5). **All three papers.**

### Error 7 — The specific rule claimed to "provably satisfy EFE in the continuum limit"

$\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \to \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$. $|LHS|=|RHS|=4$, so edge count is conserved; empirically produces 1D causal graphs on every seed tested (see `results/phase1_selfaudit`). Cannot possibly satisfy Einstein's equations as a continuum limit.

- Appears in G3 (line 6202).
- Referenced / assumed valid in G4.

Verdict **✗ refuted** by independent Python rewriter + SetReplace + structural $|LHS|=|RHS|$ argument.

## Summary table: per-paper refutation status

| Paper | Novel content | Repeats errors from | Body delivers title-claim? |
|---|---|---|---|
| G1 (2004.14810) | §3.3 discrete EFE "derivation"; Ollivier discrete Ricci on hypergraphs; ADM reframing | originator of Errors 1, 3, 4, 5, 6 | ✗ — "derivation" rests on undefined discrete objects and unproven limits |
| G2 (2011.12174) | tube formula; d'Alembertian for causal graphs; links to causal-set theory | repeats 1 (3 copies!), 3, 4, 5, 6; originator of 2 | partially — causal-set link is valid on its own terms but inherits G1's undefined discrete EFE apparatus |
| G3 (2102.09363) | CCZ4-on-hypergraph-mesh code; gravitational-wave extraction via Newman–Penrose; specific named rule | repeats 1, 2, 3, 4, 5, 6; originator of 7 | ✗ — "provably satisfies EFE" reduces to Poisson-sampling-the-target-manifold (circular); named rule produces 1D causal graph |
| G4 (2303.07282) | continuum WKB/LTB/Ernst collapse analysis + numerical validation | inherits 1–7; also non-delivers on title | ✗ — title promises "discrete singularity theorems", body has none |

## The overall picture

The corpus advertises a program that *derives* general relativity from hypergraph rewriting. Across four papers and ~400 pages:

- **Standard continuum material (~70–80% of equations in G1; ~85% in G2–G3)** is correctly quoted from textbooks.
- **Discrete-side definitions** are mostly coherent when translating known constructions (Ollivier-Ricci for directed hypergraphs follows Eidi-Jost 2019; discrete d'Alembertian follows Benincasa-Dowker 2010).
- **Discrete–continuum bridge claims** are systematically un-supported:
  - Ollivier identity stated with wrong Ricci (scalar vs directional) — **4 × across 3 papers**.
  - Tube formula stated with wrong coefficient — **2 × across 2 papers**.
  - The §3.3 Einstein-equations "derivation" uses ill-defined objects and unproven convergences — **originating in G1, reused without repair in G2, G3, G4**.
- **The one specific rule advertised as "provably" satisfying the Einstein field equations is structurally incapable of doing so**, with the refutation confirmed by two independent implementations (SetReplace and our Python rewriter).
- **Several title-promised results are not delivered in-body** (most conspicuously the "discrete singularity theorems" of G4, acknowledged as future work in the paper's own conclusions).

None of this constitutes data fabrication, but the cumulative pattern is **systematic overclaim across a 4-paper corpus**:
1. Physics-style "derivations" written with the grammar of mathematical proof;
2. Errors copied verbatim across papers without repair, even after the errors are re-stated in a third paper — suggesting none of the papers was independently checked against the cited Ollivier / Gray / Benincasa–Dowker literature;
3. A central promised theorem (discrete Einstein equations) that rests on objects that have never been constructed;
4. A central example rule that cannot possibly satisfy the claimed property.

Taken as a corpus, the work is best described as a physics research program (ideas, analogies, numerical experiments) published with the rhetorical register of mathematical derivation. Any downstream work citing these papers as having **established** the derivation of GR from Wolfram-model rewriting is citing something that has not been established.
