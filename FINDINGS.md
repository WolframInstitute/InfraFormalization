# Findings — canonical one-line summary of every claim audited

Grouped by severity (S1 most severe, S6 least). See [`INDEX.md`](INDEX.md) for document navigation, and [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) for the full taxonomy.

Each row: verdict, short form of claim, citations in the corpus, link to the verdict file.

Status key: ✗ refuted | ⚠ ill-defined | ⊘ tautology | ○ open conjecture | ✓ verified correct

---

## S1 — False statements contradicting cited sources

| # | Verdict | Claim | Where | Verdict file |
|---|---|---|---|---|
| 1 | ✗ | Wasserstein distance between $\varepsilon$-balls on parallel-transport uses scalar $R$ — but Ollivier's cited JFA 2009 theorem has directional $\mathrm{Ric}(v,v)$. | G1 eq at line 604; G2 lines 1668/1699/1882; G3 Eq 344 / line 2645 | [eq344_verdict.md](results/phase2_continuum/eq344_verdict.md) |
| 2 | ✗ | Tube-volume coefficient $(d-1)/(d+1) \cdot (R - \mathrm{Ric}(u,u))$ — correct is $(R + \mathrm{Ric}(u,u))/(6(d+1))$. Off by factor 2 on $S^2$, factor 6 on $S^3$. | G2 Eq 126; G3 Eq 342 | [eq342_verdict.md](results/phase2_continuum/eq342_verdict.md) |

## S2 — Ill-defined load-bearing objects / operations

| # | Verdict | Claim | Where |
|---|---|---|---|
| 3 | ⚠ | "Discrete Einstein–Hilbert action" $S[g^{ab}] = \sum d\mu_g R$ written down; $g^{ab}$ and $d\mu_g$ never constructed on a discrete state. | G1 Eq 86; G2 §5; G3 §5 |
| 4 | ⚠ | "Functional derivative" $\delta S / \delta g^{ab}$ applied to a discrete sum — continuum variational calculus on an undefined discrete metric. | G1 Eq 87; G2 §5; G3 §5 |
| 5 | ⚠ | "All non-parallel hyperedges are orthonormal" — declaring orthonormality without a bilinear form. | G1 line 840; G2 §5; G3 §5 |
| 6 | ⚠ | Asymptotic expansion valid as $\varepsilon \to 0$ used at unit edge length $\varepsilon = \delta = 1$. | G1 line 840; G2 §5; G3 §5 |

Each is a keystone of the §3.3 Einstein-equations "derivation" and none is rescued by any later paper.

## S3 — Tautologies presented as derivations

| # | Verdict | Claim | Why tautological |
|---|---|---|---|
| 7 | ⊘ | "Causal invariance ⇒ discrete general covariance" | Both defined as update-order independence of the causal structure. Definitions identical. |
| 8 | ⊘ | "Causal invariance ⇒ discrete Lorentz covariance" | Constancy of $c$ axiomatised via edge lengths, then "recovered." |
| 9 | ⊘ | "Asymptotic dimensionality preservation ⇒ Einstein equations" | The preservation condition is *defined* as $\delta S/\delta g^{ab} \to 0$, which is the Euler-Lagrange equation of the action. |

## S4 — Unsupported bridge claims (discrete ↔ continuum)

| # | Verdict | Claim | Status in the literature |
|---|---|---|---|
| 10 | ○ | "$\sum d\mu_g R$ becomes $\int d^4x \sqrt{-g} R$ in the continuum limit." | Unproven even for causal-set theory (Sorkin–Benincasa–Dowker conjecture, partial numerical support from Cunningham 2018). |
| 11 | ○ | "Named rule provably satisfies EFE in continuum limit." | No proof for the rule is given in G3. G3 replaces weak ergodicity by an assumption of Poisson-distributed rewrite events (line 6080) and samples the initial hypergraph from the target geometry (lines 6148-6152, 6179). The repository does not prove the claim false. See [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md), Claim 1. |
| 12 | ○ | "Ollivier–Ricci scalar on directed hypergraphs converges to Ricci in continuum limit." | Asserted. Convergence theorems exist only for specific random-geometric-graph constructions (Trillos–Slepčev 2018), not for Wolfram-model-rewriting evolutions. |

## S5 — Refuted specific claims

| # | Verdict | Claim | Evidence |
|---|---|---|---|
| 13 | MEASURED | The rule $\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \to \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$ produces a 3+1-dim causal graph. | Measured cone-growth exponents lie between 0.985 and 1.256 on cycles, paths and 3D grids up to 300 edges and 2000 events. SetReplace and the Python rewriter disagree on the exponent for 8 of 9 seeds (4x4x4 grid: 0.985 against 1.256), cause not determined. Edge-count conservation is PROVED. A bound on cone growth is OPEN. |
| 14 | ✗ | Discrete $N(r) = ar^n(1 - Rr^2/(6(n+2)) + O(r^4))$ on hypergraphs. | Obtained "by analogy," not derived. In combination with the Ollivier and tube-formula mis-statements above, the "curvatures" computed from hypergraphs are calibrated against a formula that is itself unjustified or wrong. |

## S6 — Claims in titles and abstracts not delivered in the body

| # | Verdict | Claim | Evidence |
|---|---|---|---|
| 15 | ✗ (title-body gap) | Title: "Non-Vacuum Solutions, Gravitational Collapse and **Discrete Singularity Theorems** in Wolfram Model Systems." | Body has no discrete Raychaudhuri, no discrete expansion scalar, no discrete energy condition, no discrete stress-energy tensor; zero occurrences of "shear" or "vorticity." Conclusion acknowledges these as future work. |
| 16 | ✗ (wording overclaim) | "A hypergraph substitution rule that **provably** satisfies the Einstein field equations in the continuum limit." | "Provably" is applied to a chain that assumes Poisson-distributed rewrite events (G3 line 6080) and the zero-surface-term and vanishing-tail assumptions of the Benincasa–Dowker action limit (lines 6110-6120). G3 gives no proof for the named rule. |

## Verified correct (✓)

The standard continuum material quoted in JGORARD's papers is correct. Specifically:

- All Riemannian ball-volume expansion formulas (Eq 47 / 343 of G3): match Gray 1973.
- All metric/Christoffel/Riemann/Ricci definitions: match standard GR textbooks (MTW, Hawking–Ellis, Wald).
- Einstein–Hilbert action variation (continuum, G1 Eqs 89–91): standard Hilbert 1915.
- Abstract rewriting systems / Church–Rosser / confluence definitions: standard (Baader–Nipkow).
- Ollivier–Ricci on metric-measure spaces (the definitional framework, distinct from the claimed identity with scalar $R$): standard (Ollivier 2009).
- ADM decomposition, FLRW metric, geodesic equation, Lovelock higher-derivative gravity, Chapman–Enskog expansion, Benincasa–Dowker d'Alembertian: all standard, correctly cited.

These are Lean-formalisation targets (see [`lean/InfraFormalization/`](lean/InfraFormalization/)).

## Positive Wolfram-model findings we have confirmed

| # | Finding | Status |
|---|---|---|
| P1 | `\|LHS\| = \|RHS\|` rule ⇒ state size is conserved along any evolution. | PROVED. `Application.size_result_of_conservative` (`Conservation.lean:27`), `size_preserved_by_applications` (`Conservation.lean:48`), and for the named rule `Refutations.gorardNamedRule_applications_preserve_size` (`Refutations/F7NamedRuleStructure.lean:41`). Axioms: `propext`, `Classical.choice`, `Quot.sound`. |
| P2a | `\|LHS\| = \|RHS\|` = k rule with N edges ⇒ every antichain of the causal graph of a single-way evolution has at most ⌊N/k⌋ events. | OPEN. The library has no causal graph with hyperedge identities (`Causal.lean:35-44`), so the statement cannot yet be written in Lean. |
| P2b | The named rule's causal graph has cone growth C(t) ≤ c(N)·(t+1). | OPEN. MEASURED exponents 0.985 to 1.256 on 9 seeds, with the two tools disagreeing (row 13). P2a does not imply P2b: P2a bounds events by longest-path distance and the cone counts shortest-path distance. |
| P3 | JGORARD's §3.3 dimension-$n$ argument cannot apply to the named rule. | OPEN. Depends on P2b and on a convergence notion G1 does not state. |

## Where this leaves the headline claim

The headline claim — that general relativity is derived from hypergraph rewriting — is **unsupported in the corpus**. Specifically:

- The main §3.3 argument of G1 uses undefined objects (S2) and a tautological definition (S3).
- G3 gives no proof for its named rule. The rule conserves edge count (PROVED), and its measured cone-growth exponents lie between 0.985 and 1.256 on small seeds (MEASURED, S5).
- The "provably satisfies EFE" claim assumes Poisson-distributed rewrite events and the assumptions of the Benincasa–Dowker action limit, and G3's comparison starts from initial data sampled from the target geometry (S4).
- The Riemannian identities used to calibrate hypergraph curvatures are mis-stated (S1) by non-trivial factors on simple test manifolds.

None of the errors is fabrication. All are public and checkable. The corpus is best described as *systematic overclaim with embedded mathematical errors*.
