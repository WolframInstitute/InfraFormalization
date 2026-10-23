# Corpus audit: findings that recur across G1-G4

This document lists, for each finding about the gravitational constructions, every paper and line where it occurs. Per-claim status with axiom lists is in [`STATUS_OF_GORARD_CLAIMS.md`](../STATUS_OF_GORARD_CLAIMS.md), and the findings F1-F8 are in [`MAJOR_FLAWS.md`](../MAJOR_FLAWS.md).

Line numbers refer to the text files `papers/gorard_*.txt`. The TeX sources are in `papers/tex_*`.

Status labels: PROVED (Lean, kernel-checked, sorry-free, axioms at most `propext`, `Classical.choice`, `Quot.sound`), VACUOUS (a Lean theorem whose statement does not concern the paper's objects), MEASURED, READ, OPEN.

## The corpus

| ID | Year | Title | arXiv | Text file |
|---|---|---|---|---|
| G1 | 2020 | Some Relativistic and Gravitational Properties of the Wolfram Model | 2004.14810 | `papers/gorard_2004.14810.txt` |
| G2 | 2020 | Algorithmic Causal Sets and the Wolfram Model | 2011.12174 | `papers/gorard_2011.12174.txt` |
| G3 | 2021 | Hypergraph Discretization of the Cauchy Problem in General Relativity via Wolfram Model Evolution | 2102.09363 | `papers/gorard_2102.09363.txt` |
| G4 | 2023 | Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems in Wolfram Model Systems | 2303.07282 | `papers/gorard_2303.07282.txt` |

## Finding 1. The Wasserstein expansion uses the scalar curvature R where Ollivier (2009) has Ric(v,v)

The papers state $W(B_\varepsilon(p),B_\varepsilon(q))=\delta\big(1-\tfrac{\varepsilon^2}{2(n+2)}R+O(\varepsilon^3+\varepsilon^2\delta)\big)$ with the scalar curvature $R$. Ollivier (2009, Example 7), which G2 and G3 cite, gives the same expansion with $\mathrm{Ric}(v,v)$, the Ricci curvature in the direction $v$ of the geodesic from $p$ to $q$. For $\delta,\varepsilon\neq0$ the two leading terms agree if and only if $R=\mathrm{Ric}(v,v)$. On the unit $S^2$, $R=2$ and $\mathrm{Ric}(v,v)=1$.

| Paper | Line | Text |
|---|---|---|
| G1 | 1468 (eq. 48) | the expansion with $R$; line 1475 calls the quantity the "Ricci scalar curvature" |
| G1 | 1532-1534 | "the Ollivier-Ricci scalar curvature κ (p, q) reduces (up to some arbitrary scaling factor) to the standard Riemannian Ricci scalar curvature R (p, q)" |
| G1 | 1772 | the same reduction, used to infer eq. 64 |
| G1 | 2054 (eq. 80) | the direction-averaged expansion with $R$ |
| G2 | 3517 (eq. 197) | the expansion with $R$ |
| G2 | 3581-3583 | "the Ollivier-Ricci scalar κ (p, q) reduces to the ordinary Riemannian Ricci scalar R (p, q)" |
| G2 | 4042 (eq. 225) | the direction-averaged expansion with $R$ |
| G3 | 5340 (eq. 344) | the expansion with $R$ |
| G3 | 5414-5416 | "the Ollivier-Ricci curvature scalar κ (p, q) reduces to the usual Riemannian Ricci curvature scalar R (p, q)" |
| G3 | 5868 (eq. 373) | the direction-averaged expansion with $R$ |

PROVED as arithmetic comparisons: `Infra.ollivier_minus_gorard_leading`, `Infra.ollivier_gorard_agree_iff`, `Infra.s2_gorard_error`. Ollivier's theorem is cited, not formalised. Details: [`results/phase2_continuum/eq344_verdict.md`](../results/phase2_continuum/eq344_verdict.md).

## Finding 2. The tube-volume coefficient differs from Gray (1973)

G2 and G3 give the $\varepsilon^2$ coefficient of the volume of a small geodesic tube as $\tfrac{d-1}{d+1}\big(R-\mathrm{Ric}(u,u)\big)$. Gray (1973) gives $\tfrac{R+\mathrm{Ric}(u,u)}{6(d+1)}$. On $S^2$ the two values are $1/3$ and $1/6$. On $S^3$ they differ by a factor of 6.

| Paper | Line | Coefficient |
|---|---|---|
| G1 | none | G1 contains no tube-volume formula |
| G2 | 2409 (eq. 126) | $\tfrac{d-1}{d+1}\big(R-\mathrm{Ric}(u,u)\big)$ |
| G3 | 5276 (eq. 342) | $\tfrac{d-1}{d+1}\big(R-\mathrm{Ric}(u,u)\big)$ |
| G4 | none | G4 contains no tube-volume formula |

PROVED as arithmetic comparisons: `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`. Gray's formula is cited, not formalised. Details: [`results/phase2_continuum/eq342_verdict.md`](../results/phase2_continuum/eq342_verdict.md).

## Finding 3. The argument for the Einstein equations

G1 §3.3 (lines 2168-2416) sums the discrete curvature into $S[g^{ab}]=\sum d\mu_g R$ (eq. 86, line 2200), sets its variation to zero (eq. 87, line 2211), states that the sum "becomes" the Einstein-Hilbert integral "subject to a weak ergodicity assumption" (line 2214, eq. 88), and concludes the vacuum Einstein equations (eq. 91, line 2259) "if a continuum limit exists in which the causal graph becomes a Riemannian manifold" (line 2264). Def 15 (lines 786-788) introduces a discrete Lorentzian metric g, and lines 799-801 state that the details of how it "can be explicitly obtained are outlined in the next section". G1 gives no formula for the components of $g^{ab}$ or for $d\mu_g$ in terms of the hypergraph, no definition of the variation of a discrete sum, no definition of weak ergodicity and no notion of convergence for "becomes" (READ; F1 and F5 in `MAJOR_FLAWS.md`).

| Paper | Lines | Text |
|---|---|---|
| G1 | 2168-2416 (eqs. 86-102) | the argument above |
| G2 | 4118-4160 (eqs. 227-229) | the same argument. G2 defines weak ergodicity as the vanishing, in the continuum limit, of the net flux of causal edges through every hypersurface of constant $x^\nu$ (lines 4136-4139). It then replaces weak ergodicity by "uniform (Poisson) distribution of causal set elements" (lines 4235-4237) to obtain the Benincasa-Dowker action (eq. 235) |
| G3 | 6076-6124 (eqs. 384-387) | replaces "the assumption of weak ergodicity of the causal graph dynamics with the much stronger assumption of uniform Poisson distribution of the rewrite events" (lines 6079-6081). The Benincasa-Dowker limit (eq. 387) is stated under zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood, with numerical support from Cunningham (lines 6110-6120) |
| G4 | 4713-4735 | restates the chain and concludes that "any Wolfram model rule which is causal invariant, weakly ergodic and asymptotically dimension preserving will be consistent with the Einstein field equations in the continuum limit" (lines 4733-4735) |

Lean: `Refutations/F1NoMetric.lean` and `Refutations/F5Illdefined.lean` are VACUOUS with respect to G1 (statements about a function type and about the sequence $1/(n+1)$). The findings rest on the reading.

## Finding 4. Asymptotic dimension preservation is stated as the Euler-Lagrange equation

G1 lines 2203-2211 state that asymptotic dimensionality preservation "corresponds to the statement" $\delta S[g^{ab}]/\delta g^{ab}\to0$ (eq. 87). This is the Euler-Lagrange equation of $S$, from which the Einstein equations follow by the standard variation (eqs. 89-91).

| Paper | Lines |
|---|---|
| G1 | 2170-2211 (eq. 87) |
| G2 | 4125-4133 (eq. 228: $\lim_{\rho_c\to\infty}\delta S/\delta g^{ab}=0$ as the condition for convergence to a finite dimension) |
| G3 | 150-152 and 271-273 (refer to rules that satisfy weak ergodicity and asymptotic dimension preservation) |
| G4 | 4726-4735 |

Lean: `asymptoticDimPreservation_iff_eulerLagrange` (`Refutations/F3Tautology.lean`) is PROVED by `Iff.rfl`. Both sides are the project's encoding `P.variation g = 0`. The encoding of eq. 87 is the READ finding.

## Finding 5. Orthonormality of non-parallel hyperedges is assumed without a bilinear form

G1 lines 2063-2065: "We also assume that all pairs of hyperedges which are not parallel (i.e. incident to the same set of vertices) can be considered to be orthonormal." G1 defines no bilinear form on hyperedges. The sentence occurs in G1 only. G2 (line 3981) and G3 (line 5794) use orthonormality of tangent vectors in the Riemannian definition of sectional curvature.

Lean: `Refutations/F2Orthonormality.lean` is VACUOUS with respect to G1 (statements about forms on `Bool`).

## Finding 6. Expansions stated for ε, δ → 0 are applied with ε = δ = 1

G1 lines 2059-2061 set all hyperedges to unit length and take $\varepsilon=\delta=1$ "in all of the definitions given above", which include expansions stated for $\varepsilon,\delta\to0$ (eqs. 79-80). G1 line 1790 states that the ball-volume expansion eq. 64 holds "for any sufficiently small value of r (with exactness when r = 1)". These sentences occur in G1 only.

## Finding 7. The rule of G3 line 6202

G3 states that the rule $\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\}\to\{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$ "provably satisfies the Einstein field equations in the continuum limit" (abstract, lines 50-52) and uses it in the §6 comparison (line 6202, Figures 73-84). G4 §5 uses the same rule (figure captions, lines 5140-5217) and describes it as a rewriting system that "provably satisfies the Einstein field equations in the continuum limit" (lines 4594-4598). Neither paper gives a proof for this rule (READ).

- PROVED: $|LHS|=|RHS|=4$, so every evolution preserves the edge count (`Refutations.gorardNamedRule_applications_preserve_size`). In every evolution from $N$ hyperedges, with any update order, every antichain of the causal graph has at most $N/4$ events (`CausalHistory.gorardNamedRule_antichain_card_le`) and at most $5^t$ events lie within directed distance $t$ of an event (`CausalHistory.gorardNamedRule_ball_card_le`).
- MEASURED: on cycles, paths and 3D grids of up to 300 edges and 2000 events, the log-log cone-growth exponent lies between 0.77 and 1.26 and depends on the update order (SetReplace 0.3.196 and `scripts/python/`; [`notes/empirical_refutation.md`](empirical_refutation.md) §4). On the 4-cycle and the 4-edge path the rule fires once and halts.
- OPEN: linear cone growth, stated as `CausalHistory.GorardNamedRuleConeGrowthLinear`.

## Per-paper summary

| Paper | Material added in the paper | Findings present |
|---|---|---|
| G1 | §3.3 argument for the discrete Einstein equations; Ollivier-Ricci curvature on directed hypergraphs; discrete ADM | 1, 3, 4, 5, 6 |
| G2 | tube-volume formula; causal-set d'Alembertian and Benincasa-Dowker action | 1, 2, 3, 4 |
| G3 | CCZ4 on a hypergraph mesh; Ψ4 extraction; comparison with evolution under the rule of line 6202 | 1, 2, 3, 4 (by reference), 7 |
| G4 | continuum WKB and Ernst-equation collapse analysis; numerical runs; comparison with evolution under the same rule | 3, 4, 7, and F8 of `MAJOR_FLAWS.md` (the title names discrete singularity theorems, and lines 76-78 and 351-357 state them as open) |

## Summary

- The continuum formulas the papers quote agree with the standard references, except the two coefficients of Findings 1 and 2 (READ, with the arithmetic comparisons PROVED).
- Finding 1 occurs in G1, G2 and G3 at the ten lines listed. Finding 2 occurs in G2 and G3.
- The §3.3 argument of G1 recurs in G2, G3 and G4. Each version uses an undefined discrete metric and variation, and weak ergodicity or Poisson-distributed events, for the passage from the discrete sum to the Einstein-Hilbert integral (READ). G2 and G3 state the Benincasa-Dowker limit under two assumptions with numerical support from Cunningham (G2 lines 3450-3456, G3 lines 6110-6120).
- For the rule of G3 line 6202, edge-count conservation and the antichain and cone bounds are PROVED, and linear cone growth is OPEN.
