# Continuum-limit claims in G1-G4

This document lists the statements in G1-G4 that assert convergence to, emergence of, or equivalence with a continuum geometric or physical object. For each it gives the text with its line number, the continuum object, and the status. Line numbers refer to `papers/gorard_*.txt`.

Status labels:

- Standard: a result from the cited literature, quoted in agreement with it (READ).
- Differs from source: the formula differs from the cited source; both formulas are given (READ, with the arithmetic comparison PROVED where noted).
- No proof: the paper states the claim and gives no proof, or uses an object it does not construct (READ).
- By definition: the claim holds by the definitions the paper uses (READ).
- Conditional: the paper states the claim under a named assumption or conjecture (READ).
- PROVED, MEASURED, OPEN: as in [`STATUS_OF_GORARD_CLAIMS.md`](../STATUS_OF_GORARD_CLAIMS.md).

## G1, arXiv:2004.14810

### Abstract (lines 23-27)

Text: "rigorous mathematical derivations of many key properties of such models in the continuum limit, as first discussed in NKS, including the fact that large classes of them obey discrete forms of both special and general relativity."
Continuum object: special and general relativity on Lorentzian manifolds.
Status: No proof. G1 does not define a continuum limit. The §3.3 items below give the details.

### §3.1, discrete Ricci scalar (lines 1427-1813)

Eq. 47 (line 1446). $\mathrm{Vol}(B_\varepsilon(p))/\mathrm{Vol}(B_\varepsilon(0)\subset\mathbb{R}^n)=1-\tfrac{R}{6(n+2)}\varepsilon^2+O(\varepsilon^4)$ as $\varepsilon\to0$.
Continuum object: scalar curvature.
Status: Standard (Gray 1973).

Eq. 48 (line 1468). $W(B_\varepsilon(p),B_\varepsilon(q))=\delta\big(1-\tfrac{\varepsilon^2}{2(n+2)}R+O(\varepsilon^3+\varepsilon^2\delta)\big)$ as $\varepsilon,\delta\to0$, with $\delta=d(p,q)$.
Continuum object: the scalar curvature $R$, as stated.
Status: Differs from source. Ollivier (2009, Example 7) gives the same expansion with $\mathrm{Ric}(v,v)$, the Ricci curvature in the direction $v$ of the geodesic from $p$ to $q$. On the unit $S^2$, $R=2$ and $\mathrm{Ric}(v,v)=1$. PROVED as an arithmetic comparison: `Infra.ollivier_gorard_agree_iff`, `Infra.s2_gorard_error`. See [`results/phase2_continuum/eq344_verdict.md`](../results/phase2_continuum/eq344_verdict.md).

Lines 1532-1534. "In the particular case in which (X, d) is a Riemannian manifold, and m is the standard Riemannian volume measure, the Ollivier-Ricci scalar curvature κ (p, q) reduces (up to some arbitrary scaling factor) to the standard Riemannian Ricci scalar curvature R (p, q)."
Continuum object: scalar curvature.
Status: Differs from source, as for eq. 48. Ollivier's limit is $\mathrm{Ric}(v,v)$ up to a factor depending on $n$ and $\varepsilon$.

Eqs. 64-65 (lines 1772-1798). $N(r)=ar^n\big(1-\tfrac{R}{6(n+2)}r^2+O(r^4)\big)$ for hypergraph ball counts, "for any sufficiently small value of r (with exactness when r = 1)" (line 1790).
Continuum object: scalar curvature.
Status: No proof. G1 infers eq. 64 from the reduction of lines 1532-1534 ("Using the fact that ... we infer", lines 1772-1774) and gives no convergence statement for hypergraph ball counts. See [`2004.14810_close_reading.md`](2004.14810_close_reading.md).

### §3.2, discrete spacetime Ricci curvature (lines 1814-2167)

Eq. 76 (line 1969) and eq. 83 (line 2131). $d\mu_g=\big[1-\tfrac16R_{jk}x^jx^k+O(\|x\|^3)\big]d\mu_{\mathrm{Euclidean}}$ in normal coordinates.
Continuum object: Ricci tensor.
Status: Standard.

Eq. 80 (line 2054). The direction-averaged Wasserstein expansion with $R$.
Status: Differs from source, as for eq. 48.

Lines 2059-2065. Hyperedges have unit length, $\varepsilon=\delta=1$ "in all of the definitions given above", and non-parallel hyperedges "can be considered to be orthonormal".
Status: No proof. The expansions are stated for $\varepsilon,\delta\to0$, and G1 defines no bilinear form on hyperedges.

Eq. 84 (line 2140). $C(t)=at^n\big[1-\tfrac16R_{jk}t^jt^k+O(\|t\|^3)\big]$ for the causal graph.
Continuum object: projection of the Ricci tensor on the time direction.
Status: No proof. G1 introduces eqs. 82 and 84 "by direct analogy to the spatial hypergraph case" (lines 2098 and 2109) and gives no convergence statement.

### §3.3, the discrete Einstein field equations (lines 2168-2612)

Eq. 86 (line 2200). $S[g^{ab}]=\sum d\mu_g R$.
Continuum object: Einstein-Hilbert action.
Status: No proof. G1 gives no formula for the components of $g^{ab}$ or for $d\mu_g$ in terms of the hypergraph (Def 15, lines 786-788), and the sum has no stated index set.

Eq. 87 (lines 2203-2211). Asymptotic dimensionality preservation "corresponds to the statement" $\delta S[g^{ab}]/\delta g^{ab}\to0$.
Continuum object: Euler-Lagrange equation of the Einstein-Hilbert action.
Status: By definition. The condition is the Euler-Lagrange equation of $S$. G1 does not define the variation of a discrete sum. `asymptoticDimPreservation_iff_eulerLagrange` (`Refutations/F3Tautology.lean`) is PROVED by `Iff.rfl` for the project's encoding.

Eq. 88 (lines 2214-2225). "In the continuum limit of an arbitrarily large causal graph, this sum becomes (subject to a weak ergodicity assumption on the dynamics of the causal graph) an integral", $S[g^{ab}]=\int d^4x\sqrt{-g}R$.
Continuum object: Einstein-Hilbert action.
Status: Conditional, and no proof. G1 states no notion of convergence for "becomes" and does not define weak ergodicity. The closest result in the causal-set literature is the Benincasa-Dowker limit, which G2 and G3 state under two assumptions with numerical support from Cunningham (2018). See [`limit_toolkit.md`](limit_toolkit.md).

Eq. 91 (line 2259). Vacuum Einstein equations $R_{ab}-\tfrac12Rg_{ab}=0$.
Continuum object: Einstein equations.
Status: Conditional. The variation of the continuum action (eqs. 89-90) is standard. G1 states the conclusion "if a continuum limit exists in which the causal graph becomes a Riemannian manifold" (line 2264), and it depends on eqs. 86-88.

Eq. 92 (line 2283). In the continuum limit and without non-gravitational forces, a test particle follows the geodesic equation.
Continuum object: geodesic equation.
Status: Conditional on eq. 91. G1 identifies test particles with persistent nonplanar "tangles" (lines 1305-1321, 2276) and proves eq. 92 from the continuum action of a timelike curve (lines 2288-2311).

Eq. 97 (line 2361). $R_{ab}-\tfrac12Rg_{ab}=8\pi T_{ab}$.
Continuum object: Einstein equations with matter.
Status: Conditional. G1 adds a matter Lagrangian density $L_M$ with an arbitrary constant $C_M$ (eq. 96, line 2349) and defines $T_{ab}$ by its variation (eqs. 98-99). G1 does not give $L_M$ as a function of the hypergraph.

Eq. 102 (line 2416). Einstein equations with cosmological constant.
Status: Conditional on eq. 91. Lines 2389-2395 introduce $2\Lambda$ as an arbitrary constant added to the sum of eq. 86.

Eq. 109 (line 2521). The derivation is "formally analogous" to the Chapman-Enskog expansion (line 2437) and "essentially equivalent" to one (lines 2514-2516), with $C(t)$ as a distribution function.
Continuum object: the hydrodynamic expansion, by analogy.
Status: No proof. G1 states the correspondence as an analogy and gives no theorem.

### §3.4, cosmology (lines 2613 onward)

Lines 2793-2805. A model with variable dimensionality "yields identical observational consequences to inflation".
Continuum object: FLRW cosmology with variable dimension.
Status: No proof. The hypergraph with variable dimension is described, not constructed.

## G2, arXiv:2011.12174

G2 restates the G1 material and adds causal-set material (Sorkin, Benincasa, Dowker).

Repeated from G1:

- Eq. 124 (line 2384): Riemannian ball-volume expansion. Standard.
- Eq. 126 (line 2409): tube-volume expansion with $\varepsilon^2$ coefficient $\tfrac{d-1}{d+1}\big(R-\mathrm{Ric}(u,u)\big)$. Differs from source: Gray (1973) gives $\tfrac{R+\mathrm{Ric}(u,u)}{6(d+1)}$. See [`results/phase2_continuum/eq342_verdict.md`](../results/phase2_continuum/eq342_verdict.md).
- Eq. 197 (line 3517): Wasserstein expansion with $R$. Differs from source, as for G1 eq. 48.
- Lines 3581-3583: "the Ollivier-Ricci scalar κ (p, q) reduces to the ordinary Riemannian Ricci scalar R (p, q)". Differs from source.
- Eq. 225 (line 4042): direction-averaged expansion with $R$. Differs from source.
- Eqs. 227-229 (lines 4118-4160): the G1 §3.3 argument. G2 defines weak ergodicity as the vanishing of the net flux of causal edges through every hypersurface of constant $x^\nu$ in the continuum limit (lines 4136-4139), and states that this "provides us with the analytic justification necessary to exchange this discrete sum for an integral". No proof of the exchange is given.

New in G2:

Eq. 172 (line 3197). $\lim_{\rho_c\to\infty}\rho_c^{-1/2}\langle\hat B_k^{(d)}\phi(x)\rangle=\Box\phi(x)-\tfrac12R(x)\phi(x)$ for $d=2,4$, for Poisson sprinklings, from the near region.
Continuum object: d'Alembertian and scalar curvature.
Status: Standard (Benincasa and Dowker 2010).

Eq. 194 (lines 3450-3465). The expectation of the Benincasa-Dowker action tends to the Einstein-Hilbert action as $\rho_c\to\infty$, "As argued by Sorkin, Benincasa and Dowker, and shown numerically by Cunningham for certain restricted cases", assuming that the contribution from down the light cone vanishes and zero surface terms.
Continuum object: Einstein-Hilbert action.
Status: Conditional. G2 states the two assumptions and cites numerical support.

Abstract lines 36-40 and lines 4235-4237. The Benincasa-Dowker action is a special case of the discrete Einstein-Hilbert action of Wolfram model systems "with ergodicity assumptions in the hypergraph replaced by Poisson distribution assumptions in the causal set".
Continuum object: causal sets sprinkled into a Lorentzian manifold.
Status: Conditional. G2 gives no proof that a Wolfram model evolution produces Poisson-distributed causal set elements.

## G3, arXiv:2102.09363

### Abstract (lines 50-52)

Text: "a hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit".
Continuum object: Einstein equations on a Lorentzian manifold.
Status: Conditional, and no proof for the rule. The argument (lines 6076-6124) replaces weak ergodicity by Poisson-distributed rewrite events and uses the Benincasa-Dowker limit under its two assumptions. G3 gives no proof that the rule of line 6202 produces Poisson-distributed events. For this rule: PROVED edge-count conservation, antichains of at most N/4 events and at most 5^t events within directed distance t (`CausalHistory.lean`); MEASURED cone-growth exponents between 0.77 and 1.26 on cycles, paths and 3D grids, depending on the update order ([`empirical_refutation.md`](empirical_refutation.md)); OPEN linear cone growth (`CausalHistory.GorardNamedRuleConeGrowthLinear`).

### §2-§5, CCZ4 on a hypergraph mesh (lines 310-4779)

The CCZ4 formulation of the Einstein equations is solved by finite differences on a hypergraph mesh. §5 (lines 2530-4779, Tables 1-5) reports approximately fourth-order convergence for Schwarzschild, Kerr, Einstein-Rosen bridge and binary black hole tests.
Continuum object: Schwarzschild, Kerr and Brill-Lindquist solutions.
Status: Standard numerical relativity. The hypergraph is the mesh of the solver.

Lines 3960-4345. The Weyl scalar $\Psi_4$ (eq. 267) is computed by projection on a null tetrad and integrated to the strain $h_+-ih_\times$ (eq. 303).
Continuum object: outgoing gravitational radiation.
Status: Standard. The tetrad is built from the evolved metric. See [`null_tetrad_resolution.md`](null_tetrad_resolution.md).

### §6, discrete curvature and comparison with Wolfram model evolution (lines 4780-6463)

- Eq. 340 (line 5241): ball-volume integral. Standard.
- Eq. 342 (line 5276): tube volume with coefficient $\tfrac{d-1}{d+1}\big(R-\mathrm{Ric}(u,u)\big)$. Differs from source: Gray (1973) gives $\tfrac{R+\mathrm{Ric}(u,u)}{6(d+1)}$; the values on $S^2$ are $1/3$ and $1/6$. PROVED as arithmetic comparisons: `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`.
- Eq. 343 (line 5306): ball-volume ratio. Standard.
- Eq. 344 (line 5340): Wasserstein expansion with $R$. Differs from source, as for G1 eq. 48.
- Lines 5414-5416: "the Ollivier-Ricci curvature scalar κ (p, q) reduces to the usual Riemannian Ricci curvature scalar R (p, q)". Differs from source.
- Eq. 373 (line 5868): direction-averaged expansion with $R$. Differs from source.
- Eq. 386 (line 6105): $S^{(4)}(C)=\tfrac{4}{\sqrt6}\big[n-N_0+9N_1-16N_2+8N_3\big]$. Standard (Benincasa-Dowker action).
- Eq. 387 (lines 6110-6124): the expectation of the action tends to $S_{\mathrm{EH}}(g)$ as $\rho_c\to\infty$, "as proposed by Sorkin, Benincasa and Dowker, and demonstrated numerically by Cunningham", assuming zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood. Conditional.

Lines 6076-6084. "replacing the assumption of weak ergodicity of the causal graph dynamics with the much stronger assumption of uniform Poisson distribution of the rewrite events, our construction of the discrete Einstein-Hilbert action for Wolfram model systems reduces to the general d-dimensional form of the Benincasa-Dowker action on causal sets."
Status: Conditional. From this point the argument concerns Poisson-distributed events. G3 gives no proof that the rule of line 6202 produces them.

Lines 6146-6181. The initial hypergraph is built "by means of a Poisson point process" (lines 6148-6152, eq. 389) so that it is "faithfully embeddable into a given Lorentzian manifold (M, g)", with links within "a certain cut-off distance" (line 6176), and is used for "the standard Brill-Lindquist binary black hole initial data" (line 6179).
Status: READ. The comparison starts from a sample of the target initial data. G3 does not state the cut-off distance, the update order or the number of events per unit of the time coordinate. See [`2102.09363_close_reading.md`](2102.09363_close_reading.md).

Lines 6185-6463. Figures 73-77 and 79-83 show the direct numerical solution and the pure Wolfram model evolution under the rule of line 6202. Tables 6 and 7 report approximately second-order convergence of the Hamiltonian constraint of the pure Wolfram model evolution at 100 to 1600 vertices.
Status: READ. The procedure that computes the Hamiltonian constraint from a hypergraph is not stated.

## G4, arXiv:2303.07282

### Abstract (lines 67-78)

Text: "we are able to show, through a combination of rigorous mathematical analysis and explicit numerical simulation, that the resulting discrete spacetimes converge asymptotically to either non-rotating Schwarzschild black hole solutions or maximally-rotating (extremal) Kerr black hole solutions".
Continuum object: Schwarzschild and extremal Kerr black holes.
Status: Standard for the continuum analysis: §3 follows Gonçalves and Moss (line 1756) with the WKB approximation, and §4 follows Neugebauer and Meinel (line 3188) with the Ernst equation. The Wolfram model part (§5, lines 4592 onward) uses the rule of G3 line 6202 (lines 5140-5217) and the G1 chain with weak ergodicity and asymptotic dimension preservation (lines 4713-4735). Conditional, as for G3.

### Title

Text: "Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems in Wolfram Model Systems" (lines 1-3).
Continuum object: a discrete analogue of the Penrose and Hawking singularity theorems.
Status: READ. G4 states no discrete singularity theorem. The abstract states that the results "offer hope that a more general, perhaps ultimately “Penrose-like”, singularity theorem may be provable in the discrete spacetime case too" (lines 76-78). See [`2303.07282_close_reading.md`](2303.07282_close_reading.md).

### Raychaudhuri equation

Text: "the appropriate discrete analog of the Raychaudhuri equation somewhat non-obvious" (line 351), and "there has as of yet been no systematic investigation of discrete analogs of standard general relativistic energy conditions" (lines 355-357).
Status: READ. G4 does not construct a discrete Raychaudhuri equation, expansion scalar or energy condition.

### Green's functions (lines 5040-5046)

Text: "By replacing the continuum Ricci scalar R (x) with the discrete (Ollivier-Ricci) scalar curvature for Wolfram model hypergraphs/causal graphs, we obtain a corresponding construction for arbitrary Wolfram model systems."
Status: No proof. The substitution is stated, and details are referred to G4's reference [28].

## Summary

| Type | Items | Status |
|---|---|---|
| Riemannian formulas quoted from the literature | G1 eqs. 47, 76, 83, 89-90; G2 eq. 124; G3 eqs. 340, 343 | Standard |
| Numerical relativity | G3 §2-§5, Ψ4 extraction; G4 §3-§4 continuum analysis | Standard |
| Causal-set results | G2 eq. 172; G3 eq. 386 | Standard |
| Benincasa-Dowker action limit | G2 eq. 194; G3 eq. 387 | Conditional on two stated assumptions, with numerical support |
| Wasserstein expansion with R | G1 eqs. 48, 80, lines 1532-1534, 1772; G2 eqs. 197, 225, lines 3581-3583; G3 eqs. 344, 373, lines 5414-5416 | Differs from Ollivier (2009) |
| Tube-volume coefficient | G2 eq. 126; G3 eq. 342 | Differs from Gray (1973) |
| Discrete objects without a construction | G1 eq. 86, Def 15, lines 2063-2065, eq. 96 | No proof |
| Equivalences by definition | G1 eq. 87; G1 lines 1063-1089 | By definition |
| Passage from discrete sum to integral | G1 eq. 88; G2 eq. 229; G3 lines 6076-6124; G4 lines 4713-4735 | Conditional on weak ergodicity or Poisson-distributed events |
| The rule of G3 line 6202 | G3 abstract, §6; G4 §5 | Conditional; PROVED bounds, MEASURED exponents and OPEN linear growth as above |
| Title and abstract of G4 | G4 lines 1-3, 76-78 | READ: stated as open in the body |

The items G1 eqs. 86-92, 97 and 102, G1 eqs. 64-65 and 84, G2 eq. 229, G3 lines 6076-6124 and the G3 abstract carry the argument from hypergraph rewriting to the Einstein equations. None of them has a proof in G1-G4. Each relies on an object the papers do not construct, on weak ergodicity or Poisson-distributed events, or on the Benincasa-Dowker limit under its two assumptions.
