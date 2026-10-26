# Classification of the main claims of G1, G3 and G4

This document assigns each main claim of G1 (arXiv:2004.14810), G3 (arXiv:2102.09363) and G4 (arXiv:2303.07282) to one category, with the lines it rests on. Line numbers refer to `papers/gorard_*.txt`. Per-claim status with axiom lists is in [`STATUS_OF_GORARD_CLAIMS.md`](../STATUS_OF_GORARD_CLAIMS.md), and the paper-by-paper occurrences are in [`corpus_audit.md`](corpus_audit.md).

Categories:

- (S) Standard result, cited from differential geometry, numerical relativity or causal-set theory.
- (A) Stated under an assumption or a conjecture that the paper names.
- (N) Stated without proof: the step uses an object the paper does not construct, or an analogy.
- (D) Holds by the definitions the paper uses.
- (F) A formula that differs from the cited source.
- (T) Named in the title or abstract, and stated in the body as open.

Each classification is READ unless a PROVED, MEASURED or OPEN label is given.

## G1, arXiv:2004.14810

| # | Claim | Category | Lines and note |
|---|---|---|---|
| A1 | Causal invariance corresponds to discrete general covariance | D | Lines 1063-1075 describe both as independence of the outcome from the updating order (foliation). Lean: none. |
| A2 | Causal invariance gives discrete Lorentz covariance | D | Lines 1079-1089: the constancy of the speed of light "is enforced axiomatically by our definition of the edge lengths in causal graphs, this completes the proof". |
| A3 | The Ollivier-Ricci curvature reduces to "the standard Riemannian Ricci scalar curvature R (p, q)" | F | Lines 1468 (eq. 48), 1532-1534, 2054 (eq. 80). Ollivier (2009) has the directional Ricci curvature Ric(v,v). PROVED as an arithmetic comparison: `Infra.ollivier_gorard_agree_iff`. |
| A4 | Non-parallel hyperedges "can be considered to be orthonormal" | N | Lines 2063-2065. No bilinear form on hyperedges is defined. |
| A5 | Hypergraph ball counts satisfy N(r) = a rⁿ(1 − R r²/(6(n+2)) + O(r⁴)) | N | Lines 1772-1798 (eqs. 64-65) infer this from A3, "for any sufficiently small value of r (with exactness when r = 1)" (line 1790). No derivation for hypergraphs is given. |
| A6 | δS/δg^ab → 0 gives the vacuum Einstein equations in the continuum limit | N, D | Lines 2168-2264 (eqs. 86-91). The discrete metric of Def 15 (lines 786-788) and the variation of a discrete sum are not constructed, and "becomes" (line 2214) has no stated notion of convergence. Eq. 87 states dimension preservation as the Euler-Lagrange equation (D). Lean: none. |
| A7 | The derivation is a Chapman-Enskog expansion | N | Line 2437 calls the derivation "formally analogous" to the Chapman-Enskog expansion, and lines 2514-2516 call it "essentially equivalent" to one, with C(t) of eq. 109 as the distribution function. No theorem is stated. |

## G3, arXiv:2102.09363

| # | Claim | Category | Lines and note |
|---|---|---|---|
| B1 | The CCZ4 equations can be evolved on a hypergraph mesh | S | §2-§5 (lines 310-4779). The hypergraph serves as the mesh of a finite-difference solver for the Einstein equations. |
| B2 | Gravitational waves are extracted through the Weyl scalar Ψ4 | S | Lines 3960-4345 (eq. 267 onward): Newman-Penrose projection with a null tetrad built from the evolved metric. See [`null_tetrad_resolution.md`](null_tetrad_resolution.md). |
| B3 | "a hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit" | A | Abstract lines 50-52. Lines 6079-6081 replace weak ergodicity by "uniform Poisson distribution of the rewrite events". The Benincasa-Dowker limit (eq. 387, lines 6110-6124) is stated under zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood, with numerical support from Cunningham. G3 gives no proof that the rule of line 6202 produces Poisson-distributed events. |
| B3' | The rule is {{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}} | PROVED, MEASURED, OPEN | Line 6202. PROVED: edge-count conservation (`Refutations.gorardNamedRule_applications_preserve_size`), antichains of at most N/4 events (`CausalHistory.gorardNamedRule_antichain_card_le`), at most 5^t events within directed distance t (`CausalHistory.gorardNamedRule_ball_card_le`), for every update order. MEASURED: on cycles, paths and 3D grids of up to 300 edges and 2000 events the cone-growth exponent lies between 0.77 and 1.26 and depends on the update order. On the 4-cycle and 4-edge path the rule fires once ([`empirical_refutation.md`](empirical_refutation.md)). OPEN: linear cone growth, `CausalHistory.GorardNamedRuleConeGrowthLinear`. |
| B4 | The pure Wolfram model evolution reproduces the numerical solution for binary black holes | A | §6 (lines 6146-6463). The initial hypergraph is a Poisson sample of the Brill-Lindquist data (lines 6148-6152, 6179), with an unstated cut-off distance (line 6176). Figures 73-77 and 79-83 show the direct numerical solution and the pure Wolfram model evolution side by side. Tables 6 and 7 (lines 6226-6246, 6383-6392) report approximately second-order convergence of the Hamiltonian constraint of the pure Wolfram model evolution at 100 to 1600 vertices. |
| B5 | Convergence tests for Schwarzschild, Kerr and binary black holes | S | §5 (lines 2530-4779), Tables 1-5: approximately fourth-order convergence of the finite-difference scheme. These tests concern the PDE solver. |

## G4, arXiv:2303.07282

G4 contains no labelled theorems, propositions or definitions, and the words "shear" and "vorticity" do not occur in it. Close reading: [`2303.07282_close_reading.md`](2303.07282_close_reading.md).

| # | Claim | Category | Lines and note |
|---|---|---|---|
| C1 | A discrete analogue of the Raychaudhuri equation | T | Title lines 1-3. The abstract (lines 37-41) calls it "subtle to formulate", and lines 351-357 call it "somewhat non-obvious". G4 does not construct it. |
| C2 | A discrete singularity theorem | T | The abstract (lines 76-78) states that the results "offer hope that a more general, perhaps ultimately “Penrose-like”, singularity theorem may be provable". The conclusions (lines 5377-5391) name a global topological theorem and discrete energy conditions as directions for further work. |
| C3 | Collapse of a massive scalar field converges to Schwarzschild or extremal Kerr | S, A | §3 follows Gonçalves and Moss (line 1756) and §4 follows Neugebauer and Meinel (line 3188): continuum analysis, with numerical runs. The conclusions (lines 5359-5361) state that both solutions "may be recovered as limiting cases of a pure Wolfram model/hypergraph rewriting evolution". §5 uses the rule of G3 line 6202 (lines 5140-5217) and the G1 chain with weak ergodicity and asymptotic dimension preservation (lines 4713-4735). |
| C4 | Green's functions of a massive scalar field on Wolfram model causal graphs | N | Lines 5040-5046 replace "the continuum Ricci scalar R (x) with the discrete (Ollivier-Ricci) scalar curvature" in a continuum formula, and refer to [28] for details. |

## Counts

- S: B1, B2, B5, and the continuum part of C3.
- A: B3, B4, and the Wolfram-model part of C3.
- N: A4, A5, A6, A7, C4.
- D: A1, A2, and eq. 87 within A6.
- F: A3.
- T: C1, C2.

## Lean formalisation of these findings

- `Refutations/F7NamedRuleStructure.lean` and `CausalHistory.lean`: PROVED results about the rule of G3 line 6202, listed under B3'.
- The other findings are READ findings with the line numbers above. They have no Lean module.
