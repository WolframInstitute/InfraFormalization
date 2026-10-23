# Classification of the findings on G1-G4

This note groups the findings on the gravitational constructions of G1 = arXiv:2004.14810 (`papers/gorard_2004.14810.txt`), G2 = arXiv:2011.12174 (`papers/gorard_2011.12174.txt`), G3 = arXiv:2102.09363 (`papers/gorard_2102.09363.txt`) and G4 = arXiv:2303.07282 (`papers/gorard_2303.07282.txt`) into six groups, S1 to S6. Line numbers refer to these text files. `FINDINGS.md` lists the same sixteen items one line each, and `STATUS_OF_GORARD_CLAIMS.md` gives the Lean theorems with their axioms.

Status labels: PROVED (Lean, kernel-checked, sorry-free, axioms at most `propext`, `Classical.choice`, `Quot.sound`), VACUOUS (a Lean theorem whose statement does not concern the paper's objects), MEASURED, READ (from the paper text, with line numbers), OPEN.

## Groups

- S1. A formula that differs from the source the paper cites for it.
- S2. A statement that uses an object the paper does not define or construct.
- S3. An equivalence whose two sides describe the same property.
- S4. A passage from a discrete object to a continuum one stated without proof.
- S5. Statements about the rule of G3 line 6202.
- S6. Titles and abstracts.

## S1. Formulas that differ from the cited sources

| # | Finding | Where | Status |
|---|---|---|---|
| 1 | The average distance between ε-balls transported a distance δ along a geodesic is given as $\delta\,(1-\frac{\epsilon^2}{2(n+2)}R+\dots)$, with the scalar curvature $R$. Ollivier (2009, Example 7), which the papers cite, has $\delta\,(1-\frac{\epsilon^2}{2(n+2)}\mathrm{Ric}(v,v)+\dots)$, with $\mathrm{Ric}(v,v)$ the Ricci curvature in the direction $v$ of the geodesic. The two agree when $R=\mathrm{Ric}(v,v)$. G1 lines 1530-1534 also state that the Ollivier-Ricci curvature κ(p, q) reduces to "the standard Riemannian Ricci scalar curvature R (p, q)". | G1 eq. 48 (line 1468), G1 eq. 80 (lines 2044-2057), G2 eq. 197 (line 3517), G3 eq. 344 (line 5340) | READ. The comparison of the leading terms is PROVED as arithmetic: `Infra.ollivier_minus_gorard_leading`, `Infra.ollivier_gorard_agree_iff`, `Infra.s2_gorard_error`. Ollivier's theorem is cited, not formalised. `results/phase2_continuum/eq344_verdict.md` |
| 2 | The volume of a tube of radius ε around a geodesic segment with unit tangent u is given with the $\epsilon^2$ coefficient $-\frac{d-1}{d+1}(R-\mathrm{Ric}(u,u))$. Gray (1973) gives $-\frac{1}{6(d+1)}(R+\mathrm{Ric}(u,u))$. On the unit $S^2$ the two coefficients are $-1/3$ and $-1/6$; on the unit $S^3$ they are $-2$ and $-1/3$. | G2 eq. 126 (line 2409), G3 eq. 342 (line 5276) | READ. The comparison on $S^2$ and $S^3$ is PROVED as arithmetic: `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`. Gray's formula is cited, not formalised. `results/phase2_continuum/eq342_verdict.md` |

Substituting the coefficients of the cited sources corrects both formulas.

## S2. Objects used without a definition

| # | Finding | Where | Status |
|---|---|---|---|
| 3 | The discrete Einstein-Hilbert action $S[g^{ab}]=\sum d\mu_g R$ uses a metric $g^{ab}$ and a measure $d\mu_g$. G1 Def 15 introduces "a discrete Lorentzian metric" of signature (− + + +) and gives no procedure that computes its components from the hypergraph or the causal graph. $d\mu_g$ appears in G1 eq. 76 as the Riemannian volume element. G2 eq. 227 (line 4122) has the same sum. | G1 eq. 86 (line 2200), Def 15 (lines 786-790) | READ. Lean: `Refutations/F1NoMetric.lean`, VACUOUS (the function type `DHyp V → V → V → ℝ` has more than one element) |
| 4 | The functional derivative $\delta S/\delta g^{ab}$ is applied to the discrete sum of item 3. It requires components of $g$ that can be varied, a space of perturbations and an inner product on it. G2 eq. 228 (lines 4127-4133) states the same condition as a limit $\rho_c\to\infty$. | G1 eq. 87 (lines 2203-2211) | READ |
| 5 | "We also assume that all pairs of hyperedges which are not parallel (i.e. incident to the same set of vertices) can be considered to be orthonormal." G1 defines no bilinear form on hyperedges. | G1 lines 2063-2065 | READ. Lean: `Refutations/F2Orthonormality.lean`, VACUOUS (facts about forms on `Bool`) |
| 6 | The expansions of eqs. 64-65 hold as r → 0, and eq. 80 as ε, δ → 0. G1 sets ε = δ = 1 (lines 2059-2061) and states that the ball-volume expansion holds "with exactness when r = 1" (line 1790). G1 gives no error bound at these values. | G1 lines 1790, 2059-2061 | READ |

## S3. Equivalences whose two sides describe the same property

| # | Finding | Where | Status |
|---|---|---|---|
| 7 | Causal invariance "corresponds precisely" to the ordering of timelike-separated events being independent of the foliation, which G1 calls "a discretized version of the principle of general covariance". Both sides describe independence of the causal graph from the updating order. | G1 lines 1063-1077 | READ. The project's encoding is PROVED by `Iff.rfl`: `causalInvariance_iff_discreteGeneralCovariance` (`Refutations/F4Tautology.lean:51`) |
| 8 | For flat foliations causal invariance reduces to discrete Lorentz covariance. The constancy of the speed of light "is enforced axiomatically by our definition of the edge lengths in causal graphs". | G1 lines 1079-1089 | READ |
| 9 | Asymptotic dimensionality preservation "corresponds to the statement" $\delta S/\delta g^{ab}\to 0$. This condition is the Euler-Lagrange equation of S, so the conclusion that such rules satisfy the vacuum Einstein equations restates the hypothesis. | G1 lines 2203-2211 | READ. The project's encoding is PROVED by `Iff.rfl`: `asymptoticDimPreservation_iff_eulerLagrange` (`Refutations/F3Tautology.lean:57`) |

## S4. Passages from discrete to continuum without a proof

| # | Finding | Where | Status |
|---|---|---|---|
| 10 | "In the continuum limit of an arbitrarily large causal graph, this sum becomes (subject to a weak ergodicity assumption on the dynamics of the causal graph) an integral". G1 states no notion of convergence and does not define weak ergodicity. G2 (lines 4136-4150) defines weak ergodicity as a zero net flux of causal edges through every hypersurface of constant $x^\nu$ in the continuum limit and states the exchange of sum and integral (eq. 229) without proof. G3 (lines 6076-6082) replaces weak ergodicity with "the much stronger assumption of uniform Poisson distribution of the rewrite events" and uses the Benincasa-Dowker limit, which holds "so long as one assumes zero surface terms" and a vanishing contribution from outside the Riemann normal neighbourhood, with numerical support from Cunningham (lines 6110-6120). | G1 line 2214 (eq. 88); G2 eq. 229; G3 lines 6076-6120 | READ. OPEN as a mathematical statement. Lean: `Refutations/F5Illdefined.lean`, VACUOUS (facts about the sequence 1/(n+1)) |
| 11 | The rule {{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}} "provably satisfies the Einstein field equations in the continuum limit". G3 gives no proof for this rule. G3 assumes Poisson-distributed rewrite events (line 6080) and samples the initial hypergraph from the target geometry (lines 6148-6152, 6179). | G3 lines 50-52, 6202 | READ. See `STATUS_OF_GORARD_CLAIMS.md`, Claims 1-2 |
| 12 | G1 uses the reduction of the Ollivier-Ricci curvature to Riemannian curvature on a manifold to infer the curvature correction of hypergraph ball counts. G1 gives no convergence theorem for the Ollivier-Ricci curvature of directed hypergraphs. Convergence theorems exist for random geometric graphs (García Trillos and Slepčev 2018), not for hypergraph rewriting evolutions. | G1 lines 1772-1803 (§3.1) | READ. OPEN |

## S5. The rule of G3 line 6202

| # | Finding | Status |
|---|---|---|
| 13 | G3 uses the rule as one that satisfies the Einstein equations in 3+1 dimensions. G1's §3.3 argument uses causal-graph cone counts $C(t)=at^n(1-\dots)$ with $n=4$. | PROVED: the rule conserves edge count (`Refutations.gorardNamedRule_applications_preserve_size`); in every evolution from N hyperedges, with any update order, every antichain of the causal graph has at most N/4 events (`CausalHistory.gorardNamedRule_antichain_card_le`) and at most $5^t$ events lie within directed distance t of an event (`CausalHistory.gorardNamedRule_ball_card_le`). MEASURED: log-log cone-growth exponents between 0.77 and 1.26 on cycles, paths and 3D grids of up to 300 edges and 2000 events, depending on the update order (`notes/empirical_refutation.md`, `results/phase1_selfaudit/README.md`). OPEN: linear cone growth, `CausalHistory.GorardNamedRuleConeGrowthLinear`. |
| 14 | Hypergraph ball counts satisfy $N(r)=ar^n(1-\frac{R}{6(n+2)}r^2+O(r^4))$. G1 transfers the Riemannian ball-volume expansion to vertex counts and gives no derivation for hypergraphs. G1 eq. 84 transfers the expansion of the volume element to causal-graph cone counts in the same way ("by analogy to the purely spatial case", lines 2109-2145). | READ: G1 eqs. 64-65 (lines 1772-1803) |

## S6. Titles and abstracts

| # | Finding | Status |
|---|---|---|
| 15 | The title of G4 is "Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems in Wolfram Model Systems" (lines 1-3). The abstract states that the discrete analog of Raychaudhuri's equation is "subtle to formulate" and that for a trapped null surface "no appropriate translation is known" (lines 39-43), and that the results "offer hope that a more general, perhaps ultimately “Penrose-like”, singularity theorem may be provable in the discrete spacetime case too" (lines 75-79). Lines 351-357 state that there has been "no systematic investigation of discrete analogs of standard general relativistic energy conditions". Lines 511-518 and 5377-5395 describe a general discrete singularity theorem and discrete energy conditions as future work. G4 contains no discrete Raychaudhuri equation and no discrete energy condition, and the words "shear" and "vorticity" do not occur. | READ |
| 16 | "Provably" in the G3 abstract (lines 50-52) applies to a chain that assumes Poisson-distributed rewrite events (line 6080) and the zero-surface-term and Riemann-normal-neighbourhood assumptions of the Benincasa-Dowker limit (lines 6110-6120). | READ |

## Recurrence across the papers

- The formula of item 1 appears four times: G1 eq. 48, G1 eq. 80, G2 eq. 197 and G3 eq. 344.
- The formula of item 2 appears twice: G2 eq. 126 and G3 eq. 342.
- The discrete action and its variation (items 3-4) appear in G1 eqs. 86-87 and G2 eqs. 227-228. G3 uses the Benincasa-Dowker action of a causal set (eq. 384, line 6088) under the Poisson assumption of item 10.
- Items 5 and 6 appear in G1 only.

## Where the details are

- Item 1: `results/phase2_continuum/eq344_verdict.md`
- Item 2: `results/phase2_continuum/eq342_verdict.md`
- Items 3-10, 12, 14: `notes/2004.14810_close_reading.md`, `notes/claims_catalog.md`
- Items 11, 16: `notes/2102.09363_close_reading.md`, `STATUS_OF_GORARD_CLAIMS.md`
- Item 13: `notes/empirical_refutation.md`, `results/phase1_selfaudit/README.md`
- Item 15: `notes/2303.07282_close_reading.md`
- Cross-paper: `notes/corpus_audit.md`
