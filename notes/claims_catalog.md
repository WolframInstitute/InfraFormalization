# Claims catalog — arXiv:2004.14810 "Some Relativistic and Gravitational Properties of the Wolfram Model"

This catalog lists every `\begin{equation}`, `\begin{align}` and `\begin{definition}` block in the TeX source `papers/tex_2004/RelativityAndGravitation.tex` (1505 lines) of G1, with six passages of running text. Every entry is a READ finding. The TeX line is the line of the block in the TeX source. The text line is the line of the equation number or definition heading in `papers/gorard_2004.14810.txt`.

Type:
- `DEF`: a `\begin{definition}` block.
- `STD`: a standard continuum result quoted from the literature.
- `CONT-COMP`: a continuum computation in the paper.
- `DISCR-DEF`: a definition for discrete hypergraphs or causal graphs.
- `DISCR-ASSERT`: a statement about a discrete object given without proof.
- `BRIDGE`: a statement relating a discrete object to a continuum one.
- `CONCL`: a conclusion stated in the text.

Reading:
- Standard: agrees with the cited or standard reference.
- Definition: a discrete definition with no further note.
- Notation: a typographical or notational point that does not change the content.
- Undefined: uses an object that G1 does not define or construct.
- Hypothesis: stated as an assumption.
- By definition: the two sides of the stated equivalence describe the same property.
- No proof: G1 states the result and gives no derivation.
- Differs from source: the formula differs from the cited source. Both formulas are given.
- Standard (continuum): a correct continuum formula that G1 reaches through rows marked Undefined or No proof.

---

## §2.1 — Basic formalism and causal graphs

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 1 | 68 | 233 | Def 1 | DEF | "spatial hypergraph" $H=(V,E)$ finite undirected, $E\subseteq \mathcal P(V)\setminus\{\emptyset\}$ | Undefined | Def 1 defines undirected hypergraphs. Def 33 (line 1592) uses directed hypergraphs, which G1 does not define. |
| 2 | 71 | 237 | (1) | DEF | $E \subseteq \mathcal{P}(V)\setminus\lbrace\emptyset\rbrace$ | Standard | Berge (1989). |
| 3 | 80 | 252 | Def 2 | DEF | "trivalent spatial graph" $G=(V,E)$ finite undirected 3-regular | Standard | |
| 4 | 87 | 274 | Def 3 | DISCR-DEF | "update rule" $R: H_1\to H_2$ with same number of outgoing hyperedges, preserving symmetries of $H_1$ | Undefined | Def 3 refers to "outgoing hyperedges", which Def 1 does not define, and to symmetries of $H_1$ without a definition (lines 274-278). |
| 5 | 93 | 288 | Def 4 | DISCR-DEF | "causal graph" $G_{causal}$: $A\to B$ iff update rule at $B$ was only applicable as a result of outcome of $A$ | Undefined | G1 does not define "only applicable as a result of" in terms of consumed and created hyperedges (lines 288-292). |

## §2.2 — Abstract rewriting, Church–Rosser, causal invariance

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 6 | 125 | 367 | Def 5 | DEF | "abstract rewriting system" = set $A$ with binary relation $\to$ | Standard | Baader-Nipkow, standard. |
| 7 | 132 | 382 | (2) | STD | $a \to a' \to a'' \to \dots \to b' \to b$ | Standard | Notation for rewrite sequences. |
| 8 | 137 | 390 | Def 6 | DEF | $\to^*$ = reflexive transitive closure of $\to$ | Standard | |
| 9 | 142 | 401 | (3) | STD | $a\to^* a$; $a\to^* b, b\to^* c \Rightarrow a\to^* c$ | Standard | Reflexivity + transitivity axioms. |
| 10 | 148 | 409 | Def 7 | DEF | Object $a$ is confluent | Standard | Baader-Nipkow, standard. |
| 11 | 151 | 413 | (4) | STD | $\forall b,c\in A, a\to^*b\wedge a\to^*c\Rightarrow \exists d:b\to^*d\wedge c\to^*d$ | Standard | Standard confluence predicate. |
| 12 | 156 | 416 | Def 8 | DEF | ARS $A$ is (globally) confluent / Church-Rosser | Standard | Church–Rosser 1936. |
| 13 | 170 | 458 | Def 9 | DISCR-DEF | "causal invariant" multiway system: all causal graphs eventually isomorphic as DAGs | Undefined | Def 9 does not state when "eventually" holds. See close reading §2.2. |
| 14 | 186 | 499 | (5) | CONT-COMP | $\to_1 \cup \to_2 \;=\; \to$ | Standard | Notation for decomposing a rewrite relation. |
| 15 | 191 | 510 | (6) | CONT-COMP | $p\mapsto\{(\alpha,q)\in\Lambda\times A:p\to^\alpha q\}$ | Standard | Coalgebra form of the rewrite relation. |
| 16 | 196 | 528 | (7) | STD | $\mathcal P: Set\mapsto Set$ (powerset endofunctor) | Standard | Powerset endofunctor. |
| 17 | 201 | 535 | (8) | STD | $\to: A\mapsto \mathcal P A$ | Standard | Rewrite relation as a map $A\to\mathcal P A$. |
| 18 | 208 | 552 | (9) | STD | local-confluence condition | Standard | Standard weakening. |
| 19 | 213 | 561 | (10) | STD | semi-confluence condition | Standard | |
| 20 | 218 | 570 | (11) | STD | diamond property | Standard | |
| 21 | 223 | 581 | (12) | STD | strong confluence | Standard | |
| 22 | 230 | 603 | (13) | STD | $((\lambda x.M)E)\to (M[x:=E])$ ($\beta$-reduction) | Standard | Standard λ-calculus. |
| 23 | 235 | 618 | (14) | STD | joinability $x\downarrow y \iff \exists z: x\to^*z\leftarrow^* y$ | Standard | |

## §2.3 — Causal graph hypersurfaces and discrete Lorentz covariance

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 24 | 246 | 642 | Def 10 | DEF | "layered graph embedding" of a DAG in the plane with monotonic-downward edges, minimising crossings | Standard | Di Battista–Tamassia, standard. |
| 25 | 251 | 654 | Def 11 | DEF | "downward planar embedding" (no crossings) | Standard | |
| 26 | 257 | 668 | (15) | STD | $\mathbf p=(t,\mathbf x)$ | Standard | Coordinate labelling. |
| 27 | 262 | 675 | (16) | STD | $\mathbf x=(x_1,\dots,x_n)\in\mathbb Z^n$ | Standard | Coordinate labelling. |
| 28 | 267 | 682 | Def 12 | DISCR-DEF | "discrete Minkowski norm" | Notation | The functional takes negative values, so it is not a norm. It is the Minkowski interval. |
| 29 | 270 | 686 | (17) | DISCR-DEF | $\lVert(t,\mathbf x)\rVert=\lVert \mathbf x\rVert^2 - t^2$ | Notation | Same as row 28. |
| 30 | 275 | 695 | (18) | DISCR-DEF | $\lVert(t,\mathbf x)\rVert=(x_1^2+\dots+x_n^2)-t^2$ | Notation | Same as row 28. |
| 31 | 280 | 698 | Def 13 | DISCR-DEF | timelike/lightlike/spacelike classification of $\mathbf p=(t,\mathbf x)$ | Standard | Standard SR classification, discretised. |
| 32 | 283 | 711 | (19) | DISCR-DEF | cases: $\lVert\mathbf p\rVert<0$ timelike, $=0$ lightlike, $>0$ spacelike | Standard | |
| 33 | 292 | 722 | Def 14 | DISCR-DEF | timelike/lightlike/spacelike-separated pairs $(\mathbf p,\mathbf q)$ | Standard | |
| 34 | 295 | 735 | (20) | DISCR-DEF | cases for pair $(\mathbf p,\mathbf q)$ | Standard | |
| 35 | 317 | 786 | Def 15 | DISCR-DEF | "discrete spacetime" $(\mathcal M, g)$: $\mathcal M$ a discrete metric space; $g$ a "discrete Lorentzian metric" of signature $(-+++)$ | Undefined | Def 15 introduces $g$ without a construction from the hypergraph or the causal graph. See close reading §2.3 and F1 in `MAJOR_FLAWS.md`. |
| 36 | 322 | 805 | Def 16 | DISCR-DEF | "discrete Cauchy surface" $\Sigma\subset\mathcal M$ | Undefined | Uses the Lorentzian structure of Def 15. |
| 37 | 325 | 809 | (21) | DISCR-DEF | $\Sigma\subset\mathcal M$ | Undefined | Uses the Lorentzian structure of Def 15. |
| 38 | 333 | 824 | (22) | DISCR-ASSERT | $\exists t:\mathcal M\to\mathbb Z$ (time function) | Hypothesis | Existence of a time function, stated as a hypothesis. |
| 39 | 338 | 831 | (23) | DISCR-ASSERT | $\boldsymbol\Delta t\neq 0$ everywhere | Undefined | G1 does not define a gradient on a discrete metric space. |
| 40 | 343 | 842 | (24) | DISCR-ASSERT | foliation condition on $\{\Sigma_t\}$ | Undefined | Uses $g$ of Def 15. |
| 41 | 349 | 851 | (25) | BRIDGE | $\Delta l^2=\gamma_{ij}\Delta x^i \Delta x^j$ | Undefined | G1 identifies $\gamma_{ij}$ with a discrete spatial metric in words and gives no construction. |
| 42 | 354 | 864 | (26) | BRIDGE | $\Delta\tau=\alpha\Delta t$ | Undefined | G1 identifies the lapse $\alpha$ with an effective number of updating events in words. |
| 43 | 359 | 877 | (27) | BRIDGE | $x^i(t+\Delta t)=x^i(t)-\beta^i\Delta t$ | Undefined | G1 identifies the shift $\beta^i$ with an effective graph distance in words. |
| 44 | 364 | 886 | (28) | BRIDGE | $\Delta s^2=(-\alpha^2+\beta^i\beta_i)\Delta t^2+2\beta_i\Delta x^i\Delta t+\gamma_{ij}\Delta x^i\Delta x^j$ | Undefined | The ADM line element (Arnowitt, Deser, Misner 1959). G1 constructs none of $\alpha$, $\beta^i$, $\gamma_{ij}$ from the hypergraph. See close reading §2.3. |
| 45 | 372 | 910 | Def 17 | DISCR-DEF | chronological precedence $x\ll y$ | Standard | Order-theoretic carry-over of the Lorentzian causal structure. |
| 46 | 376 | 917 | Def 18 | DISCR-DEF | strict causal precedence $x<y$ | Standard | |
| 47 | 380 | 924 | Def 19 | DISCR-DEF | causal precedence $x\prec y$ | Standard | |
| 48 | 385 | 933 | (29) | STD | $x\ll y, y\ll z\Rightarrow x\ll z$; $x\prec y, y\prec z\Rightarrow x\prec z$ | Standard | Transitivity of reachability. |
| 49 | 392 | 941 | Def 20 | DISCR-DEF | chronological future/past $I^\pm(x)$ | Standard | Penrose; Hawking and Ellis. |
| 50 | 395 | 949 | (30) | DISCR-DEF | $I^+(x)=\{y\in\mathcal M:x\ll y\}$, etc. | Standard | |
| 51 | 400 | 952 | Def 21 | DISCR-DEF | causal future/past $J^\pm(x)$ | Standard | |
| 52 | 403 | 958 | (31) | DISCR-DEF | $J^+(x)=\{y:x\prec y\})$ — stray close-paren in TeX | Notation | TeX line 404 has an unmatched `)`. The content is standard. |
| 53 | 409 | 973 | (32) | DISCR-DEF | $I^\pm(S)=\bigcup_{x\in S}I^\pm(x)$ etc. | Standard | |
| 54 | 414 | 984 | (33) | STD | $I^+(S)=I^+(I^+(S))\subset J^+(S)=J^+(J^+(S))$ | Standard | Standard Hawking-Ellis §6.2. |
| 55 | 419 | 993 | (34) | STD | $I^-(S)=I^-(I^-(S))\subset J^-(S)=I^-(I^-(S))$ | Notation | TeX line 420 reads $J^-(S)=I^-(I^-(S))$. Hawking and Ellis have $J^-(S)=J^-(J^-(S))$. |
| 56 | 426 | 1005 | Def 22 | DISCR-DEF | discrete future Cauchy development $D^+(S)$ | Standard | Hawking and Ellis. |
| 57 | 430 | 1014 | Def 23 | DISCR-DEF | discrete Cauchy development $D(S)$ | Standard | |
| 58 | 433 | 1020 | (35) | DISCR-DEF | $D(S)=D^+(S)\cup D^-(S)$ | Standard | |
| 59 | 438 | 1023 | Def 24 | DISCR-DEF | achronal set $S\subset\mathcal M$ | Standard | |
| 60 | 441 | 1029 | (36) | DISCR-DEF | $\nexists q,r\in S: r\in I^+(q)$ | Standard | |
| 61 | 446 | 1032 | Def 25 | DISCR-DEF | "discrete Cauchy surface" = achronal set whose Cauchy development is $\mathcal M$ | Standard | Def 16 (TeX line 322) restated in terms of achronal sets. |
| 62 | 451 | 1051 | (37) | STD | $\hat g=\Omega^2 g$ (conformal transformation) | Standard | |
| 63 | 456 | 1060 | (38) | STD | conformal-invariance of sign of $g(X,X)$ | Standard | |
| 64 | 460 (text) | 1063-1077 | — | CONCL | Claim: causal invariance ⇔ discrete general covariance | By definition | Lines 1063-1077 identify causal invariance with a discretised principle of general covariance. Both describe independence of the causal graph from the updating order. Lean: none. See close reading §2.3. |
| 65 | 462 (text) | 1079-1089 | — | CONCL | Claim: flat-hypersurface foliation ⇒ Lorentz covariance; constancy of $c$ axiomatic | By definition | Lines 1079-1089 derive discrete Lorentz covariance for flat foliations and state that constancy of the speed of light "is enforced axiomatically by our definition of the edge lengths in causal graphs". See close reading §2.3. |
| 66 | 466 | 1115 | (39) | STD | Malament-Hogarth spacetime $\exists\gamma_1\subset\mathcal M,\ p\in\mathcal M:\int_{\gamma_1}d\tau=\infty,\gamma_1\subset I^-(p)$ | Standard | Standard Hogarth/Welch definition. |

## §2.4 — Discrete Lorentz transformations

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 67 | 478 | 1157 | (40) | DISCR-DEF | $\mathbf v=(\tanh\rho)\mathbf u$ | Notation | $\mathbf v\in\mathbb Z^n$ while $\tanh\rho$ is in general irrational, so integer coordinates are not preserved. |
| 68 | 483 | 1167 | (41) | DISCR-DEF | $\tanh\rho=\lVert\mathbf v\rVert/\lVert\mathbf u\rVert<1$ | Notation | Same as row 67. |
| 69 | 488 | 1176 | (42) | STD | $t=t'=0$ (synchronisation convention) | Standard | Synchronisation convention. |
| 70 | 493 | 1181 | Def 26 | DISCR-DEF | "discrete Lorentz transformation" | No proof | Applies the continuum Lorentz transformation to integer coordinates. G1 gives no closure under composition and no limit theorem. See close reading §2.4. |
| 71 | 496 | 1187 | (43) | DISCR-DEF | $t' = (\cosh\rho)t-(\sinh\rho)\mathbf x\cdot\mathbf u$ | Notation | Gives the time component only. |
| 72 | 552 | 1290 | Def 27 | DEF | "subdivision" of an undirected graph $G=(V,E)$ | Standard | Standard graph theory. |
| 73 | 556 | 1296 | Def 28 | DEF | "subdivision" of an edge $e\in E$ | Standard | |
| 74 | 573 | 1345 | (44) | STD | $(\lambda x.M[x])\to(\lambda y.M[y])$ (α-conversion) | Standard | Standard λ-calculus. |
| 75 | 578 | 1364 | (45) | STD | $K=\lambda x.\lambda y.x$; $S=\lambda x.\lambda y.\lambda z.xz(yz)$ | Standard | Standard combinatory logic. |
| 76 | 583 | 1371 | (46) | STD | de Bruijn indices: $\lambda\lambda 2$; $\lambda\lambda\lambda 3\,1(2\,1)$ | Standard | Standard de Bruijn 1972. |

## §3.1 — Discrete Ricci scalar via Ollivier-Ricci

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 77 | 599 | 1446 | (47) | STD | $\mathrm{Vol}(B_\epsilon(p))/\mathrm{Vol}(B_\epsilon(0))=1-\frac{R}{6(n+2)}\epsilon^2 + O(\epsilon^4)$ | Standard | Riemannian ball-volume expansion (Gray 1973). |
| 78 | 604 | 1468 | (48) | STD | transported-ball-average-distance $\delta(1-\frac{\epsilon^2}{2(n+2)}R + O(\epsilon^3+\epsilon^2\delta))$ | Differs from source | G1 has the scalar curvature $R$. Ollivier (2009, Example 7), which G1 cites as [42], has $\delta(1-\frac{\epsilon^2}{2(n+2)}\mathrm{Ric}(v,v)+\dots)$, with $\mathrm{Ric}(v,v)$ the Ricci curvature in the direction $v$ from $p$ to $q$. The two agree when $R=\mathrm{Ric}(v,v)$ (PROVED as an arithmetic comparison: `Infra.ollivier_gorard_agree_iff`). G3 eq. 344 has the same formula (`results/phase2_continuum/eq344_verdict.md`). |
| 79 | 611 | 1487 | Def 29 | DEF | "random walk" $m=\{m_x:x\in X\}$ on Polish $(X,d)$ | Standard | Ollivier (2009) §1. |
| 80 | 614 | 1493 | (49) | STD | $m=\{m_x:x\in X\}$ | Standard | Definitional. |
| 81 | 620 | 1499 | Def 30 | DEF | "1-Wasserstein distance" $W_1(m_x,m_y)$ | Standard | Villani (2003). |
| 82 | 623 | 1504 | (50) | STD | $W_1(m_x,m_y)=\inf_{\epsilon\in\Pi(m_x,m_y)}\int d(x,y)d\epsilon(x,y)$ | Notation | $\epsilon$ denotes the coupling here and the ball radius in eq. 48. Standard Kantorovich formulation. |
| 83 | 630 | 1521 | Def 31 | DEF | Ollivier-Ricci scalar curvature $\kappa(p,q)=1-W_1(m_p,m_q)/d(p,q)$ | Standard | Ollivier (2009), Definition 3. |
| 84 | 633 | 1527 | (51) | STD | $\kappa(p,q)=1-W_1(m_p,m_q)/d(p,q)$ | Standard | Ollivier (2009). |
| 85 | 637 (text) | 1530-1538 | — | BRIDGE | Claim: "on a Riemannian manifold with standard volume measure, $\kappa(p,q)$ reduces (up to a scaling factor) to the standard Riemannian Ricci scalar curvature $R(p,q)$" | Differs from source | Lines 1530-1534 state that $\kappa(p,q)$ reduces "(up to some arbitrary scaling factor)" to "the standard Riemannian Ricci scalar curvature $R(p,q)$". Ollivier (2009, Example 7) gives $\kappa\approx\frac{\epsilon^2}{2(n+2)}\mathrm{Ric}(v,v)$ for the direction $v$ from $p$ to $q$. See close reading §3.1. |
| 86 | 641 | 1546 | Def 32 | DEF | "discrete 1-Wasserstein distance" on discrete metric space | Standard | Monge-Kantorovich problem on a discrete space. |
| 87 | 644 | 1556 | (52) | STD | $W_1(m_x,m_y)=\inf_{\mu}\sum d(x',y')\mu(x',y')$ | Standard | |
| 88 | 649 | 1565 | (53) | STD | $\sum_{y'}\mu(x',y')=m_x(x')$ | Standard | Marginal constraint. |
| 89 | 654 | 1572 | (54) | STD | $\sum_{x'}\mu(x',y')=m_y(y')$ | Standard | Marginal constraint. |
| 90 | 661 | 1592 | Def 33 | DISCR-DEF | Ollivier-Ricci scalar curvature $\kappa(e)$ of a directed hyperedge $e: A\to B$ | No proof | Defines $\kappa(e)$ for a directed hyperedge from the measures of eqs. 57-59. G1 gives no theorem relating $\kappa(e)$ to the Ricci curvature of a manifold. See close reading §3.1. |
| 91 | 664 | 1598 | (55) | DISCR-DEF | $A=\{x_1,\dots,x_n\}\to^e B=\{y_1,\dots,y_m\}$ | Notation | Directed hyperedge notation. |
| 92 | 669 | 1605 | (56) | DISCR-DEF | $\kappa(e)=1-W(\mu_{A^{in}},\mu_{B^{out}})$ | Notation | Eq. 56 has no division by a distance, which eq. 51 has. |
| 93 | 674 | 1617 | (57) | DISCR-DEF | $\mu_{A^{in}}=\sum_i \mu_{x_i}$, $\mu_{B^{out}}=\sum_j \mu_{y_j}$ | Definition | Each $\mu_{x_i}$ of eq. 58 carries a factor $1/n$, so $\mu_{A^{in}}$ has total mass 1. The same holds for $\mu_{B^{out}}$ with $1/m$. |
| 94 | 679 | 1636 | (58) | DISCR-DEF | $\mu_{x_i}(z)$ piecewise definition using $d_{x_i^{in}}$ | Definition | Combinatorial rule. $d_{x_i^{in}}$ is the in-degree of $x_i$. |
| 95 | 689 | 1673 | (59) | DISCR-DEF | $\mu_{y_j}(z)$ piecewise definition using $d_{y_j^{out}}$ | Definition | Same form as eq. 58, with out-degrees. |
| 96 | 699 | 1692 | Def 34 | DEF | discrete 1-Wasserstein distance between $\mu_{A^{in}}, \mu_{B^{out}}$ on a directed hypergraph | Definition | Def 32 applied to $\mu_{A^{in}}$ and $\mu_{B^{out}}$. |
| 97 | 702 | 1700 | (60) | DISCR-DEF | $W(\mu_{A^{in}},\mu_{B^{out}})=\min\sum_{u\to A}\sum_{B\to v}d(u,v)\epsilon(u,v)$ | Notation | $\epsilon$ denotes the coupling and $d$ the graph distance. |
| 98 | 707 | 1714 | (61) | DISCR-DEF | $\sum_{u\to A}\epsilon(u,v)=\sum_{j=1}^m \mu_{y_j}(v)$ | Definition | Marginal constraint. |
| 99 | 712 | 1726 | (62) | DISCR-DEF | $\sum_{B\to v}\epsilon(u,v)=\sum_{i=1}^n \mu_{x_I}(u)$ | Notation | TeX line 713 has $\mu_{x_I}$. The index is $i$. |
| 100 | 719 | 1739 | (63) | DISCR-ASSERT | $N(r)=ar^n$, $a\in\mathbb Z$ for a "flat" spatial hypergraph | Notation | G1 states $N(r)=ar^n$ with $a\in\mathbb Z$ as an equality. In $\mathbb Z^2$ with graph distance $N(r)=2r^2+2r+1$, so the equality holds for the leading term only. |
| 101 | 742 | 1787 | (64) | BRIDGE | $\mathrm{Vol}(B_r(p)\in\mathcal M)/\mathrm{Vol}(B_r(0)\in\mathbb Z^n)=1-\frac{R}{6(n+2)}r^2+O(r^4)$, "with exactness when $r=1$" | No proof | Eq. 64 is eq. 47 with $\epsilon$ replaced by $r$. G1 applies it to a hypergraph ball and states that it holds "with exactness when r = 1" (line 1790). Eq. 47 is an expansion as $\epsilon\to 0$. G1 gives no derivation for hypergraphs. |
| 102 | 747 | 1798 | (65) | BRIDGE | $N(r)=ar^n(1-\frac{R}{6(n+2)}r^2+O(r^4))$ | No proof | G1 obtains the correction factor from eq. 64 (lines 1772-1803) and gives no derivation for hypergraph vertex counts. |

## §3.2 — Parallel transport, discrete holonomy, discrete spacetime Ricci

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 103 | 757 | 1823 | (66) | STD | $R=\mathrm{Tr}(R_{ab})=g^{ab}R_{ab}=R_a^{\,a}$ | Standard | Standard Riemannian trace. |
| 104 | 764 | 1847 | (67) | STD | $R_{ab}=R^c_{\ acb}$ | Standard | Standard Ricci=contraction of Riemann. |
| 105 | 769 | 1858 | (68) | STD | $\delta v^\alpha = R^\alpha_{\ \beta\gamma\delta}dx^\gamma dx^\delta v^\beta$ | Notation | TeX line 770 writes $R_{\beta\gamma\delta}^{\alpha}$. Standard holonomy formula. |
| 106 | 774 | 1873 | (69) | STD | $[\nabla_c,\nabla_d]v^a = R^a_{\ bcd}v^b$ | Standard | Standard commutator of covariant derivatives. |
| 107 | 781 | 1896 | (70) | STD | $\Gamma^\rho_{\mu\nu}=\frac12 g^{\rho\sigma}(\partial_\mu g_{\sigma\nu}+\partial_\nu g_{\mu\sigma}-\partial_\sigma g_{\mu\nu})$ | Standard | Standard Christoffel symbols (MTW §8.5). |
| 108 | 786 | 1907 | (71) | STD | $R^a_{\ bcd}=\partial_c\Gamma^a_{bd}-\partial_d\Gamma^a_{bc}+\Gamma^a_{ec}\Gamma^e_{bd}-\Gamma^a_{ed}\Gamma^e_{bc}$ | Standard | Standard Riemann tensor in Levi-Civita. |
| 109 | 791 | 1918 | (72) | STD | $R_{\alpha\beta\gamma\delta}=\frac12(\partial_\beta\partial_\gamma g_{\alpha\delta}-\dots)$ in locally flat coords | Standard | Standard (MTW §8.7). |
| 110 | 797 | 1933 | (73) | STD | $g_{ij}=\delta_{ij}+O(\|\mathbf x\|^2)$ in geodesic normal coordinates | Standard | |
| 111 | 802 | 1948 | (74) | STD | $g_{ij}=\delta_{ij}-\frac13 R_{ijkl}x^k x^l+O(\|\mathbf x\|^3)$ | Standard | Standard Riemann normal coordinates expansion. |
| 112 | 807 | 1955 | (75) | STD | $\mathbf J(t)=(\partial\boldsymbol\gamma_\tau/\partial\tau)_{\tau=0}$ (Jacobi field) | Standard | |
| 113 | 812 | 1969 | (76) | STD | $d\mu_g = (1-\frac16 R_{jk}x^j x^k + O(\|\mathbf x\|^3))d\mu_{Eucl}$ | Standard | Standard Riemannian volume element expansion (Gray 1973/2004, Thm 3.1). |
| 114 | 819 | 1994 | (77) | STD | $K(\mathbf u,\mathbf v)=\langle R(\mathbf u,\mathbf v)\mathbf v,\mathbf u\rangle/(\|\mathbf u\|^2\|\mathbf v\|^2 - \langle\mathbf u,\mathbf v\rangle^2)$ | Standard | Standard sectional curvature. |
| 115 | 824 | 2007 | (78) | STD | $K(\mathbf u,\mathbf v)=\langle R(\mathbf u,\mathbf v)\mathbf v,\mathbf u\rangle$ for orthonormal $\mathbf u,\mathbf v$ | Standard | |
| 116 | 830 | 2025 | (79) | STD | $d(\exp_x(\epsilon \mathbf w_x),\exp_y(\epsilon\mathbf w_y))=\delta(1-\frac{\epsilon^2}{2}K(\mathbf v,\mathbf w)+O(\epsilon^3+\epsilon^2\delta))$ | Standard | Ollivier (2009) §5.1. |
| 117 | 835 | 2054 | (80) | STD | $\delta(1-\frac{\epsilon^2}{2(n+2)}R+O(\epsilon^3+\epsilon^2\delta))$ — average of sectional curvature | Differs from source | Same formula as eq. 48: line 2057 states that $R$ is "the Ollivier-Ricci scalar curvature", where Ollivier (2009) has $\mathrm{Ric}(v,v)$. See row 78. |
| 118 | 840 (text) | 2059-2069 | — | DISCR-ASSERT | Assertion: in a directed hypergraph, set $\epsilon=\delta=1$, all non-parallel hyperedges are "orthonormal" | Undefined | Lines 2059-2065 set $\epsilon=\delta=1$ and assume that non-parallel hyperedges "can be considered to be orthonormal". G1 defines no bilinear form on hyperedges (F2 in `MAJOR_FLAWS.md`). Eqs. 47-80 are expansions as $\epsilon,\delta\to 0$. See close reading §3.2. |
| 119 | 842 | 2077 | (81) | BRIDGE | $K(\mathbf u,\mathbf v)=\langle R(\mathbf u,\mathbf v)\mathbf v,\mathbf u\rangle$ (repeat of Eq 78) | Undefined | Eq. 78 restated as a definition for hypergraphs under the assumptions of lines 2059-2065. |
| 120 | 851 | 2104 | (82) | BRIDGE | $C(t)=at^n$, $a\in\mathbb Z$ | Undefined | Same form as eq. 63 (lines 2098-2104). G1 does not define a flat causal graph. For the rule of G3 line 6202 the cone-growth exponent is MEASURED between 0.77 and 1.26, depending on the update order (`notes/empirical_refutation.md`). Linear cone growth is OPEN (`CausalHistory.GorardNamedRuleConeGrowthLinear`). |
| 121 | 865 | 2131 | (83) | STD | $d\mu_g = (1-\frac16 R_{jk}x^j x^k + O(\|\mathbf x\|^3))d\mu_{Eucl}$ | Standard | Repeat of Eq 76. |
| 122 | 870 | 2140 | (84) | BRIDGE | $C(t)=at^n[1-\frac16 R_{jk}t^j t^k + O(\|\mathbf t\|^3)]$ | No proof | Obtained from eq. 83 "by analogy to the purely spatial case" (lines 2109-2145). G1 gives no derivation for causal graphs. For the rule of G3 line 6202 the cone-growth exponent is MEASURED between 0.77 and 1.26, depending on the update order (`notes/empirical_refutation.md`). Linear cone growth is OPEN (`CausalHistory.GorardNamedRuleConeGrowthLinear`). |
| 123 | 875 | 2153 | (85) | BRIDGE | $t^a=\alpha n^a + \beta^a$ | Undefined | Uses $\alpha$, $n^a$, $\beta^a$ of eqs. 25-28. |

## §3.3 — Discrete Einstein field equations

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 124 | 885 (text) | 2170-2182 | — | DISCR-ASSERT | Assumption: "asymptotic dimensionality preservation" — growth rate of global dimension anomaly → 0 | Hypothesis | Lines 2170-2182 state asymptotic dimensionality preservation as an assumption and give no mode of convergence. |
| 125 | 887 | 2200 | (86) | BRIDGE | $S[g^{ab}]=\sum d\mu_g R$ | Undefined | $d\mu_g$ appears in eq. 76 as the Riemannian volume element. G1 gives no discrete definition of $d\mu_g$ or of $g^{ab}$ (Def 15). |
| 126 | 891 | 2211 | (87) | BRIDGE | $\delta S[g^{ab}]/\delta g^{ab}\to 0$ | Undefined | G1 applies $\delta/\delta g^{ab}$ to the discrete sum of eq. 86 and does not construct $g$ with components that can be varied. Lines 2203-2211 state that asymptotic dimensionality preservation "corresponds to" this condition, which is the Euler-Lagrange equation of $S$. Lean: none. See close reading §3.3. |
| 127 | 897 | 2225 | (88) | BRIDGE | $S[g^{ab}]=\int d^4 x \sqrt{-g}R$ (in continuum limit) | No proof | Line 2214 states that the sum "becomes" the integral "subject to a weak ergodicity assumption". G1 states no notion of convergence and does not define weak ergodicity. |
| 128 | 902 | 2239 | (89) | STD | $\mathcal L_G = \sqrt{-g}R$ | Standard | Hilbert (1915). |
| 129 | 907 | 2252 | (90) | STD | $\delta S/\delta g^{ab}=\sqrt{-g}(R_{ab}-\frac12 Rg_{ab})$ | Standard | Hilbert variation with zero surface terms. |
| 130 | 912 | 2259 | (91) | CONCL | $R_{ab}-\frac12 Rg_{ab}=0$ (vacuum EFE) | Standard (continuum) | The continuum vacuum Einstein equations. G1 reaches them from the hypergraph through eqs. 86-88 (rows 125-127). See close reading §3.3. |
| 131 | 919 | 2283 | (92) | STD | $d^2 x^\mu/ds^2 + \Gamma^\mu_{\alpha\beta}(dx^\alpha/ds)(dx^\beta/ds)=0$ | Standard | Standard geodesic equation. |
| 132 | 924 | 2291 | (93) | STD | $S=\int ds$ | Standard | Standard action for a timelike curve. |
| 133 | 929 | 2298 | (94) | STD | $ds=\sqrt{-g_{\mu\nu}dx^\mu dx^\nu}$ | Standard | Standard line element. |
| 134 | 934 | 2308 | (95) | STD | $S=\int\sqrt{-g_{\mu\nu}(dx^\mu/d\lambda)(dx^\nu/d\lambda)}d\lambda$ | Standard | Standard parametrised action. |
| 135 | 948 | 2349 | (96) | STD | $\mathcal L=\mathcal L_G + C_M\mathcal L_M$ | Standard | Standard gravity+matter Lagrangian decomposition. |
| 136 | 953 | 2361 | (97) | CONCL | $R_{ab}-\frac12 Rg_{ab}=8\pi T_{ab}$ | Standard (continuum) | The continuum Einstein equations with matter. G1 gives no matter Lagrangian on the hypergraph. |
| 137 | 958 | 2370 | (98) | STD | $T_{ab}=-\frac{C_M}{8\pi\sqrt{-g}}\partial\mathcal L_M/\partial g^{ab}$ | Standard | Standard Hilbert stress-energy. |
| 138 | 963 | 2377 | (99) | STD | $T_{ab}=-\frac{C_M}{8\pi\sqrt{-g}}\delta S_M/\delta g^{ab}$ | Standard | Same, action form. |
| 139 | 977 | 2399 | (100) | BRIDGE | $S[g^{ab}]=\sum d\mu_g(R+2\Lambda)$ | Undefined | Eq. 86 with $2\Lambda$ added. The notes of row 125 apply. |
| 140 | 982 | 2408 | (101) | STD | $\mathcal L_G=\sqrt{-g}(R+2\Lambda)$ | Standard | Standard continuum Lagrangian with $\Lambda$. |
| 141 | 987 | 2416 | (102) | CONCL | $R_{ab}-\frac12 Rg_{ab}+\Lambda g_{ab}=8\pi T_{ab}$ | Standard (continuum) | The continuum Einstein equations with $\Lambda$. G1 adds $2\Lambda$ to the discrete sum in eq. 100 and concludes that the model "is consistent with both zero and non-zero values of the cosmological constant" (line 2419). |
| 142 | 994 | 2451 | (103) | STD | $\partial f/\partial t + \mathbf v\cdot\partial f/\partial\mathbf r + \mathbf F\cdot\partial f/\partial\mathbf v=\hat C f$ (Boltzmann) | Standard | |
| 143 | 999 | 2462 | (104) | STD | same with $\hat C f/\epsilon$ | Standard | Standard Chapman-Enskog ansatz. |
| 144 | 1004 | 2469 | (105) | STD | $f=f^{(0)}+\epsilon f^{(1)}+\epsilon^2 f^{(2)}+\dots$ | Standard | Standard expansion. |
| 145 | 1009 | 2484 | (106) | STD | $f^{(0)}=n'(\mathbf r,t)(m/(2\pi k_B T'))^{3/2}\exp(-m(\mathbf v-\mathbf v_0')^2/(2k_BT'))$ | Standard | Standard Maxwellian. |
| 146 | 1014 | 2495 | (107) | STD | $f^{(1)}=[\dots]f^{(0)}$ (Navier-Stokes closure) | Standard | Standard Chapman-Enskog (Cercignani). |
| 147 | 1019 | 2505 | (108) | STD | $\mathbb T:\mathbb T'=\sum_i\sum_j T_{ij}T'_{ji}$ | Standard | Double-dot product. |
| 148 | 1024 (text) | 2512-2514 | — | CONCL | Claim: derivation of EFE is equivalent to Chapman-Enskog hydro expansion with $C(t)$ as distribution function | No proof | Lines 2512-2514 state that the derivation is "essentially equivalent" to a Chapman-Enskog expansion with $C(t)$ as the distribution function. G1 gives no map between the Boltzmann equation and the causal-graph dynamics. |
| 149 | 1026 | 2521 | (109) | BRIDGE | $C(t)=at^n[1-\frac16 R_{jk}t^j t^k + O(\|\mathbf t\|^3)]$ | No proof | Eq. 84 repeated (row 122). |
| 150 | 1033 | 2554 | (110) | STD | Lovelock equations (first block) — $\alpha(-\frac12 R_{\rho\sigma}R^{\rho\sigma}g_{\mu\nu}-\dots)$ | Notation | TeX line 1034 has `g_{\mu nu}` and the product $\square R\,\square R_{\mu\nu}$. Lovelock (1971). |
| 151 | 1040 | 2558 | (111) | STD | $\kappa^2=32\pi G$ | Standard | |
| 152 | 1045 | 2562 | (112) | STD | Weyl tensor $C_{iklm}=R_{iklm}+\frac{1}{n-2}(\dots)+\frac{1}{(n-1)(n-2)}R(\dots)$ | Standard | Standard (Hawking-Ellis §2.6; Danehkar). |

## §3.4 — Topology, variable dimensionality, cosmology

| # | TeX line | Text line | Eqn # | Type | Statement | Reading | Note |
|---|---|---|---|---|---|---|---|
| 153 | 1056 | 2569 | (113) | BRIDGE | $N(r)=ar^n(1-\frac{R}{6(n+2)}r^2+O(r^4))$ | No proof | Eq. 65 repeated (row 102). |
| 154 | 1061 | 2583 | (114) | BRIDGE | $C(t)=at^n[1-\frac16 R_{jk}t^j t^k+O(\|\mathbf t\|^3)]$ | No proof | Eq. 84 repeated (row 122). |
| 155 | 1066 | 2586 | (115) | STD | $\forall x\in\mathcal M,\exists U: f \text{ constant on }U$ | Standard | Standard locally-constant dim property of a manifold (Lee, *Smooth Manifolds*). |
| 156 | 1075 | 2622 | (116) | STD | $\varphi:(U\subset\mathcal M)\to(\varphi(U)\subset\mathbb R^n)$ (chart) | Standard | |
| 157 | 1080 | 2630 | (117) | STD | atlas $A=\{(U_\alpha,\varphi_\alpha):\alpha\in I\}$ | Standard | |
| 158 | 1085 | 2647 | (118) | STD | $\bigcup_\alpha U_\alpha=\mathcal M$ | Standard | |
| 159 | 1090 | 2678 | (119) | STD | $p:C\to X$ (covering map) | Standard | Standard algebraic topology. |
| 160 | 1099 | 2687 | (120) | STD | $V(\Gamma)=\{g:g\in G\}$ (Cayley graph vertices) | Standard | |
| 161 | 1104 | 2694 | (121) | STD | $E(\Gamma)=\{(g,gs):g\in G,s\in S\}$ | Standard | |
| 162 | 1109 | 2703 | (122) | STD | $N_k=z(z-1)^{k-1}$, $k>0$ (Bethe lattice shells) | Standard | Standard (Bethe 1935). |
| 163 | 1120 | 2750 | (123) | STD | $c(t)=\hat c\chi(t)$ | Standard | Standard VSL parametrisation. |
| 164 | 1125 | 2757 | (124) | STD | $c(t)=c_0\theta(t_c-t)+c_m\theta(t-t_c)$ | Standard | Standard VSL. |
| 165 | 1130 | 2770 | (125) | STD | $\theta(t)=\{1\text{ if }t>0, 0\text{ if }t\le 0\}$ | Standard | Heaviside. |
| 166 | 1138 | 2837 | (126) | STD | FLRW line element with $c(t)$ | Notation | TeX line 1139 has $\sin\theta\,d\phi^2$. The FLRW metric has $\sin^2\theta\,d\phi^2$, as in eqs. 128-129. |
| 167 | 1143 | 2846 | (127) | STD | $g_{\mu\nu}=g_{0\mu\nu}+g_{m\mu\nu}$ (bimetric) | Standard | Standard VSL. |
| 168 | 1148 | 2858 | (128) | STD | $ds_0^2 = dt^2 c_0^2\theta(t_c-t) - a^2(t)[\dots]$ | Standard | |
| 169 | 1153 | 2875 | (129) | STD | $ds_m^2 = dt^2 c_m^2\theta(t-t_c) - a^2(t)[\dots]$ | Standard | |
| 170 | 1158 | 2882 | (130) | STD | $\gamma=c_0/c_m$ | Standard | Standard dimensionless ratio. |
| 171 | 1165 | 2893 | (131) | STD | $d_H(t)=a(t)\int_0^t c(t')/a(t')\,dt'$ | Standard | Standard proper horizon. |
| 172 | 1170 | 2904 | (132) | STD | $dt'=a(t)dt$ (diffeomorphism) | Notation | G1 calls the substitution $dt'=a(t)dt$ a diffeomorphism (TeX line 1170). |
| 173 | 1177 | 2911 | (133) | STD | $H^2+c^2k/a^2=8\pi G\rho/3 + c^2\Lambda/3$ (Friedmann) | Standard | |
| 174 | 1182 | 2922 | (134) | STD | $H(t)=\dot a/a$ | Standard | |
| 175 | 1187 | 2929 | (135) | STD | $\epsilon(t)=|\Omega(t)-1|=c^2|k|/\dot a^2$ | Standard | Standard flatness param. |
| 176 | 1192 | 2947 | (136) | STD | $\Omega(t)=8\pi G\rho/(3H^2)$ | Standard | Standard density param. |
| 177 | 1197 | 2954 | (137) | STD | $\dot\epsilon(t)=-2c^2|k|\ddot a/\dot a^3 + 2(\dot c/c)(c^2|k|/\dot a^2)$ | Standard | Standard, derivable from Eqs 135-136. |
| 178 | 1204 | 2961 | (138) | STD | FLRW line element in $n$ spatial dims | Standard | Standard (Tangherlini 1963). |
| 179 | 1209 | 2968 | (139) | STD | $r^2=\sum_i(x_i)^2$ | Standard | |
| 180 | 1214 | 2977 | (140) | STD | $\dot\rho + n(\rho+p)\dot a/a=0$ ($n$-D energy conservation) | Standard | Standard (Tangherlini / Lima). |
| 181 | 1219 | 2999 | (141) | STD | $\frac{n(n-1)}{2}[\dot a^2/a^2+k/a^2]=8\pi G_n\rho$ | Standard | Standard $n$-D Friedmann. |
| 182 | 1224 | 3006 | (142) | STD | $\frac{(n-1)\ddot a}{a}+\frac{(n-1)(n-2)}{2}[\dot a^2/a^2+k/a^2]=-8\pi G_n p$ | Standard | Standard $n$-D acceleration eqn. |
| 183 | 1229 | 3017 | (143) | STD | $p=\omega_n\rho$ | Standard | Standard $n$-D equation of state. |
| 184 | 1234 | 3028 | (144) | STD | $a(t) = [\dots]$ (Holanda–Pereira closed form) | Standard | Holanda and Pereira. |


---

## Summary by section

| Section | Reading |
|---|---|
| §2.1 Basic formalism | Defs 3-4 use "outgoing hyperedges" and "only applicable as a result of", which Def 1 and Def 4 do not define. |
| §2.2 Abstract rewriting | Standard abstract rewriting material (Baader and Nipkow). Def 9 does not state when "eventually" holds. |
| §2.3 Causal graph hypersurfaces and ADM | Defs 17-25 and eqs. 29-38 carry over the Penrose and Hawking-Ellis causal structure. Eqs. 25-28 identify the ADM quantities in words. Lines 1063-1089 identify causal invariance with general covariance and state that the speed of light is fixed by the definition of edge lengths. |
| §2.4 Discrete Lorentz transformations | Def 26 and eq. 43 apply the continuum Lorentz transformation to integer coordinates with no closure or limit theorem. |
| §3.1 Ollivier-Ricci curvature on hypergraphs | Eq. 48 and lines 1530-1534 have the scalar curvature $R$ where Ollivier (2009) has $\mathrm{Ric}(v,v)$. Def 33 and eqs. 56-65 give no theorem relating the hypergraph quantity to manifold curvature. |
| §3.2 Parallel transport and curvature | Eqs. 66-79 are standard Riemannian geometry. Eq. 80 has $R$ where Ollivier (2009) has $\mathrm{Ric}(v,v)$. Lines 2059-2065 set $\epsilon=\delta=1$ and assume orthonormality of non-parallel hyperedges without a bilinear form. Eq. 84 is obtained from eq. 83 by analogy. |
| §3.3 Discrete Einstein field equations | Eqs. 91, 97 and 102 are the continuum Einstein equations. G1 reaches them through eqs. 86-88, which use a metric and measure that are not constructed, a variation that is not defined for a discrete sum, and a passage from sum to integral with no stated notion of convergence. |
| §3.4 Variable dimension and cosmology | Eqs. 113-144 are standard continuum cosmology (variable speed of light, $n$-dimensional FLRW, Holanda and Pereira). |

## Steps of the §3.3 derivation

| Step | Eqn # | Reading |
|---|---|---|
| The Ollivier-Ricci quantity on a hypergraph corresponds to the scalar curvature $R$ | (48), (80), lines 1530-1534 | Differs from source: Ollivier (2009) has $\mathrm{Ric}(v,v)$ (`results/phase2_continuum/eq344_verdict.md`) |
| Hypergraph ball counts satisfy $N(r)=ar^n(1-Rr^2/(6(n+2))+\dots)$ | (65) | No proof for hypergraphs |
| Non-parallel hyperedges are orthonormal | lines 2063-2065 | Undefined: no bilinear form |
| $\epsilon=\delta=1$ in expansions valid as $\epsilon,\delta\to 0$ | lines 2059-2061 | Hypothesis, with no error bound |
| Causal-graph cone counts satisfy $C(t)=at^n[1-\frac16 R_{jk}t^jt^k+\dots]$ | (84) | No proof for causal graphs |
| The discrete sum becomes the Einstein-Hilbert integral | (88) | No proof; no notion of convergence |
| Variation $\delta S/\delta g^{ab}\to 0$ | (87) | Undefined: $g$ is not constructed; equals the Euler-Lagrange equation of $S$ |

Each step is OPEN as a mathematical statement. Eq. 91, the vacuum Einstein equation, follows from eqs. 89-90 in the continuum.

## Equations that can be formalised as stated

These equations are continuum or order-theoretic statements with no passage from discrete to continuum:

- §2.2 Abstract rewriting: eqs. 2-14. Mathlib has the corresponding definitions of rewriting, confluence and Church-Rosser.
- §2.3 Causal structure on a partial order: Defs 17-25, eqs. 29-36 and 39. These are order-theoretic.
- §3.1 Ollivier-Ricci curvature on metric measure spaces: Defs 29-32, eqs. 49-54.
- §3.2 Riemannian geometry: eqs. 66-79.
- §3.3 Einstein-Hilbert variation: eqs. 89-95, 98, 99, 101. Mathlib has no general relativity library.
- §3.4 Cosmology: eqs. 113-144.

Eqs. 25-28, 43, 48, 55-65, 80-88 and 109 use objects that G1 does not construct or formulas that differ from the cited source. A formal statement of them needs a definition of each object first.

## Relation to the Lean programme

The five statements listed at the end of `notes/2004.14810_close_reading.md` (a discrete Lorentzian metric-measure structure, a discrete Ollivier-Ricci tensor with a convergence theorem, a discrete Einstein-Hilbert functional with a convergence theorem, a discrete variation, and the vacuum Einstein theorem) correspond to the rows of this catalog marked Undefined, No proof and Differs from source. All five are OPEN.
