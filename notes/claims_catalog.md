# Claims catalog — arXiv:2004.14810 "Some Relativistic and Gravitational Properties of the Wolfram Model"

Equation-by-equation + definition-by-definition catalog, covering every `\begin{equation}`, `\begin{align}` and `\begin{definition}` block in the TeX source `papers/tex_2004/RelativityAndGravitation.tex` (1505 lines).

**Type legend.**
- `DEF` – labelled `\begin{definition}` block (no equation number of its own, though may contain numbered equations).
- `STD` – standard continuum result quoted from the literature.
- `CONT-COMP` – continuum computation carried out in-paper.
- `DISCR-DEF` – JGORARD-specific definition for discrete hypergraphs / causal graphs.
- `DISCR-ASSERT` – unproved assertion about a discrete object.
- `BRIDGE` – discrete→continuum correspondence claim.
- `CONCL` – claimed conclusion (never labelled "theorem" but stated as one).

**Status legend.** `✓` verified / standard with correct citation. `✗` refuted (with verdict file). `⚠` ill-defined (requires undefined objects to interpret). `⊘` tautology. `○` open conjecture. `→` pending.

Columns: # | TeX line | Eqn # in paper | Type | Verbatim | Status | Note.

---

## §2.1 — Basic formalism and causal graphs

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 1 | 68 | Def 1 | DEF | "spatial hypergraph" $H=(V,E)$ finite undirected, $E\subseteq \mathcal P(V)\setminus\{\emptyset\}$ | ⚠ | Berge hypergraph; paper later silently switches to *directed* hypergraphs (§3.1) without re-definition. See close-reading §2.1. |
| 2 | 71 | (1) | DEF | $E \subseteq \mathcal{P}(V)\setminus\lbrace\emptyset\rbrace$ | ✓ | Standard hypergraph definition (Berge 1989). |
| 3 | 80 | Def 2 | DEF | "trivalent spatial graph" $G=(V,E)$ finite undirected 3-regular | ✓ | Standard. |
| 4 | 87 | Def 3 | DISCR-DEF | "update rule" $R: H_1\to H_2$ with same number of outgoing hyperedges, preserving symmetries of $H_1$ | ⚠ | "Outgoing" undefined for undirected hypergraph of Def 1; "preserves symmetries" not formalised. First informal-definition hole. |
| 5 | 93 | Def 4 | DISCR-DEF | "causal graph" $G_{causal}$: $A\to B$ iff update rule at $B$ was only applicable as a result of outcome of $A$ | ⚠ | "Applicable as a result of" never precisely defined in terms of consumed/produced hyperedges. |

## §2.2 — Abstract rewriting, Church–Rosser, causal invariance

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 6 | 125 | Def 5 | DEF | "abstract rewriting system" = set $A$ with binary relation $\to$ | ✓ | Baader-Nipkow, standard. |
| 7 | 132 | (2) | STD | $a \to a' \to a'' \to \dots \to b' \to b$ | ✓ | Notation for rewrite sequences. |
| 8 | 137 | Def 6 | DEF | $\to^*$ = reflexive transitive closure of $\to$ | ✓ | Standard. |
| 9 | 142 | (3) | STD | $a\to^* a$; $a\to^* b, b\to^* c \Rightarrow a\to^* c$ | ✓ | Reflexivity + transitivity axioms. |
| 10 | 148 | Def 7 | DEF | Object $a$ is confluent | ✓ | Baader-Nipkow, standard. |
| 11 | 151 | (4) | STD | $\forall b,c\in A, a\to^*b\wedge a\to^*c\Rightarrow \exists d:b\to^*d\wedge c\to^*d$ | ✓ | Standard confluence predicate. |
| 12 | 156 | Def 8 | DEF | ARS $A$ is (globally) confluent / Church-Rosser | ✓ | Church–Rosser 1936. |
| 13 | 170 | Def 9 | DISCR-DEF | "causal invariant" multiway system: all causal graphs eventually isomorphic as DAGs | ⚠ | "Eventually" never precisely quantified. See close-reading §2.2. |
| 14 | 186 | (5) | CONT-COMP | $\to_1 \cup \to_2 \;=\; \to$ | ✓ | Notation for decomposing a rewrite relation. |
| 15 | 191 | (6) | CONT-COMP | $p\mapsto\{(\alpha,q)\in\Lambda\times A:p\to^\alpha q\}$ | ✓ | Coalgebra-style repackaging. |
| 16 | 196 | (7) | STD | $\mathcal P: Set\mapsto Set$ (powerset endofunctor) | ✓ | Category-theory triviality. |
| 17 | 201 | (8) | STD | $\to: A\mapsto \mathcal P A$ | ✓ | Repackaging rewrite relation as a morphism. |
| 18 | 208 | (9) | STD | local-confluence condition | ✓ | Standard weakening. |
| 19 | 213 | (10) | STD | semi-confluence condition | ✓ | Standard. |
| 20 | 218 | (11) | STD | diamond property | ✓ | Standard. |
| 21 | 223 | (12) | STD | strong confluence | ✓ | Standard. |
| 22 | 230 | (13) | STD | $((\lambda x.M)E)\to (M[x:=E])$ ($\beta$-reduction) | ✓ | Standard λ-calculus. |
| 23 | 235 | (14) | STD | joinability $x\downarrow y \iff \exists z: x\to^*z\leftarrow^* y$ | ✓ | Standard. |

## §2.3 — Causal graph hypersurfaces and discrete Lorentz covariance

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 24 | 246 | Def 10 | DEF | "layered graph embedding" of a DAG in the plane with monotonic-downward edges, minimising crossings | ✓ | Di Battista–Tamassia, standard. |
| 25 | 251 | Def 11 | DEF | "downward planar embedding" (no crossings) | ✓ | Standard. |
| 26 | 257 | (15) | STD | $\mathbf p=(t,\mathbf x)$ | ✓ | Coordinate labelling. |
| 27 | 262 | (16) | STD | $\mathbf x=(x_1,\dots,x_n)\in\mathbb Z^n$ | ✓ | Coordinate labelling. |
| 28 | 267 | Def 12 | DISCR-DEF | "discrete Minkowski norm" | ⚠ | Defines a norm-like functional on $\mathbb Z^{1,n}$; not a norm (negative values allowed). Reasonable rename would be "Minkowski pseudo-norm" or just "interval". |
| 29 | 270 | (17) | DISCR-DEF | $\lVert(t,\mathbf x)\rVert=\lVert \mathbf x\rVert^2 - t^2$ | ⚠ | Fine if interpreted as the Minkowski interval; the symbol $\|\cdot\|$ is abused because values can be negative. |
| 30 | 275 | (18) | DISCR-DEF | $\lVert(t,\mathbf x)\rVert=(x_1^2+\dots+x_n^2)-t^2$ | ⚠ | Same as above. |
| 31 | 280 | Def 13 | DISCR-DEF | timelike/lightlike/spacelike classification of $\mathbf p=(t,\mathbf x)$ | ✓ | Standard SR classification, discretised. |
| 32 | 283 | (19) | DISCR-DEF | cases: $\lVert\mathbf p\rVert<0$ timelike, $=0$ lightlike, $>0$ spacelike | ✓ | Standard. |
| 33 | 292 | Def 14 | DISCR-DEF | timelike/lightlike/spacelike-separated pairs $(\mathbf p,\mathbf q)$ | ✓ | Standard. |
| 34 | 295 | (20) | DISCR-DEF | cases for pair $(\mathbf p,\mathbf q)$ | ✓ | Standard. |
| 35 | 317 | Def 15 | DISCR-DEF | "discrete spacetime" $(\mathcal M, g)$: $\mathcal M$ a discrete metric space; $g$ a "discrete Lorentzian metric" of signature $(-+++)$ | ⚠ | $g$ is *declared* not *constructed*. This is the "metric-is-declared" move — see close-reading §2.3. |
| 36 | 322 | Def 16 | DISCR-DEF | "discrete Cauchy surface" $\Sigma\subset\mathcal M$ | ⚠ | Depends on $\mathcal M$'s Lorentzian structure, which is declared not built. |
| 37 | 325 | (21) | DISCR-DEF | $\Sigma\subset\mathcal M$ | ⚠ | See above. |
| 38 | 333 | (22) | DISCR-ASSERT | $\exists t:\mathcal M\to\mathbb Z$ (time function) | ⚠ | Globally-hyperbolic assumption, stated as a hypothesis. |
| 39 | 338 | (23) | DISCR-ASSERT | $\boldsymbol\Delta t\neq 0$ everywhere | ⚠ | Gradient undefined on a generic discrete metric space; "non-zero discrete gradient" not formalised. |
| 40 | 343 | (24) | DISCR-ASSERT | foliation condition on $\{\Sigma_t\}$ | ⚠ | Depends on Def 15's undeclared $g$. |
| 41 | 349 | (25) | BRIDGE | $\Delta l^2=\gamma_{ij}\Delta x^i \Delta x^j$ | ⚠ | $\gamma_{ij}$ "3-dim discrete spatial metric" never constructed. Verbal identification only. |
| 42 | 354 | (26) | BRIDGE | $\Delta\tau=\alpha\Delta t$ | ⚠ | Lapse $\alpha$ identified with "effective number of updating events"; verbal only. |
| 43 | 359 | (27) | BRIDGE | $x^i(t+\Delta t)=x^i(t)-\beta^i\Delta t$ | ⚠ | Shift $\beta^i$ identified with "effective graph distance"; verbal only. |
| 44 | 364 | (28) | BRIDGE | $\Delta s^2=(-\alpha^2+\beta^i\beta_i)\Delta t^2+2\beta_i\Delta x^i\Delta t+\gamma_{ij}\Delta x^i\Delta x^j$ | ⚠ | Standard continuum ADM line element (Arnowitt-Deser-Misner 1959) copied verbatim; $(\alpha,\beta^i,\gamma_{ij})$ none constructed from the hypergraph. See close-reading §2.3. |
| 45 | 372 | Def 17 | DISCR-DEF | chronological precedence $x\ll y$ | ✓ | Standard CG/Lorentz structure carried over combinatorially. |
| 46 | 376 | Def 18 | DISCR-DEF | strict causal precedence $x<y$ | ✓ | Standard. |
| 47 | 380 | Def 19 | DISCR-DEF | causal precedence $x\prec y$ | ✓ | Standard. |
| 48 | 385 | (29) | STD | $x\ll y, y\ll z\Rightarrow x\ll z$; $x\prec y, y\prec z\Rightarrow x\prec z$ | ✓ | Transitivity, immediate from graph reachability. |
| 49 | 392 | Def 20 | DISCR-DEF | chronological future/past $I^\pm(x)$ | ✓ | Direct carry-over from Penrose/Hawking-Ellis. |
| 50 | 395 | (30) | DISCR-DEF | $I^+(x)=\{y\in\mathcal M:x\ll y\}$, etc. | ✓ | Standard. |
| 51 | 400 | Def 21 | DISCR-DEF | causal future/past $J^\pm(x)$ | ✓ | Standard. |
| 52 | 403 | (31) | DISCR-DEF | $J^+(x)=\{y:x\prec y\})$ — stray close-paren in TeX | ✓ | Minor TeX typo (an unmatched `)`); content is standard. |
| 53 | 409 | (32) | DISCR-DEF | $I^\pm(S)=\bigcup_{x\in S}I^\pm(x)$ etc. | ✓ | Standard. |
| 54 | 414 | (33) | STD | $I^+(S)=I^+(I^+(S))\subset J^+(S)=J^+(J^+(S))$ | ✓ | Standard Hawking-Ellis §6.2. |
| 55 | 419 | (34) | STD | $I^-(S)=I^-(I^-(S))\subset J^-(S)=I^-(I^-(S))$ | ⚠ | **TeX typo**: last clause should be $J^-(S)=J^-(J^-(S))$, not $I^-(I^-(S))$. Clear cut-paste error. |
| 56 | 426 | Def 22 | DISCR-DEF | discrete future Cauchy development $D^+(S)$ | ✓ | Standard Hawking-Ellis carryover. |
| 57 | 430 | Def 23 | DISCR-DEF | discrete Cauchy development $D(S)$ | ✓ | Standard. |
| 58 | 433 | (35) | DISCR-DEF | $D(S)=D^+(S)\cup D^-(S)$ | ✓ | Standard. |
| 59 | 438 | Def 24 | DISCR-DEF | achronal set $S\subset\mathcal M$ | ✓ | Standard. |
| 60 | 441 | (36) | DISCR-DEF | $\nexists q,r\in S: r\in I^+(q)$ | ✓ | Standard. |
| 61 | 446 | Def 25 | DISCR-DEF | "discrete Cauchy surface" = achronal set whose Cauchy development is $\mathcal M$ | ✓ | Standard rephrase. (This duplicates Def 16 — Def 16 was sketch, Def 25 is the formal one.) |
| 62 | 451 | (37) | STD | $\hat g=\Omega^2 g$ (conformal transformation) | ✓ | Standard. |
| 63 | 456 | (38) | STD | conformal-invariance of sign of $g(X,X)$ | ✓ | Standard. |
| 64 | 460 (text) | — | CONCL | **Claim: causal invariance ⇔ discrete general covariance** | ⊘ | Tautology: "causal invariance" and "general covariance" are both *defined* as update-order-independence of observable outcomes. See close-reading §2.3. |
| 65 | 462 (text) | — | CONCL | **Claim: flat-hypersurface foliation ⇒ Lorentz covariance; constancy of $c$ axiomatic** | ⊘ | Circular: discrete Minkowski norm (Def 12) hard-codes SR; "derivation" restates axioms. See close-reading §2.3. |
| 66 | 466 | (39) | STD | Malament-Hogarth spacetime $\exists\gamma_1\subset\mathcal M,\ p\in\mathcal M:\int_{\gamma_1}d\tau=\infty,\gamma_1\subset I^-(p)$ | ✓ | Standard Hogarth/Welch definition. |

## §2.4 — Discrete Lorentz transformations

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 67 | 478 | (40) | DISCR-DEF | $\mathbf v=(\tanh\rho)\mathbf u$ | ⚠ | Rapidity parametrisation, but $\mathbf v\in\mathbb Z^n$ and $\tanh\rho$ is generically irrational — the integer-coordinate system is not preserved. |
| 68 | 483 | (41) | DISCR-DEF | $\tanh\rho=\lVert\mathbf v\rVert/\lVert\mathbf u\rVert<1$ | ⚠ | Same issue. |
| 69 | 488 | (42) | STD | $t=t'=0$ (synchronisation convention) | ✓ | Trivial. |
| 70 | 493 | Def 26 | DISCR-DEF | "discrete Lorentz transformation" | ⚠ | Applies continuum formula to integer coords; no proof the resulting set is stable under composition, no limit theorem. See close-reading §2.4. |
| 71 | 496 | (43) | DISCR-DEF | $t' = (\cosh\rho)t-(\sinh\rho)\mathbf x\cdot\mathbf u$ | ⚠ | Same issue; only the time component; the spatial component is not written down. |
| 72 | 552 | Def 27 | DEF | "subdivision" of an undirected graph $G=(V,E)$ | ✓ | Standard graph theory. |
| 73 | 556 | Def 28 | DEF | "subdivision" of an edge $e\in E$ | ✓ | Standard. |
| 74 | 573 | (44) | STD | $(\lambda x.M[x])\to(\lambda y.M[y])$ (α-conversion) | ✓ | Standard λ-calculus. |
| 75 | 578 | (45) | STD | $K=\lambda x.\lambda y.x$; $S=\lambda x.\lambda y.\lambda z.xz(yz)$ | ✓ | Standard combinatory logic. |
| 76 | 583 | (46) | STD | de Bruijn indices: $\lambda\lambda 2$; $\lambda\lambda\lambda 3\,1(2\,1)$ | ✓ | Standard de Bruijn 1972. |

## §3.1 — Discrete Ricci scalar via Ollivier-Ricci

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 77 | 599 | (47) | STD | $\mathrm{Vol}(B_\epsilon(p))/\mathrm{Vol}(B_\epsilon(0))=1-\frac{R}{6(n+2)}\epsilon^2 + O(\epsilon^4)$ | ✓ | Standard Riemannian ball-volume (Gray, *Tubes* 2nd ed. Thm 3.1; also Ricci-Curbastro). |
| 78 | 604 | (48) | STD | transported-ball-average-distance $\delta(1-\frac{\epsilon^2}{2(n+2)}R + O(\epsilon^3+\epsilon^2\delta))$ | ✗ | **Ollivier 2009 Ex 7 + Thm 4 gives $\mathrm{Ric}(v,v)$, not scalar $R$**. This is the same error flagged in `results/phase2_continuum/eq344_verdict.md` (which addresses the identical equation in 2102.09363 Eq 344). |
| 79 | 611 | Def 29 | DEF | "random walk" $m=\{m_x:x\in X\}$ on Polish $(X,d)$ | ✓ | Standard (Ollivier 2009 §1). |
| 80 | 614 | (49) | STD | $m=\{m_x:x\in X\}$ | ✓ | Definitional. |
| 81 | 620 | Def 30 | DEF | "1-Wasserstein distance" $W_1(m_x,m_y)$ | ✓ | Standard (Villani 2003). |
| 82 | 623 | (50) | STD | $W_1(m_x,m_y)=\inf_{\epsilon\in\Pi(m_x,m_y)}\int d(x,y)d\epsilon(x,y)$ | ⚠ | **Notation bug**: $\epsilon$ used for the coupling *and* elsewhere as the ball radius. No substance issue. Standard Kantorovich formulation. |
| 83 | 630 | Def 31 | DEF | Ollivier-Ricci scalar curvature $\kappa(p,q)=1-W_1(m_p,m_q)/d(p,q)$ | ✓ | Definition matches Ollivier 2009 Def 3. |
| 84 | 633 | (51) | STD | $\kappa(p,q)=1-W_1(m_p,m_q)/d(p,q)$ | ✓ | Standard (Ollivier 2009). |
| 85 | 637 (text) | — | BRIDGE | **Claim: "on a Riemannian manifold with standard volume measure, $\kappa(p,q)$ reduces (up to a scaling factor) to the standard Riemannian Ricci scalar curvature $R(p,q)$"** | ✗ | $R(p,q)$ is not a standard object; Ollivier's theorem delivers $\mathrm{Ric}(v,v)$ for $v$ = direction from $p$ to $q$, the *directional* Ricci tensor, not the scalar $R$. See close-reading §3.1 and `results/phase2_continuum/eq344_verdict.md`. |
| 86 | 641 | Def 32 | DEF | "discrete 1-Wasserstein distance" on discrete metric space | ✓ | Standard (Monge–Kantorovich discretisation). |
| 87 | 644 | (52) | STD | $W_1(m_x,m_y)=\inf_{\mu}\sum d(x',y')\mu(x',y')$ | ✓ | Standard. |
| 88 | 649 | (53) | STD | $\sum_{y'}\mu(x',y')=m_x(x')$ | ✓ | Marginal constraint. |
| 89 | 654 | (54) | STD | $\sum_{x'}\mu(x',y')=m_y(y')$ | ✓ | Marginal constraint. |
| 90 | 661 | Def 33 | DISCR-DEF | Ollivier-Ricci scalar curvature $\kappa(e)$ of a directed hyperedge $e: A\to B$ | ⚠ | Ad hoc generalisation with asymmetric in/out measures (Eqs 58-59 below). No theorem given that this converges, in any limit, to continuum Ricci on an embedding manifold. See close-reading §3.1. |
| 91 | 664 | (55) | DISCR-DEF | $A=\{x_1,\dots,x_n\}\to^e B=\{y_1,\dots,y_m\}$ | ⚠ | Directed hyperedge notation. |
| 92 | 669 | (56) | DISCR-DEF | $\kappa(e)=1-W(\mu_{A^{in}},\mu_{B^{out}})$ | ⚠ | **Missing $d(p,q)$ normaliser**: cf. Eq 51 which divides by distance. For a single-edge hyperedge where "distance" between "centres" is ambiguous, the correct normalisation is ill-defined. |
| 93 | 674 | (57) | DISCR-DEF | $\mu_{A^{in}}=\sum_i \mu_{x_i}$, $\mu_{B^{out}}=\sum_j \mu_{y_j}$ | ⚠ | Sums of probability measures are not probability measures without normalisation; the resulting $\mu_{A^{in}}$ has total mass $n$, not 1. |
| 94 | 679 | (58) | DISCR-DEF | $\mu_{x_i}(z)$ piecewise definition using $d_{x_i^{in}}$ | ⚠ | Piecewise combinatorial rule. Notation: $d_{x_i^{in}}$ (in-degree) and $\mu_{x_i}$ are defined only in-context; vary with edges being traversed. |
| 95 | 689 | (59) | DISCR-DEF | $\mu_{y_j}(z)$ piecewise definition using $d_{y_j^{out}}$ | ⚠ | Same type of ad hoc rule. |
| 96 | 699 | Def 34 | DEF | discrete 1-Wasserstein distance between $\mu_{A^{in}}, \mu_{B^{out}}$ on a directed hypergraph | ⚠ | Repackages Def 32 for the hypergraph case; but since $\mu_{A^{in}}, \mu_{B^{out}}$ are not normalised (Eq 57) the Wasserstein minimisation is not over probability measures. |
| 97 | 702 | (60) | DISCR-DEF | $W(\mu_{A^{in}},\mu_{B^{out}})=\min\sum_{u\to A}\sum_{B\to v}d(u,v)\epsilon(u,v)$ | ⚠ | Notational clash again: $\epsilon$ is coupling; $d$ is graph distance. |
| 98 | 707 | (61) | DISCR-DEF | $\sum_{u\to A}\epsilon(u,v)=\sum_{j=1}^m \mu_{y_j}(v)$ | ⚠ | Marginal. |
| 99 | 712 | (62) | DISCR-DEF | $\sum_{B\to v}\epsilon(u,v)=\sum_{i=1}^n \mu_{x_I}(u)$ | ⚠ | **TeX typo**: $\mu_{x_I}$ should be $\mu_{x_i}$ (capital $I$ instead of $i$). |
| 100 | 719 | (63) | DISCR-ASSERT | $N(r)=ar^n$, $a\in\mathbb Z$ for a "flat" spatial hypergraph | ⚠ | "Flat" is never defined before it is used. Also $a\in\mathbb Z$ is wrong — $a$ is a constant of proportionality that depends on the degree, typically irrational (e.g. $\pi$ for 2D). Close-reading §3.1. |
| 101 | 742 | (64) | BRIDGE | $\mathrm{Vol}(B_r(p)\in\mathcal M)/\mathrm{Vol}(B_r(0)\in\mathbb Z^n)=1-\frac{R}{6(n+2)}r^2+O(r^4)$, "with exactness when $r=1$" | ✗ | **Three issues:** (i) this is just Eq 47 relabelled $\epsilon\to r$; but now **applied to a discrete hypergraph**, not a Riemannian manifold — the derivation was Riemannian. (ii) The parenthetical "with exactness when $r=1$" is unjustified and false in general (an asymptotic expansion is never exact at $\epsilon=1$ except on $\mathbb R^n$). (iii) Relies on the false Eq 48/85 identification of $\kappa$ with scalar $R$. |
| 102 | 747 | (65) | BRIDGE | $N(r)=ar^n(1-\frac{R}{6(n+2)}r^2+O(r^4))$ | ✗ | Correction factor obtained "by analogy" from Riemannian Eq 47, with no proof. Also: empirically refuted on the specific "EFE-satisfying" rule named in 2102.09363 line 6202, where the spatial hypergraph is *bounded*, so $N(r)$ does not grow polynomially at all. See `notes/empirical_refutation.md`. |

## §3.2 — Parallel transport, discrete holonomy, discrete spacetime Ricci

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 103 | 757 | (66) | STD | $R=\mathrm{Tr}(R_{ab})=g^{ab}R_{ab}=R_a^{\,a}$ | ✓ | Standard Riemannian trace. |
| 104 | 764 | (67) | STD | $R_{ab}=R^c_{\ acb}$ | ✓ | Standard Ricci=contraction of Riemann. |
| 105 | 769 | (68) | STD | $\delta v^\alpha = R^\alpha_{\ \beta\gamma\delta}dx^\gamma dx^\delta v^\beta$ | ⚠ | TeX index placement: sub/super ordering unusual ($R_{\beta\gamma\delta}^{\alpha}$). Standard formula for holonomy around an infinitesimal loop. |
| 106 | 774 | (69) | STD | $[\nabla_c,\nabla_d]v^a = R^a_{\ bcd}v^b$ | ✓ | Standard commutator of covariant derivatives. |
| 107 | 781 | (70) | STD | $\Gamma^\rho_{\mu\nu}=\frac12 g^{\rho\sigma}(\partial_\mu g_{\sigma\nu}+\partial_\nu g_{\mu\sigma}-\partial_\sigma g_{\mu\nu})$ | ✓ | Standard Christoffel symbols (MTW §8.5). |
| 108 | 786 | (71) | STD | $R^a_{\ bcd}=\partial_c\Gamma^a_{bd}-\partial_d\Gamma^a_{bc}+\Gamma^a_{ec}\Gamma^e_{bd}-\Gamma^a_{ed}\Gamma^e_{bc}$ | ✓ | Standard Riemann tensor in Levi-Civita. |
| 109 | 791 | (72) | STD | $R_{\alpha\beta\gamma\delta}=\frac12(\partial_\beta\partial_\gamma g_{\alpha\delta}-\dots)$ in locally flat coords | ✓ | Standard (MTW §8.7). |
| 110 | 797 | (73) | STD | $g_{ij}=\delta_{ij}+O(\|\mathbf x\|^2)$ in geodesic normal coordinates | ✓ | Standard. |
| 111 | 802 | (74) | STD | $g_{ij}=\delta_{ij}-\frac13 R_{ijkl}x^k x^l+O(\|\mathbf x\|^3)$ | ✓ | Standard Riemann normal coordinates expansion. |
| 112 | 807 | (75) | STD | $\mathbf J(t)=(\partial\boldsymbol\gamma_\tau/\partial\tau)_{\tau=0}$ (Jacobi field) | ✓ | Standard. |
| 113 | 812 | (76) | STD | $d\mu_g = (1-\frac16 R_{jk}x^j x^k + O(\|\mathbf x\|^3))d\mu_{Eucl}$ | ✓ | Standard Riemannian volume element expansion (Gray 1973/2004, Thm 3.1). |
| 114 | 819 | (77) | STD | $K(\mathbf u,\mathbf v)=\langle R(\mathbf u,\mathbf v)\mathbf v,\mathbf u\rangle/(\|\mathbf u\|^2\|\mathbf v\|^2 - \langle\mathbf u,\mathbf v\rangle^2)$ | ✓ | Standard sectional curvature. |
| 115 | 824 | (78) | STD | $K(\mathbf u,\mathbf v)=\langle R(\mathbf u,\mathbf v)\mathbf v,\mathbf u\rangle$ for orthonormal $\mathbf u,\mathbf v$ | ✓ | Standard. |
| 116 | 830 | (79) | STD | $d(\exp_x(\epsilon \mathbf w_x),\exp_y(\epsilon\mathbf w_y))=\delta(1-\frac{\epsilon^2}{2}K(\mathbf v,\mathbf w)+O(\epsilon^3+\epsilon^2\delta))$ | ✓ | Standard (Ollivier 2009 §5.1; Gray 2004 §4). |
| 117 | 835 | (80) | STD | $\delta(1-\frac{\epsilon^2}{2(n+2)}R+O(\epsilon^3+\epsilon^2\delta))$ — average of sectional curvature | ✗ | **Same directional/scalar error as Eq 48**: Ollivier's theorem yields $\mathrm{Ric}(v,v)$, not $R$, unless $K$ is averaged over all 2-planes, not over all $\mathbf w$ at fixed $\mathbf v$. See `results/phase2_continuum/eq344_verdict.md`. |
| 118 | 840 (text) | — | DISCR-ASSERT | **Assertion: in a directed hypergraph, set $\epsilon=\delta=1$, all non-parallel hyperedges are "orthonormal"** | ✗ | **Load-bearing fiat**: (1) orthonormality declared without any inner product — vacuous. (2) $\epsilon=\delta=1$ invalidates the asymptotic expansions (47)–(80), which are $\epsilon\to 0$. See close-reading §3.2. |
| 119 | 842 | (81) | BRIDGE | $K(\mathbf u,\mathbf v)=\langle R(\mathbf u,\mathbf v)\mathbf v,\mathbf u\rangle$ (repeat of Eq 78) | ⚠ | Formally identical to Eq 78; now used as the "discrete definition" via the fiat of line 840. See close-reading §3.2. |
| 120 | 851 | (82) | BRIDGE | $C(t)=at^n$, $a\in\mathbb Z$ | ⚠ | Leading term for a flat causal graph. As with Eq 63, $a\in\mathbb Z$ is wrong (typically irrational); and "flat causal graph" is never defined. Empirically, for the JGORARD-named EFE rule, $C(t)\approx 2t+1$, i.e. $n=1$ always. See `notes/empirical_refutation.md`. |
| 121 | 865 | (83) | STD | $d\mu_g = (1-\frac16 R_{jk}x^j x^k + O(\|\mathbf x\|^3))d\mu_{Eucl}$ | ✓ | Repeat of Eq 76. |
| 122 | 870 | (84) | BRIDGE | $C(t)=at^n[1-\frac16 R_{jk}t^j t^k + O(\|\mathbf t\|^3)]$ | ✗ | **Key discrete-cone claim.** Obtained "by analogy" from Eq 76, with no derivation in the discrete setting. Tube-volume formula has been independently refuted (different paper, same structural claim) — see `results/phase2_continuum/eq342_verdict.md`. The sign and coefficient do not match the Riemannian tube formula derived there. Empirically, the specific "EFE-satisfying" rule gives $C(t)\sim 2t+1$, ruling out this expansion entirely — see `notes/empirical_refutation.md`. |
| 123 | 875 | (85) | BRIDGE | $t^a=\alpha n^a + \beta^a$ | ⚠ | ADM decomposition of time vector; depends on $(\alpha,n^a,\beta^a)$ from §2.3 which were only verbally identified. |

## §3.3 — Discrete Einstein field equations (the claimed main theorem)

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 124 | 885 (text) | — | DISCR-ASSERT | **Assumption: "asymptotic dimensionality preservation"** — growth rate of global dimension anomaly → 0 | ⚠ | Hypothesis, not theorem. Never made precise in terms of a specific convergence mode. |
| 125 | 887 | (86) | BRIDGE | $S[g^{ab}]=\sum d\mu_g R$ | ⚠ | Discrete sum ostensibly over a causal graph; but $d\mu_g$ was only defined (Eq 76) *inside* the Riemannian expansion, not as a discrete object. $R$ here is "discrete Ollivier-Ricci scalar" (Def 33), which is a per-edge scalar, not a scalar field. |
| 126 | 891 | (87) | BRIDGE | $\delta S[g^{ab}]/\delta g^{ab}\to 0$ | ⚠ | **$\delta/\delta g^{ab}$ is never defined on a discrete metric.** $g$ has not been constructed as an object with components that one could vary. Close-reading §3.3. |
| 127 | 897 | (88) | BRIDGE | $S[g^{ab}]=\int d^4 x \sqrt{-g}R$ (in continuum limit) | ○ | Claim that the discrete sum (Eq 86) converges to the Einstein-Hilbert integral in some "continuum limit". No convergence theorem given; the continuum limit itself is not defined. Would need a Γ-convergence result or analogous. Open. |
| 128 | 902 | (89) | STD | $\mathcal L_G = \sqrt{-g}R$ | ✓ | Standard Einstein-Hilbert Lagrangian (Hilbert 1915). |
| 129 | 907 | (90) | STD | $\delta S/\delta g^{ab}=\sqrt{-g}(R_{ab}-\frac12 Rg_{ab})$ | ✓ | Standard Hilbert variation with zero surface terms. |
| 130 | 912 | (91) | CONCL | $R_{ab}-\frac12 Rg_{ab}=0$ (vacuum EFE) | ✗ | As a conclusion about the discrete system: inherits ✗/⚠ from Eqs 86-88 (the "discrete sum converges to EH" step was not proved; $\delta/\delta g$ not defined discretely). As a standalone continuum formula: ✓. The *claimed derivation* is vacuous — see close-reading §3.3. |
| 131 | 919 | (92) | STD | $d^2 x^\mu/ds^2 + \Gamma^\mu_{\alpha\beta}(dx^\alpha/ds)(dx^\beta/ds)=0$ | ✓ | Standard geodesic equation. |
| 132 | 924 | (93) | STD | $S=\int ds$ | ✓ | Standard action for a timelike curve. |
| 133 | 929 | (94) | STD | $ds=\sqrt{-g_{\mu\nu}dx^\mu dx^\nu}$ | ✓ | Standard line element. |
| 134 | 934 | (95) | STD | $S=\int\sqrt{-g_{\mu\nu}(dx^\mu/d\lambda)(dx^\nu/d\lambda)}d\lambda$ | ✓ | Standard parametrised action. |
| 135 | 948 | (96) | STD | $\mathcal L=\mathcal L_G + C_M\mathcal L_M$ | ✓ | Standard gravity+matter Lagrangian decomposition. |
| 136 | 953 | (97) | CONCL | $R_{ab}-\frac12 Rg_{ab}=8\pi T_{ab}$ | ✗ | As derivation from the discrete side: inherits ✗/⚠ from §3.3. As a continuum statement: ✓. Matter Lagrangian $\mathcal L_M$ on the hypergraph is never given. |
| 137 | 958 | (98) | STD | $T_{ab}=-\frac{C_M}{8\pi\sqrt{-g}}\partial\mathcal L_M/\partial g^{ab}$ | ✓ | Standard Hilbert stress-energy. |
| 138 | 963 | (99) | STD | $T_{ab}=-\frac{C_M}{8\pi\sqrt{-g}}\delta S_M/\delta g^{ab}$ | ✓ | Same, action form. |
| 139 | 977 | (100) | BRIDGE | $S[g^{ab}]=\sum d\mu_g(R+2\Lambda)$ | ⚠ | Adds $2\Lambda$ as integration constant. Same issues as Eq 86. |
| 140 | 982 | (101) | STD | $\mathcal L_G=\sqrt{-g}(R+2\Lambda)$ | ✓ | Standard continuum Lagrangian with $\Lambda$. |
| 141 | 987 | (102) | CONCL | $R_{ab}-\frac12 Rg_{ab}+\Lambda g_{ab}=8\pi T_{ab}$ | ✗ | Same verdict as Eq 97. Continuum EFE with $\Lambda$ — ✓; discrete derivation — ✗. JGORARD's claim the Wolfram Model is "consistent with both zero and non-zero $\Lambda$" is vacuous: you added $\Lambda$ as an arbitrary constant, of course you get either sign. |
| 142 | 994 | (103) | STD | $\partial f/\partial t + \mathbf v\cdot\partial f/\partial\mathbf r + \mathbf F\cdot\partial f/\partial\mathbf v=\hat C f$ (Boltzmann) | ✓ | Standard. |
| 143 | 999 | (104) | STD | same with $\hat C f/\epsilon$ | ✓ | Standard Chapman-Enskog ansatz. |
| 144 | 1004 | (105) | STD | $f=f^{(0)}+\epsilon f^{(1)}+\epsilon^2 f^{(2)}+\dots$ | ✓ | Standard expansion. |
| 145 | 1009 | (106) | STD | $f^{(0)}=n'(\mathbf r,t)(m/(2\pi k_B T'))^{3/2}\exp(-m(\mathbf v-\mathbf v_0')^2/(2k_BT'))$ | ✓ | Standard Maxwellian. |
| 146 | 1014 | (107) | STD | $f^{(1)}=[\dots]f^{(0)}$ (Navier-Stokes closure) | ✓ | Standard Chapman-Enskog (Cercignani). |
| 147 | 1019 | (108) | STD | $\mathbb T:\mathbb T'=\sum_i\sum_j T_{ij}T'_{ji}$ | ✓ | Double-dot product. |
| 148 | 1024 (text) | — | CONCL | **Claim: derivation of EFE is equivalent to Chapman-Enskog hydro expansion with $C(t)$ as distribution function** | ⚠ | Purely analogical; no mapping between Boltzmann equation solution and causal-graph dynamics constructed. |
| 149 | 1026 | (109) | BRIDGE | $C(t)=at^n[1-\frac16 R_{jk}t^j t^k + O(\|\mathbf t\|^3)]$ | ✗ | Repeat of Eq 84 — same refutations. |
| 150 | 1033 | (110) | STD | Lovelock equations (first block) — $\alpha(-\frac12 R_{\rho\sigma}R^{\rho\sigma}g_{\mu\nu}-\dots)$ | ⚠ | **TeX typo**: `g_{\mu nu}` (no backslash on nu). Also the "$\Box R\,\Box R_{\mu\nu}$" product in the first line is dimensionally odd (product of two d'Alembertians?) — likely missing a $+$. Lovelock (1971) is standard; the transcription contains these errors. |
| 151 | 1040 | (111) | STD | $\kappa^2=32\pi G$ | ✓ | Standard. |
| 152 | 1045 | (112) | STD | Weyl tensor $C_{iklm}=R_{iklm}+\frac{1}{n-2}(\dots)+\frac{1}{(n-1)(n-2)}R(\dots)$ | ✓ | Standard (Hawking-Ellis §2.6; Danehkar). |

## §3.4 — Topology, variable dimensionality, cosmology

| # | TeX line | Eqn # | Type | Verbatim | Status | Note |
|---|---|---|---|---|---|---|
| 153 | 1056 | (113) | BRIDGE | $N(r)=ar^n(1-\frac{R}{6(n+2)}r^2+O(r^4))$ | ✗ | Repeat of Eq 65. |
| 154 | 1061 | (114) | BRIDGE | $C(t)=at^n[1-\frac16 R_{jk}t^j t^k+O(\|\mathbf t\|^3)]$ | ✗ | Repeat of Eq 84. |
| 155 | 1066 | (115) | STD | $\forall x\in\mathcal M,\exists U: f \text{ constant on }U$ | ✓ | Standard locally-constant dim property of a manifold (Lee, *Smooth Manifolds*). |
| 156 | 1075 | (116) | STD | $\varphi:(U\subset\mathcal M)\to(\varphi(U)\subset\mathbb R^n)$ (chart) | ✓ | Standard. |
| 157 | 1080 | (117) | STD | atlas $A=\{(U_\alpha,\varphi_\alpha):\alpha\in I\}$ | ✓ | Standard. |
| 158 | 1085 | (118) | STD | $\bigcup_\alpha U_\alpha=\mathcal M$ | ✓ | Standard. |
| 159 | 1090 | (119) | STD | $p:C\to X$ (covering map) | ✓ | Standard algebraic topology. |
| 160 | 1099 | (120) | STD | $V(\Gamma)=\{g:g\in G\}$ (Cayley graph vertices) | ✓ | Standard. |
| 161 | 1104 | (121) | STD | $E(\Gamma)=\{(g,gs):g\in G,s\in S\}$ | ✓ | Standard. |
| 162 | 1109 | (122) | STD | $N_k=z(z-1)^{k-1}$, $k>0$ (Bethe lattice shells) | ✓ | Standard (Bethe 1935). |
| 163 | 1120 | (123) | STD | $c(t)=\hat c\chi(t)$ | ✓ | Standard VSL parametrisation. |
| 164 | 1125 | (124) | STD | $c(t)=c_0\theta(t_c-t)+c_m\theta(t-t_c)$ | ✓ | Standard VSL. |
| 165 | 1130 | (125) | STD | $\theta(t)=\{1\text{ if }t>0, 0\text{ if }t\le 0\}$ | ✓ | Heaviside. |
| 166 | 1138 | (126) | STD | FLRW line element with $c(t)$ | ✓ | Standard. **TeX**: $\sin\theta$ (not $\sin^2\theta$) in the first version, corrected to $\sin^2\theta$ in Eqs 128/129. Copy error. |
| 167 | 1143 | (127) | STD | $g_{\mu\nu}=g_{0\mu\nu}+g_{m\mu\nu}$ (bimetric) | ✓ | Standard VSL. |
| 168 | 1148 | (128) | STD | $ds_0^2 = dt^2 c_0^2\theta(t_c-t) - a^2(t)[\dots]$ | ✓ | Standard. |
| 169 | 1153 | (129) | STD | $ds_m^2 = dt^2 c_m^2\theta(t-t_c) - a^2(t)[\dots]$ | ✓ | Standard. |
| 170 | 1158 | (130) | STD | $\gamma=c_0/c_m$ | ✓ | Standard dimensionless ratio. |
| 171 | 1165 | (131) | STD | $d_H(t)=a(t)\int_0^t c(t')/a(t')\,dt'$ | ✓ | Standard proper horizon. |
| 172 | 1170 | (132) | STD | $dt'=a(t)dt$ (diffeomorphism) | ⚠ | This is a reparametrisation, not a diffeomorphism in the standard sense; also, "$dt'$" is used inconsistently with $t'$ earlier. Minor notational sloppiness. |
| 173 | 1177 | (133) | STD | $H^2+c^2k/a^2=8\pi G\rho/3 + c^2\Lambda/3$ (Friedmann) | ✓ | Standard. |
| 174 | 1182 | (134) | STD | $H(t)=\dot a/a$ | ✓ | Standard. |
| 175 | 1187 | (135) | STD | $\epsilon(t)=|\Omega(t)-1|=c^2|k|/\dot a^2$ | ✓ | Standard flatness param. |
| 176 | 1192 | (136) | STD | $\Omega(t)=8\pi G\rho/(3H^2)$ | ✓ | Standard density param. |
| 177 | 1197 | (137) | STD | $\dot\epsilon(t)=-2c^2|k|\ddot a/\dot a^3 + 2(\dot c/c)(c^2|k|/\dot a^2)$ | ✓ | Standard, derivable from Eqs 135-136. |
| 178 | 1204 | (138) | STD | FLRW line element in $n$ spatial dims | ✓ | Standard (Tangherlini 1963). |
| 179 | 1209 | (139) | STD | $r^2=\sum_i(x_i)^2$ | ✓ | Standard. |
| 180 | 1214 | (140) | STD | $\dot\rho + n(\rho+p)\dot a/a=0$ ($n$-D energy conservation) | ✓ | Standard (Tangherlini / Lima). |
| 181 | 1219 | (141) | STD | $\frac{n(n-1)}{2}[\dot a^2/a^2+k/a^2]=8\pi G_n\rho$ | ✓ | Standard $n$-D Friedmann. |
| 182 | 1224 | (142) | STD | $\frac{(n-1)\ddot a}{a}+\frac{(n-1)(n-2)}{2}[\dot a^2/a^2+k/a^2]=-8\pi G_n p$ | ✓ | Standard $n$-D acceleration eqn. |
| 183 | 1229 | (143) | STD | $p=\omega_n\rho$ | ✓ | Standard $n$-D equation of state. |
| 184 | 1234 | (144) | STD | $a(t) = [\dots]$ (Holanda–Pereira closed form) | ✓ | Cited from Holanda-Pereira; correct. |

---

## Section-by-section verdicts

| Section | Overall verdict |
|---|---|
| §2.1 Basic formalism | Definitions are readable but informal. Defs 3–4 have undefined concepts ("outgoing hyperedges" on undirected graphs; "applicable because of"). |
| §2.2 Abstract rewriting | Standard ARS material, all ✓. Only caveat: Def 9 (causal invariance) is quantified-informally. |
| §2.3 Causal graph hypersurfaces / ADM | Mix of standard ✓ carryovers of Penrose-Hawking-Ellis causal structure (Defs 17-25, Eqs 29-38) and load-bearing ⚠/⊘ items: Eqs 25-28 (ADM identification) and the two named conclusions (causal inv ⇔ GC, and the SR derivation) which are tautological / circular. |
| §2.4 Discrete Lorentz transformations | Def 26 / Eq 43 apply the continuum Lorentz formula to integer lattice without closure / approximation theorems (⚠). The particle-as-Kuratowski-tangle discussion contains no equations, only prose. |
| §3.1 Ollivier-Ricci on hypergraphs | **Major load-bearing errors.** Eq 48/85 (`R` vs `Ric(v,v)`) is refuted in `results/phase2_continuum/eq344_verdict.md`. Def 33 and Eqs 56-65 are ad-hoc with no convergence theorem. Eq 65 empirically refuted on JGORARD's named rule by `notes/empirical_refutation.md`. |
| §3.2 Parallel transport / Riemann / Ricci on hypergraphs | §3.2 Riemannian review (Eqs 66-80) is all ✓. The discrete transition (line 840 fiat: orthonormal non-parallel hyperedges; $\epsilon=\delta=1$) is unjustified (✗). Eq 84 is refuted (same structural error as 2102.09363 Eq 342, see `results/phase2_continuum/eq342_verdict.md`). |
| §3.3 Discrete EFE (main theorem) | Depends on Eqs 86-88 (discrete action, variation, continuum limit) — all ⚠/○. The final equations (91, 97, 102) are correct continuum EFE but the *discrete derivation of them* from the hypergraph is vacuous: none of the three required steps (define discrete action, prove continuum limit, define discrete variational principle) is carried out. Close-reading §3.3. |
| §3.4 Variable dim + cosmology | Eqs 113-144 are all ✓ textbook continuum cosmology (VSL, $n$-D FLRW, Holanda-Pereira). The "connection to the Wolfram Model" is prose-only; no discrete-side object is constructed. |

## Load-bearing bridge claims (for the main §3.3 theorem)

The chain of claims that would need to be made rigorous for the "derivation of Einstein's equations" to stand:

| Load-bearing claim | Eqn # | Status |
|---|---|---|
| Ollivier-Ricci scalar on hypergraphs converges to scalar $R$ on the continuum limit | (48), (80) | ✗ (error is `R` ↔ `Ric(v,v)`; see eq344 verdict) |
| Hypergraph ball volume $N(r)$ grows as $ar^n(1-Rr^2/6(n+2)+\dots)$ | (65) | ✗ (empirical refutation on JGORARD's named rule) |
| Non-parallel hyperedges can be treated as orthonormal | line 840 fiat | ✗ (declared, not constructed) |
| $\epsilon=\delta=1$ is OK in asymptotic expansions | line 840 fiat | ✗ (category error) |
| Hypergraph cone volume $C(t)$ expansion | (84) | ✗ (same error as 2102.09363 Eq 342; see eq342 verdict) |
| Discrete Einstein-Hilbert sum = continuum EH integral | (88) | ○ (continuum limit not defined) |
| Discrete variation $\delta S/\delta g^{ab}=0$ | (87) | ⚠ ($g$ never constructed, $\delta/\delta g$ never defined discretely) |

None of these is verified; five are refuted, one open, one ill-defined. The main conclusion (Eq 91, vacuum discrete EFE) inherits the worst of these, i.e. ✗.

## Equations that are candidates for Lean formalisation

Equations that are correct-as-stated AND whose proof is purely continuum-mathematical (no discrete→continuum bridge, no JGORARD-specific constructions) — these are safely formalisable in Mathlib-style Lean:

- **§2.2 Abstract rewriting:** Eqs (2)–(14). All correspond to existing Mathlib definitions (rewriting / confluence / Church-Rosser).
- **§2.3 Causal structure on a DAG / partial order:** Defs 17–25, Eqs (29)–(36), (39). All are order-theoretic and match Hawking-Ellis verbatim; no Lorentzian-manifold content is required.
- **§3.1 Ollivier-Ricci on metric-measure spaces:** Defs 29–32, Eqs (49)–(54). Standard Villani/Ollivier material; Mathlib's probability + metric library covers this.
- **§3.2 Riemannian building blocks:** Eqs (66)–(80). Pure Riemannian geometry; potentially formalisable via Mathlib's differential-geometry library.
- **§3.3 Einstein-Hilbert variation:** Eqs (89)–(95), (98), (99), (101). Standard continuum GR; Mathlib doesn't have GR yet, so these would be a Mathlib-adjacent effort.
- **§3.4 Cosmology:** Eqs (113)–(144). Pure FLRW calculus; formalisable with symbolic-differentiation tactics.

Equations that are **NOT Lean candidates** (because they are either refuted or require ill-defined objects): **Eqs (25)–(28), (43), (48), (55)–(65), (81)–(85), (86)–(88), (109)**. These are the load-bearing hypergraph claims where the whole content of the paper's novelty resides.

## Note on the Lean programme

The "five items we would need in Lean to actually prove or refute the main theorem" listed at the end of `notes/2004.14810_close_reading.md` (discrete metric-measure Lorentzian structure; discrete Ollivier-Ricci tensor with convergence theorem; discrete EH functional with Γ-convergence; discrete-to-continuum variational principle; full EFE theorem) map directly onto the ⚠/○/✗ rows of this catalog. Each open row is a missing theorem or definition in that programme.
