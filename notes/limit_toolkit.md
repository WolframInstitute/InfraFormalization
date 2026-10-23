# Continuum-limit results in the literature

This note lists published results that bear on a passage from discrete structures to continuum geometry, with the status of each: theorem, numerical support, or open. G1-G3 use the phrase "in the continuum limit" without stating which notion of convergence is meant (`FINDINGS.md` S4 #10). The notions below differ from one another.

Paper files: G1 = `papers/gorard_2004.14810.txt`, G3 = `papers/gorard_2102.09363.txt`.

## 1. Ollivier-Ricci curvature of metric measure spaces

Theorem (Ollivier, J. Funct. Anal. 2009). Let (M, g) be a smooth n-dimensional Riemannian manifold and let m_x^ε be the uniform measure on the ball B_ε(x). For y = exp_x(δv) with |v| = 1,
$$
\kappa(x,y)\;=\;1-\frac{W_1(m^\varepsilon_x, m^\varepsilon_y)}{d(x,y)}\;=\;\frac{\varepsilon^2}{2(n+2)}\,\mathrm{Ric}(v,v)+O(\varepsilon^3+\varepsilon^2\delta).
$$

G1 eq. 48 (line 1468, §3.1) states the corresponding average-distance expansion with the scalar curvature R in place of Ric(v,v). G1 Definition 31 (lines 1521-1534) states that κ(p, q) "reduces (up to some arbitrary scaling factor) to the standard Riemannian Ricci scalar curvature R(p, q)". Ollivier's theorem gives Ric(v,v) in the direction of the geodesic from p to q. The arithmetic comparison of the two leading terms is PROVED (`Infra.ollivier_gorard_agree_iff`, `results/phase2_continuum/eq344_verdict.md`).

Discrete versions: Ollivier (2007, 2009) and Lin, Lu and Yau (2011) define κ on graphs with W_1 between random-walk measures. Eidi and Jost (2019) define it on directed hypergraphs. G1 Definition 33 (line 1592) defines the Ollivier-Ricci curvature of a directed hyperedge and cites Eidi and Jost (G1 reference [44]).

Open in the literature: a theorem that κ_{G_n} → Ric for a sequence of graphs G_n converging to (M, g) in a general sense. Convergence results exist for random geometric graphs on a manifold (García Trillos and Slepčev 2018 and related work). No result covers the causal graphs or spatial hypergraphs of a Wolfram model evolution.

## 2. The Benincasa-Dowker action on causal sets

Setup (Sorkin 2007; Benincasa and Dowker 2010). For a causal set C obtained by Poisson sampling of (M, g) at density ρ_c, the discrete d'Alembertian B^(d) is a weighted sum over the k-th nearest past neighbours (k = 0, 1, 2, 3 in four dimensions) with coefficients chosen so that
$$
\left\langle B^{(d)}_\rho \phi \right\rangle \xrightarrow{\rho\to\infty} \Box\phi - \tfrac{1}{2} R\,\phi
$$
in Riemann normal coordinates. With φ ≡ 1 this gives a discrete scalar curvature, and its sum over the events is the Benincasa-Dowker action S_BD.

Status:

- The limit of the expectation of B^(d) φ(x) at a point is derived by Benincasa and Dowker (2010) under Poisson sampling, in Riemann normal coordinates, with assumptions on the region of the past light cone that contributes.
- The convergence of the expectation of the integrated action to S_EH is not proved. It requires zero surface terms and a vanishing contribution from the region of the light cone outside the Riemann normal neighbourhood. Sorkin (2007) introduced the intermediate non-locality scale l_k to reduce the fluctuations of the discrete operator. G3 eq. 388 (line 6133, TeX line 2927) chooses l_k with l_k ≫ (l² L)^{1/3}.
- Cunningham (2018, PhD thesis, G3 reference [108], lines 7139-7141) gives numerical support. G3 states the convergence "as proposed by Sorkin, Benincasa and Dowker, and demonstrated numerically by Cunningham" (lines 6110-6112).

G3 describes the rule of line 6202 as one "that provably satisfies the Einstein field equations in the continuum limit" (abstract, lines 50-52). The argument of G3 §6 replaces weak ergodicity "with the much stronger assumption of uniform Poisson distribution of the rewrite events" (line 6080) and then applies the Benincasa-Dowker convergence. The steps concern a causal set obtained by Poisson sampling of a given (M, g). G3 gives no proof that the causal graph of the rule is distributed as such a causal set.

## 3. Gromov-Hausdorff convergence

Riemannian case: Fukaya (1987) and Cheeger and Colding (1997-2000) describe Gromov-Hausdorff limits of Riemannian manifolds with Ricci curvature bounded below, with rectifiability, volume comparison and regularity results.

Graphs: a finite graph with its path metric is a metric space, and one can ask whether a sequence G_n converges to (M, d_g) in Gromov-Hausdorff distance. For random geometric graphs and proximity graphs of Poisson point processes, convergence results are known (García Trillos, Slepčev and coauthors). For Wolfram model hypergraph rewriting no such result is known.

Lorentzian case: Noldus (2004), Bombelli and Noldus (2004) and Minguzzi and Suhr (2022) define Gromov-Hausdorff distances for Lorentzian spaces with the time separation τ in place of the distance d.

## 4. Spectral convergence of graph Laplacians

Theorem (Singer 2006; Belkin and Niyogi 2008; García Trillos and coauthors 2020). For points sampled independently from a density on a compact Riemannian manifold, a normalised graph Laplacian converges to the Laplace-Beltrami operator as n → ∞ and ε → 0 at a suitable rate, pointwise and spectrally.

These theorems require independent sampling from a density. No theorem states that the hypergraphs of a Wolfram model evolution have this form.

## 5. Lorentz invariance of causal sets

Theorem (Bombelli, Henson and Sorkin 2009). A Poisson-sampled causal set in Minkowski space does not determine a preferred frame: the Poisson process is Lorentz invariant in distribution. A regular lattice does not have this property. The Benincasa-Dowker step of G3 §6 uses Poisson sampling (line 6080).

## 6. Limits of graph sequences

Dense graphs: Lovász and Szegedy (2006) and Borgs, Chayes, Lovász, Sós and Vesztergombi (2008) show that Cauchy sequences of dense graphs in the cut distance converge to graphons.

Sparse graphs: Benjamini and Schramm (2001) define local weak convergence, whose limit is a random rooted graph. In the causal graph of a rule, the in-degree of an event is at most |LHS| and the out-degree at most |RHS| (the out-degree bound is PROVED as `CausalHistory.History.succ_card_le`), so the causal graphs are sparse and the dense theory does not apply to them. No application of sparse-graph limits to hypergraph rewriting is known.

## Statements needed for a continuum theorem

A theorem of the form "a rule R that is causal invariant and asymptotically dimension preserving has a continuum limit that satisfies the vacuum Einstein equations" needs each of the following. Each is OPEN.

1. A notion of convergence on a space that contains finite causal graphs and Lorentzian manifolds, for example a Lorentzian Gromov-Hausdorff distance.
2. A theorem that the evolution of R produces causal graphs whose events are distributed, in the limit, as a Poisson process on a Lorentzian manifold, or as another process that is Lorentz invariant in distribution.
3. The Benincasa-Dowker convergence for the distribution in item 2.
4. A variational statement: minimisers of the discrete action converge to solutions of the Einstein equations, for example by Γ-convergence (Braides 2002; Alicandro and Cicalese 2004).
5. A rule for which item 2 holds.

G1-G3 give arguments for the individual steps and give no proof that links them.
