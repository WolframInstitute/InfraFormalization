# Continuum-limit toolkit

An inventory of the actual mathematical results that *could* make a Gorard-style "discrete → continuum GR" derivation rigorous. For each tool, the status matters: *proved theorem*, *conjecture with numerical support*, *heuristic only*. This matters because Gorard's papers repeatedly use "in the continuum limit" as if a single such limit exists — in reality there are several distinct notions and they do not agree.

## 1. Ollivier–Ricci for metric-measure spaces

**Theorem (Ollivier, JFA 2009).** Let $(M,g)$ be a smooth Riemannian manifold and let $m^\varepsilon_x$ be the uniform distribution on the closed ball $B_\varepsilon(x)$. For $q = \exp_x(\varepsilon v)$ with $|v|=1$:
$$
\kappa(x,q)\;=\;1-\frac{W_1(m^\varepsilon_x, m^\varepsilon_q)}{d(x,q)}\;=\;\frac{\varepsilon^2}{2(n+2)}\,\mathrm{Ric}(v,v)+O(\varepsilon^3).
$$
This is the theorem Gorard invokes in §3.1 of 2004.14810 (his Eq 48). Note the RHS is the **directional Ricci curvature** $\mathrm{Ric}(v,v)$, *not* the scalar curvature $R$. Gorard's prose in Def 31 says "reduces to the standard Riemannian Ricci scalar curvature $R(p,q)$" — there is no such object. The theorem recovers $\mathrm{Ric}(v,v)$ along the $p \to q$ direction. This is a live-ammunition error — a serious referee would reject on this.

**Discrete analogue (Lin–Lu–Yau 2011; Ollivier 2007; Eidi–Jost 2019 for directed hypergraphs).** On a graph or (directed) hypergraph one defines $\kappa$ using a discrete Wasserstein $W_1$ between simple-random-walk distributions. Gorard's Def 33 is essentially Eidi–Jost specialized to a particular in/out-measure choice.

**What is *not* proved for discrete $\kappa$.** A convergence theorem of the form
$$
\text{graph sequence } G_n \to (M,g) \text{ in GH / spectral / … } \implies \kappa_{G_n} \to \mathrm{Ric}_{(M,g)}
$$
is **not** a theorem. Partial results exist for very specific constructions (Cristofaro-Gardiner & Viazovska-style lattices, or random geometric graphs on a Riemannian manifold in the $\varepsilon \to 0$ limit — van der Hofstad 2017ff, Trillos–Slepčev 2018). None applies to general causal-invariant hypergraph rewriting.

**Implication for Gorard.** Even reading the term "scalar" charitably, a convergence theorem for *Gorard's directed-hyperedge $\kappa$ applied to the causal graph of a Wolfram-model evolution* does not exist in the literature.

## 2. Benincasa–Dowker action on causal sets

**Setup (Sorkin 2007, Benincasa–Dowker 2010).** For a causal set $C$ Poisson-sampled in $(M,g)$ at density $\rho_c$, define a local discrete d'Alembertian $B^{(d)}_\rho$ as a weighted sum over $k$-nearest-past-neighbors ($k = 0,1,2,3$), with specific alternating-sign coefficients $c_k^{(d)}$ dimensionally tuned so that
$$
\left\langle B^{(d)}_\rho \phi \right\rangle \xrightarrow{\rho\to\infty} \Box\phi - \tfrac{1}{2} R\,\phi
$$
in expectation, in Riemann normal coordinates. Setting $\phi\equiv 1$ yields the discrete scalar curvature. Summing over events yields the **Benincasa–Dowker action** $S_{\mathrm{BD}}$.

**Status of $\langle S_{\mathrm{BD}} \rangle \to S_{\mathrm{EH}}$.**
- Pointwise convergence of $\langle B^{(d)}_\rho \phi(x)\rangle \to \Box\phi(x) - \tfrac{1}{2}R(x)\phi(x)$: **proved** (Benincasa–Dowker 2010) under Poisson sampling in Riemann normal coordinates, with technical assumptions on $\phi$'s support relative to the light cone of $x$.
- Convergence of the *integrated action* $\langle S^{(d)}_\rho \rangle \to S_{\mathrm{EH}}$: **not proved**. Issues:
  - The sum picks up contributions from far down the light cone, which require a "non-locality cut-off" $l_k$ (Sorkin 2007) that has to be tuned — Gorard (2102.09363, Eq 388) sets $l_k \ll l^{\tfrac{2}{3}} L^{\tfrac{1}{3}}$ by fiat.
  - "Zero surface terms" is needed; this is natural only in asymptotically flat or compact spacetimes.
  - Fluctuations: $\mathrm{Var}(S^{(d)}_\rho)$ grows with $\rho$ (Dowker 2019, Sorkin 2020), which makes the Monte-Carlo-style "expectation converges" claim weaker than one would like. Dowker and collaborators have developed a smearing / thermodynamic-limit argument, but it remains **conjectural**.
- Cunningham 2018 (cited by Gorard) gave numerical support for the conjecture; not a proof.

**Implication for Gorard.** What he calls "a hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit" is at best the Poisson-sampling / BD convergence conjecture, one step removed. It says nothing about the dynamics of any specific Wolfram rule; it is a statement about the *kinematics of Poisson-sampling a causal set from a given $(M,g)$*. The direction of inference is backwards from what a derivation of GR would need.

## 3. Gromov–Hausdorff convergence

**Theorem (Fukaya 1987; Cheeger–Colding 1997–2000).** A pointed GH limit of a sequence of Riemannian manifolds with uniformly bounded Ricci curvature below is a metric-measure space with rectifiable structure. Various rigidity, volume-comparison, and regularity results.

**For graphs.** A finite graph $(V,d_G)$ is a metric space; we can ask whether a sequence $G_n$ converges in GH to $(M,d_g)$. For specific sampled constructions (random geometric graphs, Poisson point processes with proximity graphs, Delaunay-type triangulations) such convergence has been proved (Trillos, Slepčev, García-Trillos–Gerlach–Hein–Slepčev). For Wolfram-model hypergraph rewriting there is *no* such result, nor any obvious route to one without either (a) proving the graph sequence comes from a Poisson sample, or (b) identifying an embedding into a fixed manifold and passing to an $\varepsilon \to 0$ limit.

**Lorentzian GH.** Noldus 2004; Bombelli–Noldus 2004; Minguzzi–Suhr 2020+. The Lorentzian version replaces $d$ by the Lorentzian time-separation $\tau$. This is the right framework for causal-graph continuum limits, but it is still young mathematics. Noldus–Suhr 2022 established convergence of sampled causal sets to Lorentz manifolds under hypotheses essentially matching BD. This is the nearest-to-rigorous precedent for what Gorard claims.

## 4. Spectral convergence of graph Laplacians

**Theorem (Belkin–Niyogi 2008; Singer 2006; García-Trillos et al. 2020).** For points sampled iid from a density on a compact Riemannian manifold, an appropriately normalized graph Laplacian converges (pointwise, spectrally, and in operator norm) to the Laplace–Beltrami operator as $n\to\infty$, $\varepsilon\to 0$ at the right rate.

**Implication.** If the Wolfram-model evolution produced hypergraphs whose shadow on a fixed manifold looked like iid samples from a smooth density, one could invoke spectral convergence. But for general causal-invariant rules there is no mechanism ensuring this — the hypergraph has intrinsic discrete dynamics, not a probabilistic sampling structure.

## 5. Causal-set Lorentz invariance

**Theorem (Bombelli–Henson–Sorkin 2009).** A Poisson-sampled causal set in Minkowski space is statistically Lorentz invariant — there is no distinguished "rest frame" emerging from the discretization, even though individual samples look irregular.

**Relevance.** This is the actual rigorous result behind the Wolfram-model slogan "discrete spacetime without a preferred frame." It requires Poisson sampling (so the point process is LI in distribution), not arbitrary discretization. A regular lattice would violate LI in the continuum limit; a Poisson sample does not. Gorard uses this implicitly by invoking BD, but does not separate out what is actually being used.

## 6. Graphon / dense graph limits

**Theorem (Lovász–Szegedy 2006; Borgs–Chayes–Lovász–Sós–Szegedy 2008).** Cauchy sequences of dense graphs under the cut-distance converge to graphons. This is a well-developed theory for dense graphs.

**Relevance.** Of limited use for Wolfram model, whose graphs are sparse (polynomial-volume growth tracking spacetime dimension). Sparse-graph-limit theory (Benjamini–Schramm 1999; local weak convergence) is the right one, but it gives a "tangent space" picture (limit = rooted random graph) that doesn't obviously approach a manifold. Lyons–Nazarov 2011, Szegedy 2014 on sparse limits are active research; no applications to hypergraph rewriting exist.

## What would a real Gorard-style theorem look like?

To make "Wolfram model rule $R$ (causal-invariant, asymptotically dimension-preserving) has a continuum limit satisfying the vacuum Einstein equations" into a real theorem, one would need all of the following:

1. **Precise limit notion**: a topology on a space containing both finite hypergraphs/causal graphs and pseudo-Riemannian manifolds. Lorentzian-GH (Noldus–Suhr) is the most plausible candidate, but needs extension to handle the non-Poisson case.
2. **Distribution control on the dynamics**: a theorem that iterated application of $R$ to a large hypergraph produces causal graphs whose vertex density converges to a Poisson measure on some limiting manifold, or at least to a measure with the statistical-Lorentz-invariance property.
3. **BD-convergence in that limit**: an upgrade of Benincasa–Dowker's expectation result to the concrete measure produced by $R$. This is where Cunningham's numerical work would need to be proved.
4. **Variational characterization of EFE in the limit**: minimization of the discrete BD action converges (in Γ-convergence or related sense) to minimization of the EH action. Γ-convergence of discrete-to-continuum actions is a mature theory (Braides 2002, Alicandro–Cicalese 2004) and this step is probably the most tractable.
5. **Construction of an explicit rule satisfying (2).** Currently no rule is known for which (2) is proved.

Any of (1)–(5) being unproved means the overall chain is unproved. Gorard's papers contain at most plausibility arguments for each step independently; none are linked into a rigorous chain.

## Practical conclusion

The tools exist. Causal-set theory has been building them for 20+ years and has genuine partial results. Gorard's contribution relative to that literature, in the specific matter of "deriving GR from discrete spacetime," is **almost entirely absent** — every load-bearing step he uses is due to Sorkin, Benincasa, Dowker, Bombelli, Henson, and collaborators. What is Gorard's own is the reformulation using directed hypergraphs and the narrative that this emerges from a *specific Wolfram-model rewriting rule*. The latter is the claim with no rigorous backing.
