# Glossary

Definitions used throughout this project. Organized by topic. Terms Gorard uses in his corpus are marked with ★; our additions are unmarked.

## Hypergraph rewriting

**Hypergraph (directed).** A pair $H = (V, E)$ where $V$ is a set of vertices and $E$ is a multiset of *ordered* tuples of vertices ("hyperedges"). In our Lean formalisation, `Hyperedge V` is a nonempty `List V`; `Hypergraph V` is a `Multiset (Hyperedge V)`.

**Rule.** A pair $(LHS, RHS)$ of hypergraphs on a common *pattern-vertex* type. When a rule fires, a subhypergraph matching $LHS$ is replaced by $RHS$.

**Match.** An assignment of pattern vertices to target vertices such that the image of $LHS$ sits in the target as a submultiset. Pattern vertices in $RHS$ that are not in $LHS$ are *fresh* and allocate new target vertices on firing.

**Application.** A match plus the choice of fresh-vertex bindings. Each application has a `consumed` multiset (the LHS image) and a `produced` multiset (the RHS image).

**Conservative rule.** A rule with $|LHS| = |RHS|$. Edge count is preserved by every application. Keystone of our P1 / P2 structural findings.

**State size.** The multiset cardinality of the hypergraph's edge multiset. For a conservative rule, the state size is constant along every trajectory.

★ **Single-way evolution.** A linear sequence $s_0 \to s_1 \to \ldots$ where each step picks one match per rule per step. The result is one causal graph. Determined by a scheduler (SetReplace's `EventOrderingFunction`).

★ **Multi-way evolution graph (MWEG).** The directed acyclic graph of *all* possible states reachable from $s_0$ via legal applications, with edges to every possible successor. Every path through the MWEG is a legal single-way evolution.

★ **Branchial graph.** A graph on states at the same "generation" of the MWEG; edges connect states sharing a common ancestor. Intended to encode a quantum-mechanical notion of "branchial distance."

★ **Causal graph.** A directed graph whose vertices are events (rule firings) along a single-way evolution, with an edge $A \to B$ iff some expression produced by $A$ is consumed by $B$. See also *causal precedence*.

★ **Causal precedence / light-cone structure.** The partial order $\prec$ on events induced by the causal graph.

★ **Causal invariance.** Property of a rewriting system: all causal graphs produced by every path through the MWEG are isomorphic (or "eventually isomorphic"). A multi-way property. Analogous to confluence in abstract rewriting.

★ **Confluence (Church–Rosser).** Standard ARS property: divergent rewrites reconverge. Necessary condition for causal invariance.

★ **Asymptotic dimensionality preservation.** Gorard's condition (G1 §3.3): the "dimension anomaly" of the causal graph $\to 0$ as the graph grows. Defined by Gorard as $\delta S[g^{ab}] / \delta g^{ab} \to 0$. Our audit classifies this as tautological (S3) because the definition is the Euler-Lagrange equation of the claimed action.

## Continuum geometry

**Riemannian manifold** $(M, g)$. A smooth manifold with a positive-definite metric $g$.

**Lorentzian manifold** $(M, g)$. A smooth manifold with a metric of signature $(-,+,+,+)$.

**Metric tensor** $g_{ab}$ / **inverse metric tensor** $g^{ab}$. Standard.

**Christoffel symbols** $\Gamma^\rho_{\mu\nu}$. Components of the Levi-Civita connection.

**Riemann tensor** $R_{abcd}$ / **Ricci tensor** $R_{ab} = R^c_{acb}$ / **scalar curvature** $R = g^{ab} R_{ab}$. Standard.

**Directional Ricci** $\mathrm{Ric}(v, v) = R_{ab} v^a v^b$ for a unit vector $v$. *Not* the same as $R$ in general. The conflation of $\mathrm{Ric}(v,v)$ with $R$ is S1 in our taxonomy.

**Einstein field equations.** $R_{ab} - \tfrac{1}{2} R g_{ab} + \Lambda g_{ab} = 8\pi T_{ab}$.

**ADM formalism.** A 3+1 decomposition of a Lorentzian spacetime: lapse $\alpha$, shift $\beta^i$, spatial metric $\gamma_{ij}$; line element $ds^2 = -\alpha^2 dt^2 + \gamma_{ij}(dx^i + \beta^i dt)(dx^j + \beta^j dt)$.

**BSSN / CCZ4.** Specific hyperbolic re-formulations of the Einstein PDEs used in numerical relativity. Not specific to the Wolfram program.

**Null tetrad** $\{\ell, n, m, \bar m\}$. A basis of $T_p M$ at each point of a Lorentzian 4-manifold satisfying $\ell \cdot n = -1$, $m \cdot \bar m = 1$, all other inner products zero. Requires a tangent space. **Does not exist intrinsically on a hypergraph** — see [`notes/null_tetrad_resolution.md`](notes/null_tetrad_resolution.md).

**Newman–Penrose formalism.** Decomposition of Weyl/Riemann tensor via the null tetrad. $\Psi_4$ = outgoing gravitational radiation.

**Kinnersley tetrad.** A particular null tetrad aligned with the principal null directions of the Kerr Weyl tensor. Used for black-hole perturbation theory.

## Metric-measure geometry

**1-Wasserstein distance** $W_1(\mu, \nu)$. The optimal transport distance between probability measures on a metric space: $\inf_\pi \int d(x,y) d\pi(x,y)$ over couplings $\pi$ of $\mu$ and $\nu$.

**Ollivier–Ricci curvature** $\kappa(x,y) = 1 - W_1(m_x, m_y) / d(x,y)$ for a random walk $m$ on a metric space $(X, d)$. For a Riemannian manifold with uniform-ball random walk, Ollivier (JFA 2009, Example 7) proved $\kappa = \varepsilon^2 \mathrm{Ric}(v,v) / (2(d+2)) + O(\varepsilon^3)$ where $v$ = unit vector from $x$ to $y$.

**Directional vs scalar Ollivier.** Ollivier's Riemannian identity yields $\kappa$ ∝ directional Ricci $\mathrm{Ric}(v,v)$. Gorard consistently writes scalar $R$ where $\mathrm{Ric}(v,v)$ should appear — S1.

**Benincasa–Dowker action.** A discrete counting functional $S_{BD}(C)$ on a causal set $C$, whose expectation under Poisson sampling in a continuum spacetime converges to (conjecturally) the Einstein–Hilbert action.

## Limit / convergence

**Gromov–Hausdorff (GH) convergence.** A topology on the space of compact metric spaces. Standard for comparing sequences of discrete approximations to manifolds.

**Lorentzian Gromov–Hausdorff.** Extension of GH to Lorentzian (pseudo-Riemannian) spaces using the Lorentzian time-separation in place of the Riemannian distance. Young theory — Noldus 2004, Minguzzi–Suhr 2020.

**Γ-convergence.** Variational notion of convergence for functionals; ensures that minimisers of the discrete functional approach minimisers of the continuum functional. Proper tool for discrete-to-continuum variational claims (Braides 2002).

**Poisson sampling / sprinkling.** Drawing a countable point set in a measure space whose number-of-points-in-$V$ distribution is Poisson$(\rho \mathrm{Vol}(V))$. Standard in causal-set theory. In G3 §5 this is what replaces "Wolfram-model dynamics" by fiat.

**Continuum limit.** Informal phrase used throughout Gorard's corpus. Never formally defined. Could mean GH, spectral, measure-space, Γ-convergence, or several other things; the papers do not commit.

## Research program

**Infrageometry.** The study of discrete analogues of continuous geometric notions (curvature, metric, volume, differential operators, connection, holonomy) on combinatorial structures (hypergraphs, causal sets, directed multigraphs), made rigorous by *convergence theorems* linking the discrete objects to classical continuum geometry. The long-term research direction that hosts this repository; see [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md).

**Discrete-to-continuum bridge.** A theorem of the form: "sequence of discrete objects $X_n$ with parameter $\varepsilon_n \to 0$ converges (in a specified topology) to a continuum object $X$, and discrete invariants defined on $X_n$ converge to the corresponding classical invariants on $X$." The object of phases 3–6 of the research program.

**Parallel-layer bound / Parallel schedule width.** For a conservative rule (|LHS|=|RHS|=k) evolving from seed of size N, the greedy-parallel-schedule decomposition of the causal DAG has each layer containing ≤ ⌊N/k⌋ events. Provable from conservation; distinct from (and weaker than) "linear BFS-cone growth," which requires rule-specific structure.

## Our project vocabulary

**Rail (verification).** One of four independent ways we verify a claim: (A) literature re-derivation, (B) symbolic check, (C) numerical check, (D) manual hand-check. A claim must pass ≥ 3 to be published as verified.

**Corpus (G1–G4).** The four Gorard papers under audit: 2004.14810 (G1), 2011.12174 (G2), 2102.09363 (G3), 2303.07282 (G4).

**Severity class (S1–S6).** Defined in [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md). S1 = false statement; S2 = ill-defined; S3 = tautology; S4 = unsupported bridge; S5 = refuted specific; S6 = claim not delivered in the body.

**Verdict status.** ✓ verified, ✗ refuted, ⚠ ill-defined, ⊘ tautology, ○ open.

**Conservative rule.** $|LHS| = |RHS|$ — Wolfram-model-specific term (not Gorard's; ours). Central to the structural refutation of S5.

**Directional Ricci conflation.** Our label for the S1 error pattern — treating $\mathrm{Ric}(v,v)$ as if it were the scalar $R$.

**Claim not delivered in the body.** S6 — a title or abstract states a result that the body does not deliver.
