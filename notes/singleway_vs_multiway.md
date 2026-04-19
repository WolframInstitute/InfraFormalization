# Single-way vs multi-way evolution — what it means, what Gorard does, where our refutations stand

Written for a reader who knows the Wolfram Physics framework (causal graph, multiway evolution graph, branchial slices) but wants a precise account of *why* Gorard's papers are usually single-way, *when* the multiway view actually matters, and *whether* our refutations survive the distinction.

## 1. Precise definitions

Fix a rewriting system: rules $R = \{r_1, \ldots, r_k\}$, initial state $s_0$ (a hypergraph).

**Single-way evolution.** A linear sequence $s_0 \to s_1 \to s_2 \to \cdots$, where each step is determined by a single *choice* of rule application. To make evolution deterministic one picks an **event-ordering function** (SetReplace's `EventOrderingFunction`), which given the current state returns one of the many possible matches. One causal graph is built from this linear sequence: events = applied rules, edges = expression-level dependencies.

**Multiway evolution graph (MWEG).** A directed acyclic graph whose nodes are states. From each state $s$, draw an edge to *every* state $s'$ reachable from $s$ by applying *any* legal rule at *any* legal match. The full tree/DAG of possibilities. In the MWEG every path from $s_0$ is a legal single-way evolution.

**Branchial structure.** Within one "time step" of the MWEG, two states that share a common ancestor are *branchially connected*. The branchial graph records this. The branchial distance is supposed to play the role of quantum distance in Gorard's program.

**Causal graph of the MWEG.** Not a single causal graph — a family. Each single-way path through the MWEG gives its own causal graph.

## 2. Where Gorard actually works in single-way mode

Scanning his four main papers:

| Paper | Section | Mode |
|---|---|---|
| G1 (2004.14810) §2.1 basic formalism | defines both | but illustrations and all later §2.3 / §2.4 / §3 arguments are single-way |
| G1 §2.2 Church–Rosser / causal invariance | **defined multi-way** ("all causal graphs isomorphic regardless of updating order") | the MWEG is implicit |
| G1 §2.3 ADM / foliations / hypersurfaces | **single-way** (a single causal graph, many foliations of it) |
| G1 §2.4 discrete Lorentz | **single-way** (transformations between foliations of one causal graph) |
| G1 §3.1 Ollivier–Ricci on spatial hypergraph | **single-state** (one spatial hypergraph snapshot) |
| G1 §3.2 discrete Riemann/Ricci tensor | **single-state + single-way** |
| G1 §3.3 discrete Einstein equations | **single-way** (asymptotic dim preservation of *the* causal graph) |
| G2 (2011.12174) §4 causal-set link | single-way — a specific evolution produces a causal set |
| G2 §5 discrete-geometry / tube / EFE | single-way (copies of G1 §3) |
| G3 (2102.09363) §1–§3 CCZ4 on mesh | single-state (a mesh at one time) — the hypergraph is a fluctuating mesh, not a multiway object |
| G3 §4–§5 Benincasa–Dowker + EFE | **Poisson-sampled single causal set** — not multiway at all; samples a known manifold |
| G3 §6 null tetrad + gravitational waves | **continuum numerical relativity** — lives entirely off the hypergraph |
| G4 (2303.07282) | single-way; inherits from G3 |

**The pattern:** causal invariance is *defined* multi-way, but every *use* of it is single-way. Every empirical and numerical claim in the corpus is about a single causal graph, never about the family of causal graphs produced by the MWEG.

## 3. Why this is inconsistent

Causal invariance means "all updating orders produce isomorphic causal graphs." To verify or use this property you need the MWEG: pick two paths, compare the two causal graphs. You need the multi-way view to even *state* what is being claimed.

Once you have causal invariance, it ceases to matter which path you pick — every path gives the same causal graph. From that point on, single-way reasoning is rigorous. But you have to *first* verify causal invariance, which requires enumeration of paths.

**Gorard never verifies causal invariance** for any of his "derivation" rules — it is asserted, sometimes as a hypothesis of a claim ("for any causal-invariant rule …") and sometimes as a fact. Without verification, single-way reasoning about invariants is incomplete.

**This is why it is strange he uses single-way throughout:** either he is relying on the yet-unverified hypothesis that his rules are causal-invariant (making his reasoning conditional on an unproven premise), or he is implicitly conflating single-way and multi-way behaviour (making his conclusions unsupported).

## 4. Does our single-way refutation still refute him?

**Yes, because our refutations are either structural (independent of update order) or literature-based (independent of discrete dynamics entirely).**

| Refutation | Type | Multi-way sensitivity? |
|---|---|---|
| **S1 #1 — Ollivier $R$ vs $\mathrm{Ric}(v,v)$** | contradicts Ollivier's published theorem | NONE — the error is about the *continuum side*, not the discrete dynamics |
| **S1 #2 — Tube coefficient** | contradicts Gray's tube formula | NONE — continuum-side |
| **S2 #3–#6 — Ill-defined discrete action / variation / orthonormality / $\varepsilon=\delta=1$** | undefined objects | NONE — holds in any update-ordering mode |
| **S3 #7–#9 — Tautologies** | restatements of definitions | NONE — they're tautological in any framing |
| **S4 #10–#12 — Unsupported bridge claims** | unproven conjectures | Benincasa–Dowker hypothesis is about Poisson-sampling, not about Wolfram dynamics per se |
| **S5 #13 — Named rule is 1-dimensional** | structural: $|LHS|=|RHS|$ ⇒ edge conservation ⇒ linear cone growth | **ROBUST**: edge conservation holds for *every* update order; linear cone growth bound follows without picking an order |
| **S5 #14 — $N(r)$ by analogy** | not derived from convergence theorem | NONE — "by analogy" is rhetorical, not scheduler-specific |
| **S6 #15–#16 — Claims not delivered in the body** | title/abstract-level | NONE |

So of 16 distinct errors: zero depend on single-way vs multi-way.

**Specifically for Error #13 (1D causal graph):** the causal graph's edge-count $|E_{cg}|$ with multi-count convention is bounded by $k \cdot m$, where $k$ is |LHS| and $m$ is the number of events. Each event has in-degree $k$. The state size is constant $N$, so in any *greedy parallel schedule* of the causal DAG each layer has $\le \lfloor N/k\rfloor$ events. This is the parallel-layer bound, and it is provable from $|LHS|=|RHS|$ alone.

**Honest caveat (corrected 2026-04-19):** the parallel-layer bound does NOT directly imply that the BFS cone of radius $t$ from any source has size $O(t)$. An event in the BFS cone can have arbitrarily high parallel-level via long alternate paths, so the cone is not contained in a contiguous band of parallel layers. The empirical *linear* cone growth we measured for the named rule on the tested seeds is rule-and-seed-specific structure (multiple paths merge in a way that keeps the cone narrow); it would require a rule-specific induction to prove formally, not a structural theorem about all conservative rules.

To be explicit: if I wanted to rescue the named rule by changing schedulers, I'd need to produce a scheduler that makes the *total* edge count grow. No such scheduler exists, because total edge count is conserved per event. Multi-way evolution would produce many branches each of whose causal graphs is linear — more *states* but not higher *dimension* per branch.

## 5. The null tetrad, vierbein, spin connection — where they actually live

The reader wanted a clear statement. Here it is.

### 5a. What the null tetrad is

In continuum (smooth Riemannian or Lorentzian) geometry: a **tetrad** (or *vierbein*, *frame field*) at a point $p$ of a pseudo-Riemannian 4-manifold is a basis $\{e_0, e_1, e_2, e_3\}$ of the tangent space $T_pM$ satisfying $g(e_a, e_b) = \eta_{ab}$ (Minkowski metric). A **null tetrad** is an equivalent basis $\{\ell, n, m, \bar m\}$ with $\ell, n$ real null vectors and $m$ complex, satisfying $\ell \cdot n = -1$, $m \cdot \bar m = 1$, all other inner products zero.

Newman-Penrose formalism decomposes the Riemann and Weyl tensors into scalar components ($\Psi_0, \ldots, \Psi_4$) using this null tetrad. $\Psi_4$ encodes outgoing gravitational radiation.

### 5b. What a tetrad needs, pre-requisites

- A smooth manifold $M$.
- A pseudo-Riemannian metric $g$ (so that orthonormality is meaningful).
- A tangent space $T_pM$ at each point.
- A connection (Levi-Civita) so that "null" can be defined using the metric.

### 5c. On a pure Wolfram-model hypergraph

A hypergraph has:
- A discrete vertex set and a set of directed hyperedges.
- No vector space structure at vertices.
- No "tangent space" — the natural discrete substitute would be "the set of edges incident at $v$," which is a set, not a vector space.
- No metric beyond graph distance.

**A null tetrad cannot be constructed intrinsically on a hypergraph, because there is no tangent space on which to erect it.**

The tetrad of the papers appears only in G3 §6, built from the 3D-metric that CCZ4 numerically evolves on a hypergraph grid (the hypergraph serves only as an adaptive mesh). See `notes/null_tetrad_resolution.md` for the line-by-line trace.

### 5d. What could substitute on a hypergraph?

There is an honest research question here: can you replace the tetrad by a combinatorial object playing a similar role in a continuum limit?

Candidates (none worked out rigorously):
- **Edge labeling** — assign each hyperedge one of four "flavour" labels, intended to approximate the four tetrad directions. Problem: no canonical choice.
- **Orthogonal-frame bundle approximation** — if a hypergraph has a well-defined continuum limit as a smooth manifold (big IF — see §4 above), the limiting frame bundle could be inferred. But this requires the convergence theorems in `notes/limit_toolkit.md` that are not in the literature.
- **Null-direction-as-light-cone-edge** — the causal graph's directed edges *are* in some sense "null" (light-cone-like). One could call certain pairs of edges "orthogonal null pairs." This is a rhetorical choice, not a constructive one.

No author has produced a definitive construction. Our refutation of Gorard's tube formula (S1 #2) strikes at the nearest thing to a "hypergraph analog of a Riemannian tube," where he does attempt a discrete-continuum bridge — and gets the coefficient wrong.

### 5e. The broader GR machinery (connection, curvature tensor, Jacobi fields)

Same pattern as the tetrad:
- **Connection** needs a tangent space — not available on hypergraphs.
- **Parallel transport** Gorard *does* attempt in G1 §3.2 by "declaring non-parallel edges orthonormal" (S2 #5) — this is the fiat orthonormality move, not a construction.
- **Riemann curvature tensor** needs the connection — same obstacle.
- **Jacobi fields** need the connection and the tangent bundle — same obstacle.

**The honest summary:** every piece of GR machinery that requires a tangent bundle does not have a hypergraph analog. The pieces that work on metric-measure spaces (distance, Ollivier–Ricci, ball volume) do transplant. Everything beyond metric-measure-space geometry requires the continuum-limit bridge that has not been built.

## 6. What would a genuine multi-way formalization require?

If we wanted to rescue Gorard's framework in a way that a skeptical reader would accept:

1. **Define the discrete metric $g$ on the causal graph.** Not just declare it exists; specify its components $g_{ab}$ as functions of the causal-graph structure. Until this is done, every use of $g$ is ill-defined.
2. **Define $\delta/\delta g^{ab}$ on a discrete state.** Specify a notion of "varying a component of the discrete metric" that reduces to the continuum functional derivative in an appropriate limit. Γ-convergence of discrete-to-continuum variational problems (Braides; Alicandro–Cicalese) is the right machinery.
3. **Verify causal invariance multi-way for concrete rules.** For any rule claimed to derive GR, actually enumerate the MWEG and check that all paths produce isomorphic causal graphs. SetReplace cannot do this alone; `efficient_rewriting_final/` is closer to capable.
4. **Prove the continuum limit exists.** State it as "the sequence of causal graphs from iterated application of rule $R$ from seed $s_0$, with edge length $\varepsilon_n \to 0$, GH-converges to a Lorentzian manifold $(M, g)$." No such convergence theorem exists for any Wolfram-model rule.
5. **Replace the fiat orthonormality and the $\varepsilon=\delta=1$ asymptotic with rigorous arguments.** Either use a sequence with $\varepsilon_n \to 0$, or provide a non-asymptotic Ollivier–Ricci construction.
6. **Decide what happens on non-causal-invariant rules.** The entire framework assumes causal invariance. For a generic rule, the multiway produces many inequivalent causal graphs and the "continuum limit" would be a family, not a single manifold. The branchial structure would then be load-bearing.

Items 1 and 4 are the most serious. Each is a research project, not a paper-revision.

## 7. Bottom line for a new reader

- Gorard's *definitions* of causal invariance and general covariance are multi-way, but his *arguments* are almost always single-way, and causal invariance is never verified for any specific rule.
- Multi-way machinery (MWEG, branchial graph) is present in the corpus as a feature-set, but not deployed where the load-bearing arguments are made.
- **Our empirical refutation (the named rule is 1-dim) uses a single-way SetReplace run + a single-way Python re-implementation, and the result is multi-way-robust because it is structural**: $|LHS| = |RHS|$ ⇒ conservation law ⇒ bounded cone growth.
- **Our continuum-side refutations (S1 errors) are independent of single-way vs multi-way entirely**; they are bugs in Gorard's statement of Riemannian-geometry theorems.
- **The null tetrad, connection, parallel transport, curvature tensor — none live on a hypergraph**; Gorard's claims on them pertain either to an ambient continuum metric (G3 §6) or to hypergraph surrogates that fail the needed properties (S2 #5 fiat orthonormality).
- A genuine hypergraph-to-GR derivation would require §6's six items — none of which Gorard's corpus provides.

If the user's multi-way engine (`efficient_rewriting_final/`) is used for a future pass, the verifications it *adds* are causal-invariance checks for specific rules, branchial-structure computations, and enumeration of inequivalent causal graphs. None of these changes the refutations we already have.
