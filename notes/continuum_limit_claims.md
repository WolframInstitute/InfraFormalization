# JGORARD's continuum-limit claims — exhaustive catalog

Every claim in the JGORARD corpus that asserts *convergence to, emergence of, or
equivalence to a continuum geometric/physical object*. Organised by paper and by
type. For each: verbatim quote (TeX line reference), claimed continuum object,
proof status in the paper, and our audit status.

Status key:
- ✅ genuine standard fact (correctly cited; not a JGORARD contribution).
- ✗ mathematically wrong.
- ⊘ tautology (rewrites a definition as a limit claim).
- ⚠ ill-defined (limit invoked without specifying topology / convergence sense / target object components).
- ○ open conjecture (from the cited literature, still unresolved).
- 🧨 load-bearing for the headline program: if unresolved, the "derivation of GR" fails.

## G1 — arXiv:2004.14810

### §Abstract (TeX 22)

**Quote.** "rigorous mathematical derivations of many key properties of such models in the continuum limit, as first discussed in NKS, including the fact that large classes of them obey discrete forms of both special and general relativity."
**Continuum object.** Special + general relativity on smooth Lorentzian manifolds.
**Our status.** ⚠🧨 Aspirational umbrella claim. No single "continuum limit" is formally defined in-paper. See §3.3 specifics below.

### §3.1 — ball-growth (TeX 599–605)

**Claim (Eq 47 / line 599).** Riemannian ball-volume expansion
$$\mathrm{Vol}(B_\varepsilon(p))/\mathrm{Vol}(B_\varepsilon(0) \subset \mathbb{R}^n) = 1 - R\varepsilon^2/(6(n+2)) + O(\varepsilon^4)$$
as $\varepsilon \to 0$.
**Continuum object.** Riemannian scalar curvature.
**Our status.** ✅ Standard (Gray 1973). Not a JGORARD contribution; quoted correctly from the literature.

**Claim (Eq 48 / line 604).** Parallel-transport W distance between two $\varepsilon$-balls
$$W(B_\varepsilon(p), B_\varepsilon(q)) = \delta(1 - \varepsilon^2 R/(2(n+2)) + O(\varepsilon^3 + \varepsilon^2 \delta))$$
as $\varepsilon, \delta \to 0$, where $\delta = d(p, q)$.
**Continuum object.** Ricci scalar $R$ (as stated).
**Our status.** ✗🧨 Contradicts the cited Ollivier JFA 2009 theorem, which has *directional* $\mathrm{Ric}(v,v)$, not scalar $R$. Off by a factor of 2 on $S^2$. See [`results/phase2_continuum/eq344_verdict.md`](../results/phase2_continuum/eq344_verdict.md).

**Claim (Eq 55 prose, line 637).** "In the particular case in which $(X,d)$ is a Riemannian manifold, … the Ollivier-Ricci scalar curvature $\kappa(p,q)$ reduces (up to some arbitrary scaling factor) to the standard Riemannian Ricci scalar curvature $R(p,q)$."
**Continuum object.** Scalar Ricci.
**Our status.** ✗ Mislabels Ollivier's theorem (again). The reduction is to *directional* Ricci, not scalar. "$R(p,q)$" is not a standard object.

**Claim (Eq 65 / line 747).** Discrete $N(r) = ar^n(1 - R r^2/(6(n+2)) + O(r^4))$ on hypergraphs.
**Continuum object.** Scalar Ricci (Ollivier-style).
**Our status.** ⚠🧨 Written "by analogy" with the Riemannian formula (Eq 47/343). No convergence theorem is proved. The applicability at discrete edge length $r = 1$ is a category error (S2 #6). See [`notes/2004.14810_close_reading.md`](2004.14810_close_reading.md).

### §3.2 — spacetime curvature (TeX 812–871)

**Claim (Eq 76 / line 813).** Volume-element expansion
$$d\mu_g = [1 - R_{jk} x^j x^k / 6 + O(\|x\|^3)] d\mu_{\text{Euclidean}}$$
in geodesic normal coordinates.
**Continuum object.** Ricci tensor.
**Our status.** ✅ Standard (Taylor expansion of $\sqrt{\det g}$). Not a JGORARD contribution.

**Claim (Eq 84 / line 871).** Discrete cone-growth
$$C(t) = a t^n [1 - R_{jk} t^j t^k / 6 + O(\|t\|^3)]$$
for a discrete causal graph.
**Continuum object.** Ricci tensor timelike projection.
**Our status.** ⚠🧨 Asserted "by direct analogy" (line 865). No convergence theorem. Needs the fiat orthonormality (S2 #5) and $\varepsilon = \delta = 1$ asymptotic abuse (S2 #6) to interpret.

### §3.3 — Einstein field equations (TeX 882–990)

**Claim 1 (Eq 86 / line 888).** Discrete dimension-anomaly action
$$S[g^{ab}] = \sum d\mu_g R$$
**Continuum object.** Einstein–Hilbert action $\int d^4 x \sqrt{-g} R$.
**Our status.** ⚠🧨 Ill-defined. "$g^{ab}$" and "$d\mu_g$" on a discrete state are never constructed; "$\sum$" has no specified domain.

**Claim 2 (Eq 87 / line 892).** "Asymptotic dimensionality preservation" = $\delta S[g^{ab}]/\delta g^{ab} \to 0$.
**Continuum object.** Euler–Lagrange equation of the EH action.
**Our status.** ⊘🧨 The condition is the conclusion of the variational argument in disguise. $\delta/\delta g^{ab}$ on a discrete state is never defined. See S3 #9.

**Claim 3 (Eq 88 / line 898).** "In the continuum limit of an arbitrarily large causal graph, this sum becomes (subject to a weak ergodicity assumption on the dynamics of the causal graph) an integral."
$$S[g^{ab}] = \int d^4 x \sqrt{-g} R$$
**Continuum object.** Einstein–Hilbert action.
**Our status.** ○🧨 This is the **central bridge claim**. Neither "becomes" (which topology? Γ-convergence? pointwise?) nor "weak ergodicity" (precise definition?) is specified. The closest rigorous statement in the literature is the Sorkin–Benincasa–Dowker conjecture for Poisson-sampled causal sets, which is *still open* in causal-set theory. See [`notes/limit_toolkit.md`](limit_toolkit.md).

**Claim 4 (Eq 91 / line 913).** Vacuum Einstein field equations $R_{ab} - \tfrac{1}{2} R g_{ab} = 0$.
**Continuum object.** Einstein's equations.
**Our status.** 🧨 Headline result. Inherits ✗ / ⚠ / ○ from dependencies above. The standard continuum variation (Hilbert 1915) is correct; the chain *to* it from the discrete action is not. The conditional "if a continuum limit exists in which the causal graph becomes a Riemannian manifold" (line 914) carries the entire burden.

**Claim 5 (Eq 92 / line 920).** "In the continuum limit and in the absence of any non-gravitational forces," test particles obey the geodesic equation.
**Continuum object.** Relativistic geodesic equation.
**Our status.** ⚠🧨 Inherits from Claim 4; "test particles" in a hypergraph are "nonplanar tangles" (identification via Kuratowski, never made rigorous).

**Claim 6 (Eq 97 / line 954).** Full Einstein field equations $R_{ab} - \tfrac{1}{2} R g_{ab} = 8\pi T_{ab}$.
**Continuum object.** Non-vacuum Einstein equations.
**Our status.** ⚠🧨 Requires a matter Lagrangian on the hypergraph (line 949) that is never constructed.

**Claim 7 (Eq 102 / line 988).** Einstein equations with cosmological constant $\Lambda$.
**Continuum object.** Einstein equations with $\Lambda$.
**Our status.** ⚠ $\Lambda$ appears as an integration constant of the variational derivation. Conditional on Claim 4.

**Claim 8 (Eq 109 / line 1027).** Chapman–Enskog analogy: the discrete cone-growth function $C(t)$ plays the role of a "distribution function" in a hydrodynamic expansion, recovering Ricci (zeroth order) + Weyl (first order).
**Continuum object.** Navier–Stokes / Burnett hierarchy, by analogy to GR.
**Our status.** ⚠ Analogy, not derivation. Interesting intuition; asserted as if it had been made rigorous.

### §3.4 — cosmology (TeX 1051+)

**Claim.** Under variable-dimensionality hypergraphs, an "inflation-like" solution to the horizon and flatness problems emerges.
**Continuum object.** FLRW with variable $n$ (scale relativity).
**Our status.** ⚠ Standard FLRW analysis applied to the hypothetical variable-$n$ regime; the "hypergraph with variable dimensionality" is itself not formally constructed.

---

## G2 — arXiv:2011.12174 (Algorithmic Causal Sets and the Wolfram Model)

Reprises the G1 continuum-limit machinery and adds causal-set-theory material (Sorkin / Benincasa / Dowker).

### Repeated from G1

- **Eq 124 (line 1103).** Riemannian ball-volume expansion — ✅ standard, correctly stated.
- **Eq 126 (line 1165).** Tube-volume expansion — ✗ same wrong coefficient as G3 Eq 342; see S1 #2.
- **Eq ~165 (line 1668).** Parallel-transport W distance — ✗ same scalar-$R$ error as G1 Eq 48; see S1 #1.
- **Prose (line 1699).** "the Ollivier-Ricci scalar $\kappa(p,q)$ reduces to the ordinary Riemannian Ricci scalar $R(p,q)$" — ✗.
- **Eq (line 1882).** Direction-averaged W recovers scalar $R$ — ✗ same error, third instance in G2.

### New to G2

**Claim.** Discrete d'Alembertian $B^{(d)}_\rho$ on a causal set. Expected value (under Poisson sampling at density $\rho$) satisfies
$$\mathbb{E}[B_\rho^{(d)} \phi] \to \Box \phi - \tfrac{1}{2} R \phi$$
as $\rho \to \infty$, in Riemann normal coordinates.
**Continuum object.** Box operator + Ricci scalar.
**Our status.** ✅ Genuine result (Benincasa–Dowker 2010), correctly imported. Not a JGORARD contribution.

**Claim.** $\phi \equiv 1$ specialisation yields
$$\mathbb{E}[S_{\mathrm{BD}}(C)] \to -\tfrac{1}{2} \int \sqrt{-g} R \, d^d x$$
as $\rho \to \infty$ with additional assumptions (zero surface terms, non-local cutoff).
**Continuum object.** Einstein–Hilbert action (up to constant).
**Our status.** ○🧨 **The Sorkin–Benincasa–Dowker conjecture in causal-set theory.** Cited as numerically demonstrated (Cunningham 2018). *Open* analytically. This is the best-supported continuum-limit claim in the entire corpus, but it is not JGORARD's — it's causal-set theory, still open there.

**Claim.** Wolfram-model causal graphs, under a weak ergodicity assumption, can be interpreted as Poisson-sampled causal sets of some continuum spacetime.
**Continuum object.** Causal set embedding.
**Our status.** ⚠🧨 The bridge from Wolfram-model *rewriting dynamics* to Poisson-sampling statistics has no proof. Any rule in the Wolfram-model zoo could in principle produce non-Poisson statistics; no theorem guarantees Poisson behaviour.

---

## G3 — arXiv:2102.09363 (Hypergraph Discretization of the Cauchy Problem)

### Abstract

**Claim.** "a hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit."
**Continuum object.** EFE on a Lorentzian manifold.
**Our status.** ✗🧨 The "provably" reduces to the Benincasa–Dowker causal-set conjecture (above), with a Poisson-sampling hypothesis replacing Wolfram dynamics (line 6080 verbatim). For the specific named rule (line 6202), the measured cone-growth exponents are 0.985 to 1.256 on small seeds, and no bound is proved. See [`notes/empirical_refutation.md`](empirical_refutation.md).

### §3–§4 — CCZ4 / BSSN

**Claim.** Standard numerical-relativity CCZ4 / BSSN reformulation of the Einstein PDEs, solved on an adaptive hypergraph mesh, converges to smooth Lorentzian spacetimes (Schwarzschild, Kerr, binary-merger).
**Continuum object.** Specific Lorentzian metric solutions.
**Our status.** ✅ Standard numerical relativity. Not a Wolfram-model convergence result — the hypergraph is the adaptive mesh, not the source of dynamics.

### §5 — discrete curvature (TeX 2579–2816)

Direct repeats of G1 §3 formulas with the same Ricci-directional/scalar error pattern.

- **Eq 340 / line 2597.** Ball volume — ✅ standard.
- **Eq 342 / line 2607.** Tube volume — ✗ **wrong coefficient** (see S1 #2; factor 2 off on $S^2$, factor 6 on $S^3$).
- **Eq 343 / line 2621.** Ball-volume ratio — ✅ standard.
- **Eq 344 / line 2626.** Parallel-transport W distance — ✗ **scalar-$R$ error** (see S1 #1).
- **Eq 384 / line 6088.** Causal-set action $S^{(4)}(C) = (4/\sqrt 6)[n - N_0 + 9N_1 - 16N_2 + 8N_3]$.
**Continuum object.** Continuum EH action.
**Our status.** ○🧨 The Benincasa–Dowker conjecture again. Convergence is cited, not proved.
- **Eq 387 / line 6120.** $\lim_{\rho_c \to \infty} [\ldots] = S_{\mathrm{EH}}(g)$ — ○🧨 stated; conjecturally true in causal-set theory; never proved.

### §6 — gravitational wave extraction (TeX 3950+)

**Claim.** Newman–Penrose scalar $\Psi_4$ extracted via null tetrad, time-integrated to give gravitational-wave strain $h_+ - i h_\times$.
**Continuum object.** Outgoing gravitational radiation.
**Our status.** ✅ Standard numerical relativity. The null tetrad lives on the *continuum metric* that CCZ4 numerically evolves — *not on the hypergraph*. See [`notes/null_tetrad_resolution.md`](null_tetrad_resolution.md).

### §7 — validation numerics

**Claim.** Numerical evolution converges at 4th order to Schwarzschild / Kerr / binary-BH merger.
**Continuum object.** Specific Kerr / Schwarzschild solutions.
**Our status.** ✅ Validation of the PDE solver, not of Wolfram-model dynamics.

### The critical swap (TeX ~6080)

**Quote.** "replacing the assumption of weak ergodicity of the causal graph dynamics with the much stronger assumption of uniform Poisson distribution of the rewrite events, our construction of the discrete Einstein-Hilbert action for Wolfram model systems reduces to the general d-dimensional form of the Benincasa-Dowker action on causal sets."
**Our status.** 🧨 This is the moment Wolfram dynamics is *dropped*. From here on the "derivation" proceeds on Poisson-sampled causal sets in a pre-specified continuum manifold. The "hypergraph rewriting" brand is preserved rhetorically but not mathematically.

### Initial-data construction (TeX ~6152)

**Quote.** The initial hypergraph is constructed by "Poisson distribution, in which the probability of $n$ vertices of $H$ lying within a spatial region of volume $v$ is given by $P_v(n) = (\rho_c v)^n \exp(-\rho_c v)/n!$."
**Our status.** 🧨 The initial data is sampled from the target geometry (lines 6148-6152, 6179), so the comparison does not test the rule from initial data that does not encode the target. See [`notes/2102.09363_close_reading.md`](2102.09363_close_reading.md).

---

## G4 — arXiv:2303.07282 (Non-Vacuum Solutions, Gravitational Collapse, Discrete Singularity Theorems)

### Abstract

**Claim.** "the resulting discrete spacetimes converge asymptotically to either non-rotating Schwarzschild black hole solutions or maximally-rotating (extremal) Kerr black hole solutions."
**Continuum object.** Schwarzschild, Kerr black holes.
**Our status.** ✅ Validation of the CCZ4 numerical solver on hypergraph mesh; *not* a Wolfram-model convergence statement.

### Title promise

**Claim.** "Discrete Singularity Theorems in Wolfram Model Systems."
**Continuum object.** A discrete analogue of Penrose/Hawking singularity theorems.
**Our status.** ✗ (Title-body gap, S6 #15.) Zero discrete singularity theorems are proved or even precisely stated in the body. The conclusions section acknowledges these as future work. See [`notes/2303.07282_close_reading.md`](2303.07282_close_reading.md).

### Raychaudhuri

**Claim.** A discrete analogue of the Raychaudhuri equation.
**Our status.** ✗ Not constructed. Paper acknowledges: "the appropriate discrete analog of the Raychaudhuri equation [is] somewhat non-obvious" (TeX around line 351) and defers construction.

### Asymptotic black-hole convergence

**Claim.** Under appropriate (spherical or axial) symmetry assumptions and massive-scalar-field matter, the numerical evolution converges to Schwarzschild / Kerr.
**Our status.** ✅ Standard continuum GR (Gonçalves–Moss for spherical, Neugebauer–Meinel for axial), numerically validated. Not a discrete-to-continuum theorem of the sort the paper's title implies.

---

## Summary of continuum-limit claim types

| Type | Instances | Status distribution |
|---|---:|---|
| Standard Riemannian formulas correctly quoted | ~15 | ✅ |
| Standard numerical relativity correctly applied | ~8 | ✅ |
| Causal-set theory results correctly imported | 3 | ✅ + 1 ○ |
| Ricci directional/scalar conflation (S1 #1) | 6 (across 3 papers) | ✗ verbatim repeated |
| Tube-formula coefficient error (S1 #2) | 2 | ✗ |
| Ill-defined discrete objects (S2) | 4 | ⚠ across 3 papers |
| Tautologies (S3) | 3 | ⊘ |
| Unsupported bridge to continuum (S4 #10, #11) | ~5 | ○ or ✗ |
| Rule-specific / claim not delivered in the body | 2 | ✗ |

**The load-bearing claims (🧨 marked):** Eq 48 / 344 (Ollivier), Eq 65 ($N(r)$), Eq 84 ($C(t)$), Eqs 86–91 (§3.3 derivation), Eq 92 (geodesic), Eqs 97/102 (matter + $\Lambda$), the Benincasa–Dowker convergence (G2/G3), and the "provably satisfies EFE" claim in G3. Of these, **none** has a rigorous proof in the corpus; they range from formally false (✗) through ill-defined (⚠) and tautological (⊘) to relying on an open causal-set conjecture (○).

**What a careful reader is meant to take from the corpus:** that GR has been derived from hypergraph rewriting. **What has actually been established:** a plausibility narrative with correctly-quoted continuum geometry, an incorrectly-stated discrete Ollivier identity, a Poisson-sampling identification that silently replaces Wolfram dynamics with causal-set theory, and numerical validation that a PDE solver for the Einstein equations runs correctly on a hypergraph mesh. The bridge from one to the other — the actual program — has not been built.
