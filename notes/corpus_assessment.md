# Which of JGORARD's claims are established, and which are working hypotheses?

This is a synthesis addressing the central question raised by the user: the Wolfram Institute internally doubts JGORARD's GR-from-hypergraph-rewriting results; we cannot verify them; is he deceiving, or is he right about a hunch he has not rigorously proved?

The honest answer is **neither**, and both, in different parts of the corpus. Below I break down the claims by type and assign each one to one of four categories:

- **(T) True, proved elsewhere** — a correct mathematical statement, usually imported from causal-set theory or classical differential geometry.
- **(C) Conjectural** — plausibly true, with partial numerical or analytical support, but not proven.
- **(H) Hunch relabeled as theorem** — a plausibility argument that JGORARD presents with the rhetoric of a derivation, despite no proof. This category matters most: it involves no invented data, but it blurs the distinction between "I believe" and "I have shown."
- **(X) Definitionally empty** — a claim whose content is a rephrasing of a definition, presented as a theorem. Not false; just empty.

I mark each major claim from the three most load-bearing papers.

## The claims

### 2004.14810 — "Some Relativistic and Gravitational Properties"

| # | Claim (paraphrased) | Category | Note |
|---|---|---|---|
| A1 | Causal invariance ⇔ discrete general covariance | **X** | Both sides are defined as foliation/update-order independence; the biconditional is tautological by definition. |
| A2 | "Flat hypersurfaces" correspond to inertial frames ⇒ discrete Lorentz covariance | **H** | Uses the speed of light as an axiom (unit edge length = discrete light cone). No propagation result is derived from dynamics. |
| A3 | Ollivier–Ricci κ(p,q) "reduces to Riemannian Ricci scalar R(p,q)" | **Error** | Ollivier's theorem (JFA 2009) says κ recovers **directional** Ricci Ric(v,v), not scalar R. "R(p,q)" is not a standard object. Either a loose paraphrase or a genuine misunderstanding. |
| A4 | Non-parallel hyperedges are "orthonormal" (the fiat) | **H** | Orthonormality requires a bilinear form; none is constructed. The assumption is the geometric content, not a consequence. |
| A5 | Discrete volume-of-ball expansion Vol(B_r) = a r^n(1 − R r²/(6(n+2)) + …) on hypergraph | **H** | Obtained "by analogy" with the Riemannian formula; the analogy is not a convergence proof, and ε = δ = 1 invalidates the asymptotic regime. |
| A6 | δS/δg^ab → 0 gives vacuum Einstein equations in continuum limit | **H** | "δ/δg^ab" is never defined on discrete g. The argument is a rewriting of the EH→Einstein continuum derivation in front of an undefined discrete object. |
| A7 | Chapman–Enskog analogy to discrete molecular dynamics | **H (analogy)** | Presented as proof; actually an analogy. |

### 2102.09363 — "Hypergraph Discretization of the Cauchy Problem"

| # | Claim (paraphrased) | Category | Note |
|---|---|---|---|
| B1 | CCZ4 Einstein-PDE evolution can be run on an unstructured hypergraph mesh | **T** | This is standard numerical relativity with a flexible mesh topology. Not a derivation of GR — a solver for GR. |
| B2 | Gravitational-wave extraction via null-tetrad projection onto numerical Weyl tensor | **T** | Baker–Campanelli–Lousto 2002. Standard. Tetrad lives on the continuum metric, not on the hypergraph. |
| B3 | "A hypergraph substitution rule that provably satisfies EFE in the continuum limit" | **H + sampled initial data** | The chain (now confirmed by close reading, notes/2102.09363_close_reading.md): (a) cite BD d'Alembertian; (b) replace "weak ergodicity of the Wolfram model" with **uniform Poisson distribution** (line 6080 verbatim) — this drops the Wolfram-model dynamics entirely; (c) invoke ⟨S_BD⟩ → S_EH under zero surface terms and vanishing far-light-cone tails, with numerical support from Cunningham; (d) **construct the initial hypergraph by Poisson-sampling points from the Brill-Lindquist initial data** (lines 6148-6152, 6179). The initial data is taken from the target geometry. |
| B3' | The specific "rule that satisfies EFE" is `{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` | **MEASURED, bound OPEN** | First named at line 6202. We ran it in SetReplace (see `notes/empirical_refutation.md`, scripts in `scripts/`): on small 4-cycle/4-path seeds it halts after 1 firing; on larger cycles/paths it conserves edge count exactly; measured cone-growth exponents 0.985 to 1.256 (6-cycle, 8-cycle, 10-path, 20-cycle, figure-8, 3×3×3, 4×4×4, 5×5×5 grids), with SetReplace and Python disagreeing on 8 of 9 shared seeds. `\|LHS\|=\|RHS\|=4` gives edge conservation (PROVED). No bound on cone growth is proved. JGORARD's §3.3 machinery needs `n=4`. |
| B4 | Pure-Wolfram evolution agrees with CCZ4-on-mesh evolution on benchmarks | **numerical only** | ≈2nd-order agreement on Tables 6–7. Agreement is between two evolutions of the same initial data, sampled from the target geometry. Does not establish that the rule encodes GR. |
| B5 | Validation against Schwarzschild / Kerr / binary mergers | **T (as NR validation)** | Real numerical work using CCZ4; but this validates the *PDE solver*, not the derivation of GR from the Wolfram model. |

### 2303.07282 — "Discrete Singularity Theorems"

Close-reading now in `notes/2303.07282_close_reading.md`. **The paper does not contain what its title promises.** Zero labeled theorems / propositions / definitions; the words "shear" and "vorticity" appear zero times in the body; no discrete Raychaudhuri equation, no discrete expansion scalar θ, no discrete energy condition, no discrete stress-energy tensor, no discrete trapped surface is constructed. The "rigorous mathematical analysis" the abstract advertises (lines 453, 4331) is exclusively continuum: WKB expansions for spherical collapse (following Gonçalves–Moss) and Ernst-equation derivations for axial rotating collapse (Neugebauer–Meinel). Both are correct continuum GR, neither is discrete.

| # | Claim (paraphrased) | Category | Note |
|---|---|---|---|
| C1 | Discrete analog of Raychaudhuri equation on causal graphs | **Not delivered** | Promised by title, conceded as open problem in the abstract (lines 38–49) and conclusions (lines 5369–5381). |
| C2 | Discrete singularity theorem (Penrose-like) | **Not delivered** | Same — acknowledged as future work. |
| C3 | Asymptotic convergence to Schwarzschild / Kerr (spherical / axial collapse) | **T (continuum) + numerical validation** | Standard Gonçalves–Moss + Neugebauer–Meinel continuum GR, validated numerically on the CCZ4-on-hypergraph mesh. Correct, but not about hypergraph→manifold convergence. |
| C4 | Ollivier–Ricci scalar substituted into a curved-space Green's-function formula | **H** | §5 substitutes the discrete Ollivier–Ricci scalar into continuum formulas **without proving the substitution is legitimate**. Inherits all three unproved hypotheses from 2004.14810 (causal invariance, weak ergodicity, asymptotic dimension preservation). |

## What pattern does this reveal?

Tabulating:

- **(T) True, proved elsewhere**: B1, B2, B5. These are standard numerical relativity or standard differential geometry. JGORARD's contribution is exposition and software integration, not derivation.
- **(C) Conjectural**: B3 (the big one — reduces to the BD conjecture in causal-set theory, with numerical support only).
- **(H) Hunch relabeled as theorem**: A2, A4, A5, A6, A7. These are the heart of 2004.14810's "derivation of GR." Every single one is a plausibility move.
- **(X) Definitionally empty**: A1. Presented as a discovery, but it's a rephrasing.
- **Error**: A3. A genuine misstatement of what Ollivier's theorem says.

## The honest verdict

**The published texts claim more than their arguments establish, and contain no fabricated data.** There is no evidence of invented numerical data or simulation results — the CCZ4-on-mesh validation against Schwarzschild/Kerr is real NR work, and the references to Sorkin/Benincasa/Dowker are correct. What *is* present in the published corpus:

  * a "provably satisfies" claim whose numerical support starts from initial data sampled from the target geometry (2102.09363 §6, lines 6148-6152 and 6179),
  * title/abstract claims that the body does not deliver (2303.07282 promises discrete singularity theorems and delivers none; the paper's own conclusions concede this),
  * load-bearing conjectures (Sorkin–Benincasa–Dowker) cited in contexts that read as if the conjecture were settled,
  * a verbatim Ollivier-curvature misstatement (scalar where Ollivier's theorem has directional Ric(v,v)) reused across four papers,
  * fiat orthonormality and an undefined discrete metric tensor that carry the weight of the §3.3 "Einstein equations" derivation.

Whether each is "an error of register" or "a deliberate choice" is a question about authorial intent which is outside the mathematical record. What *is* in the mathematical record is that the papers, read literally, do not deliver what the titles and abstracts claim; and that the §6 comparison starts from initial data sampled from the target geometry.

**The pattern is not incidental.** The same fiat orthonormality assumption (G1 §3.2 line 840, reused in G2 §5 and G3 §5), the same undefined discrete `g^ab` (G1 Def 15, reused in G2 §5 and G3 §5), the same treatment of the Sorkin–Benincasa–Dowker conjecture as if it were a settled theorem, and the same Poisson-sprinkle-then-reconstruct procedure recur across four papers over three years. In the published texts, the gap between plausibility argument and derivation, between open conjecture and theorem, between sample-consistency check and "provably satisfies the Einstein field equations" is consistently collapsed in the direction that favours the stronger claim. Whether this is best explained by shorthand, by institutional publication pressure, or by something else is outside the mathematical record; what *is* on the record is the repetition, its direction, and its consequence. The derivations, read as written, are not derivations.

**The §6 comparison in 2102.09363 starts from initial data sampled from the target geometry (READ).** The procedure is:
1. Pick a target initial-data geometry (Brill-Lindquist, line 6179).
2. Poisson-sample vertices into it (lines 6148-6152).
3. Link vertices closer than a cut-off distance whose value is not stated (line 6176).
4. Evolve the hypergraph with the named rule and compare it with the CCZ4 evolution of the same initial data (Figures 73-84, Tables 6-7).
No rewriting rule is used to produce the initial hypergraph. The paper does not run the rule from initial data that does not encode the target geometry. `Refutations/F6Circularity.lean` does not model this procedure (see `STATUS_OF_GORARD_CLAIMS.md`, Claim 2).

**Systematic overclaim.** The word "derivation" is used where "plausibility argument" would be accurate. The word "provably" is used where "conjecturally, via a result of Sorkin–Benincasa–Dowker on Poisson causal sets" would be accurate. The phrase "in the continuum limit" is used as if it denoted a single well-defined limit, when in fact it would have to be one of several (GH, Lorentzian-GH, spectral, graphon, Poisson–BD) and JGORARD does not commit to one.

**Overclaim extends to paper titles.** The pattern of 2303.07282 is especially revealing: the title and abstract advertise "Discrete Singularity Theorems in Wolfram Model Systems," the body contains neither a discrete Raychaudhuri equation nor a discrete singularity theorem, and JGORARD himself concedes in the conclusion that these are future work. The paper delivers standard continuum GR collapse arguments plus numerical validation on a hypergraph mesh; it does not deliver a discrete theorem. A reader who saw only the title would come away with a false picture of the paper's content.

**Hunches that might well be true.** The underlying intuition — that *some* coarse-graining of causal graphs produced by a well-behaved rewriting rule should behave like a Lorentzian manifold satisfying GR — is not crazy. Causal-set theory has been operating on the same intuition since Bombelli–Lee–Meyer–Sorkin 1987, with genuine partial results. JGORARD's hunch is in good company; what distinguishes his papers is the rhetoric. He writes as if the results are established when in fact they are inherited from causal-set theory (and still conjectural there) or genuinely new and unproved.

**Why the Institute is right to be skeptical.** Because the papers read like derivations and are cited as if they are. If a Wolfram-Institute colleague asked "has JGORARD derived GR?" the honest answer is *no one has*, and what JGORARD has done is present a reformulation that (a) imports a causal-set conjecture as if it were a Wolfram-model theorem, (b) treats several plausibility steps as proofs, and (c) contains at least one outright misstatement (A3). The appearance of rigor outruns the substance by a wide margin.

**What this project should do.**
1. Formalize the setup in Lean so that the *gap between what is defined and what is concluded* becomes visible at the type level. This alone will make most of category (H) impossible to state without committing to the missing hypotheses.
2. Import (or wait for) Mathlib's differential-geometry and Lorentz-manifold libraries and state the target theorem (convergence to GR) in full. An unproved Lean goal records what is open. A refutation needs a proof of the negation.
3. State the weakest version of "hypergraph → GR" that one could hope to prove — along the BD line — and either prove it (a real contribution) or show its obstruction.
4. Stay honest in the output: call hunches hunches, call conjectures conjectures, reserve "theorem" for theorems.

The cleanest way to describe what JGORARD did, without accusing him of misconduct, is: **he wrote physics-style derivations and called them mathematical ones**. This is an error of register, not of data integrity. It is nonetheless an error that makes the papers unverifiable in the form they are written, which is exactly what the user's colleagues report.
