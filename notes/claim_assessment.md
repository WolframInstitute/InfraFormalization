# Which of Gorard's claims are established, and which are working hypotheses?

This is a synthesis addressing the central question raised by the user: the Wolfram Institute internally doubts Gorard's GR-from-hypergraph-rewriting results; we cannot verify them; is he deceiving, or is he right about a hunch he has not rigorously proved?

The honest answer is **neither**, and both, in different parts of the corpus. Below I break down the claims by type and assign each one to one of four categories:

- **(T) True, proved elsewhere** — a correct mathematical statement, usually imported from causal-set theory or classical differential geometry.
- **(C) Conjectural** — plausibly true, with partial numerical or analytical support, but not proven.
- **(H) Hunch relabeled as theorem** — a plausibility argument that Gorard presents with the rhetoric of a derivation, despite no proof. This category matters most: it involves no invented data, but it blurs the distinction between "I believe" and "I have shown."
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
| B3 | "A hypergraph substitution rule that provably satisfies EFE in the continuum limit" | **H + circular** | The chain (now confirmed by close reading, notes/2102.09363_close_reading.md): (a) cite BD d'Alembertian; (b) replace "weak ergodicity of the Wolfram model" with **uniform Poisson distribution** (line 6080 verbatim) — this drops the Wolfram-model dynamics entirely; (c) invoke Sorkin/BD/Cunningham conjecture ⟨S_BD⟩ → S_EH, under zero surface terms + vanishing far-light-cone tails; (d) **construct the initial hypergraph by Poisson-sprinkling points into the known Schwarzschild / Kerr metric** (line 6152). The spacetime is the *input*, not the output. This is circular. |
| B3' | The specific "rule that satisfies EFE" is `{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}` | **empirically refuted** | Named exactly once (line 6202). We ran it in SetReplace (see `notes/empirical_refutation.md`, scripts in `scripts/`): on small 4-cycle/4-path seeds it halts after 1 firing; on larger cycles/paths it conserves edge count exactly; **causal-graph cone dimension ≈ 1.0** on every seed tested (6-cycle, 8-cycle, 10-path, 20-cycle, figure-8, 3×3×3 grid, 4×4×4 grid, 5×5×5 grid). Structural: `\|LHS\|=\|RHS\|=4` forces edge conservation and a quasi-regular in-degree-4 causal DAG which cannot have polynomial cone growth of exponent > 1. Gorard's §3.3 machinery needs `n=4`. **The rule cannot satisfy EFE in any continuum limit.** |
| B4 | Pure-Wolfram evolution agrees with CCZ4-on-mesh evolution on benchmarks | **numerical only** | ≈2nd-order agreement on Tables 6–7. Agreement is between two discretizations of the *same* pre-specified Schwarzschild/Kerr; does not establish the rule encodes GR. |
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

- **(T) True, proved elsewhere**: B1, B2, B5. These are standard numerical relativity or standard differential geometry. Gorard's contribution is exposition and software integration, not derivation.
- **(C) Conjectural**: B3 (the big one — reduces to the BD conjecture in causal-set theory, with numerical support only).
- **(H) Hunch relabeled as theorem**: A2, A4, A5, A6, A7. These are the heart of 2004.14810's "derivation of GR." Every single one is a plausibility move.
- **(X) Definitionally empty**: A1. Presented as a discovery, but it's a rephrasing.
- **Error**: A3. A genuine misstatement of what Ollivier's theorem says.

## The honest verdict

**The published texts claim more than their arguments establish, and contain no fabricated data.** There is no evidence of invented numerical data or simulation results; the CCZ4-on-mesh validation against Schwarzschild/Kerr is real NR work, and the references to Sorkin/Benincasa/Dowker are correct. What *is* present: circular "derivations" presented as theorems, title/abstract claims that the body does not deliver, load-bearing conjectures cited as established results, and at least one verbatim misstatement of a cited source (the Ollivier scalar/directional error) reused across four papers.

The same steps recur across the papers: the fiat orthonormality assumption, the undefined `g^ab`, the Benincasa-Dowker conjecture treated as a theorem, and the Poisson-sprinkle-and-reconstruct procedure. The papers present plausibility arguments as derivations, open conjectures as theorems, and sample-consistency checks as a proof that the rule "provably satisfies EFE".

**The central "derivation" in 2102.09363 is circular, and this is now unambiguous, and Lean-formalised (`Refutations/F6Circularity.lean`).** The procedure that produces a "hypergraph satisfying the Einstein field equations" is:
1. Pick a target manifold (Schwarzschild, Kerr) known a priori.
2. Poisson-sprinkle vertices into it.
3. Connect nearby vertices.
4. Check that Benincasa–Dowker counting on the result recovers the curvature of (1).
The continuum manifold is the input, not the output. No Wolfram-model rewriting dynamics is used to *generate* the hypergraph — the dynamics is only compared post-hoc against a CCZ4 evolution of the same initial data. This is the kind of check you'd do to validate a mesh, not to derive physics from an underlying computational rule. Describing this as "deriving GR" is an overclaim of the first order.

**Systematic overclaim.** The word "derivation" is used where "plausibility argument" would be accurate. The word "provably" is used where "conjecturally, via a result of Sorkin–Benincasa–Dowker on Poisson causal sets" would be accurate. The phrase "in the continuum limit" is used as if it denoted a single well-defined limit, when in fact it would have to be one of several (GH, Lorentzian-GH, spectral, graphon, Poisson–BD) and Gorard does not commit to one.

**Overclaim extends to paper titles.** The pattern of 2303.07282 is especially revealing: the title and abstract advertise "Discrete Singularity Theorems in Wolfram Model Systems," the body contains neither a discrete Raychaudhuri equation nor a discrete singularity theorem, and Gorard himself concedes in the conclusion that these are future work. The paper delivers standard continuum GR collapse arguments plus numerical validation on a hypergraph mesh; it does not deliver a discrete theorem. A reader who saw only the title would come away with a false picture of the paper's content.

**Hunches that might well be true.** The underlying intuition — that *some* coarse-graining of causal graphs produced by a well-behaved rewriting rule should behave like a Lorentzian manifold satisfying GR — is not crazy. Causal-set theory has been operating on the same intuition since Bombelli–Lee–Meyer–Sorkin 1987, with genuine partial results. Gorard's hunch is in good company; what distinguishes his papers is the rhetoric. He writes as if the results are established when in fact they are inherited from causal-set theory (and still conjectural there) or genuinely new and unproved.

**Why the Institute is right to be skeptical.** Because the papers read like derivations and are cited as if they are. If a Wolfram-Institute colleague asked "has Gorard derived GR?" the honest answer is *no one has*, and what Gorard has done is present a reformulation that (a) imports a causal-set conjecture as if it were a Wolfram-model theorem, (b) treats several plausibility steps as proofs, and (c) contains at least one outright misstatement (A3). The appearance of rigor outruns the substance by a wide margin.

**What this project should do.**
1. Formalize the setup in Lean so that the *gap between what is defined and what is concluded* becomes visible at the type level. This alone will make most of category (H) impossible to state without committing to the missing hypotheses.
2. Import (or wait for) Mathlib's differential-geometry and Lorentz-manifold libraries and state the target theorem (convergence to GR) in full. The resulting unprovable Lean goal **is** the refutation of Gorard's claim in its strong form.
3. State the weakest version of "hypergraph → GR" that one could hope to prove — along the BD line — and either prove it (a real contribution) or show its obstruction.
4. Stay honest in the output: call hunches hunches, call conjectures conjectures, reserve "theorem" for theorems.

The cleanest way to describe what Gorard did, without accusing him of misconduct, is: **he wrote physics-style derivations and called them mathematical ones**. This is an error of register, not of data integrity. It is nonetheless an error that makes the papers unverifiable in the form they are written, which is exactly what the user's colleagues report.
