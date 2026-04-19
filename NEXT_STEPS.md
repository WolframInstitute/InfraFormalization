# Next steps — what's done, in flight, and waiting

Lives next to [`README.md`](README.md) / [`INDEX.md`](INDEX.md) / [`FINDINGS.md`](FINDINGS.md). Curated by hand.

## Done ✓

All of these are archived under `notes/` and `results/` and linked from [`INDEX.md`](INDEX.md).

- [x] Close-reading of all three main papers (G1, G3, G4). [`notes/*_close_reading.md`](notes/).
- [x] Close-reading of the causal-set paper (G2) sufficient to confirm the repeated errors. [`notes/corpus_audit.md`](notes/corpus_audit.md).
- [x] Full claims catalog for G1 (184 rows). [`notes/claims_catalog.md`](notes/claims_catalog.md).
- [x] Phase 1A self-audit: independent Python rewriter agrees with SetReplace on 9 seeds. [`results/phase1_selfaudit/`](results/phase1_selfaudit/).
- [x] Phase 2B audit of tube-volume coefficient (Eq 342): 4-rail refuted. [`results/phase2_continuum/eq342_verdict.md`](results/phase2_continuum/eq342_verdict.md).
- [x] Phase 2C audit of Ollivier Wasserstein (Eq 344): structural refutation against Ollivier's cited theorem. [`results/phase2_continuum/eq344_verdict.md`](results/phase2_continuum/eq344_verdict.md).
- [x] Empirical refutation of the named "EFE-satisfying" rule: 1-dim causal graph on every seed. [`notes/empirical_refutation.md`](notes/empirical_refutation.md).
- [x] Severity taxonomy S1–S6 with 16 distinct errors. [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md).
- [x] Cross-paper corpus audit showing errors repeated verbatim. [`notes/corpus_audit.md`](notes/corpus_audit.md).
- [x] Single-way vs multi-way explainer + null tetrad resolution. [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md).
- [x] Lean skeleton with Conservation theorem proved (modulo Mathlib build). [`lean/InfraFormalization/`](lean/InfraFormalization/).
- [x] Project-wide navigation: [`INDEX.md`](INDEX.md), [`GLOSSARY.md`](GLOSSARY.md), [`FINDINGS.md`](FINDINGS.md).

## In flight 🛠

- [x] ~~Lean build against Mathlib to verify `Conservation.size_result_of_conservative`.~~ **Done.** Full `lake build` succeeds on 1687 jobs; Theorem A (edge conservation) and its trajectory corollary are machine-verified by Lean 4 + Mathlib 4.29.1.

## Ready to pick up — awaiting user direction

### A. Extend the Lean formalisation

Honest sizing: ★★★ = days/weeks, ★★ = day, ★ = a few hours.

- [ ] ★★ **Parallel-layer bound (Theorem B'):** for a conservative rule, each layer of the greedy-parallel schedule of the causal DAG has ≤ ⌊N/k⌋ events. This is the *correct* version of the antichain argument — bounds parallel layers, not arbitrary antichains and not BFS cones. Proof requires formalising greedy parallel schedules and state invariants. Real Lean theorem, no `sorry`.
- [ ] ★★★ **Linear cone bound for the named rule on tested seeds (Theorem B''):** rule-specific induction. Takes a long time per rule. Pays off only for one specific rule.
- [ ] ★★ **In-degree exactly $k$ (Theorem B'''):** every event in the causal graph of a conservative rule has exactly $k$ causal in-edges (multi-counted). Trivial from definitions but useful as a building block.
- [ ] ★★★★ **Cycle-to-circle Gromov–Hausdorff convergence:** $C_n$ scaled by $1/n$ → $S^1$. The simplest non-trivial continuum-limit theorem we could state. Requires Mathlib's GH API + explicit ε-isometry construction. ~100–300 lines.
- [ ] ★★★★★ **Correct Ollivier identity in Mathlib:** $\kappa = \varepsilon^2 \mathrm{Ric}(v,v)/(2(d+2)) + O(\varepsilon^3)$ formalised against Mathlib's Riemannian geometry + optimal transport. Multi-week project; would be a substantial Mathlib contribution.
- [ ] ★★★★★ **Correct Gray tube formula in Mathlib:** $V(T_\varepsilon(\gamma)) = \omega_{d-1}\varepsilon^{d-1}L(1 - \varepsilon^2(R+\mathrm{Ric}(u,u))/(6(d+1)) + O(\varepsilon^4))$. Requires Fermi normal coordinates infrastructure that Mathlib doesn't fully have.
- [ ] ★★★★ **MWEG + branchial structure:** define formally so causal invariance can be stated as a theorem-target (not a hypothesis). Useful but doesn't prove anything yet.

### B. Honest claims-correction sweep

- [x] ~~"Linear cone growth follows from conservation"~~ — corrected in `FINDINGS.md` and `empirical_refutation.md` (2026-04-19): conservation implies parallel-layer width bound, NOT linear BFS-cone growth. The empirical 1D-cone observation for the named rule is rule-and-seed-specific, not a structural consequence.
- [ ] Sweep `notes/severity_taxonomy.md` for any S5 claim that overstates "structural" — none should claim more than "conservation ⇒ state-size preservation, plus rule-specific empirical confirmation that the named rule is 1D on tested seeds."
- [ ] Sweep `notes/singleway_vs_multiway.md` table where it says "edge conservation ⇒ linear cone growth" — this needs the same correction.

### C. What we genuinely *can* claim about conservation

After the corrections, the firm Lean-verified claim is just **edge conservation (Theorem A)**, plus the empirical observation that the named rule is 1D on every tested seed. Neither alone refutes Gorard's headline "EFE in continuum limit" claim; *together* they refute it for the specific rule he names, on the seeds tested. That's a smaller (but still real) refutation than I was implying earlier.

### B. Phase 3 — discrete-side audits
- [ ] Numerical verification of Gorard's discrete Ollivier–Ricci formula (G1 Def 33 with the specific $\mu_{A^{in}}, \mu_{B^{out}}$) on Figures 66/67/68's hypergraphs: does it give the sign Gorard claims? Does the magnitude match?
- [ ] Re-compute the Benincasa–Dowker action on a Poisson sample of Schwarzschild via the Cunningham-style numerical protocol; compare to the continuum Einstein–Hilbert action. This is a replication of causal-set-theory convergence, not Wolfram-model-specific.

### C. Phase 4 — bridge-claim formalisation
- [ ] Write up the precise theorem that G1 §3.3 would *need* to state, with all hypotheses made explicit: Γ-convergence / GH convergence / spectral convergence of the discrete EH action to the continuum one. Identify which pieces exist in the literature (e.g. Benincasa–Dowker convergence conjecture) and which do not.
- [ ] Produce a toy counterexample: a rule whose causal-graph evolution is demonstrably *not* GH-close to any manifold, even though the rule happens to be causal-invariant. This would show that "causal invariance" alone is insufficient for a manifold-like limit.

### D. Positive program — our own contribution
- [ ] Theorem target: for random-geometric-graph samples from a Riemannian manifold with proximity edges at scale $\varepsilon$, the discrete Ollivier–Ricci converges to directional $\mathrm{Ric}(v,v)$ as the sample size $\to \infty$ and $\varepsilon \to 0$ at matched rates. (Trillos–Slepčev-style, but specifically for $\kappa$.) This is a *positive* result linking discrete to continuum geometry — the opposite of the Gorard-style overclaim. Formalisable in Lean given Mathlib's optimal-transport + differential geometry.
- [ ] Cross-check against `efficient_rewriting_final/`'s multi-way engine: verify causal invariance of simple rules computationally (which SetReplace alone cannot do).

### E. Publication / external communication
- [ ] Draft a short "technical comment" PDF summarising the S1–S6 findings, suitable for circulation to the Wolfram Institute (internal) or for public critique (arXiv). Evidence-backed, with links to this project.
- [ ] Decide whether to frame as "corrected derivations of what Gorard's papers should have said" (constructive) or as "report of specific errors" (critical), or both.

## Waiting on decisions

Before continuing, your input would resolve:
- **Priority**: Lean depth (A) vs new audits (B, C) vs positive program (D) vs external communication (E)?
- **Scope of Lean theorem targets**: just the Wolfram-model structural theorems (conservation + bounded cone), or also the corrected continuum identities (Ollivier directional Ricci, Gray tube formula)?
- **MWEG / branchial verification**: invest in hooking up `efficient_rewriting_final/` for causal-invariance checks?
- **Publication**: draft a short comment-PDF now, or wait until Lean proofs are in?
- **Positive program scope**: ambitious (Trillos–Slepčev-for-Ollivier in Lean) vs modest (numerical reproduction of Benincasa–Dowker convergence on Schwarzschild)?
