# Plan: deep review of Gorard's GR-from-rewriting claims

**Mission.** Examine Gorard's claimed derivation of general relativity from hypergraph rewriting (arXiv:2004.14810, 2102.09363, 2303.07282). For every load-bearing claim: determine *correctness* with *certainty*. Correct claims → formalize in Lean and extend toward an actual discrete-to-continuum geometry theorem. Incorrect claims → document precisely, with counterexample or correct-statement side-by-side, so the error is unambiguous.

## Ground rules (non-negotiable)

1. **Triple-redundant verification for every claim we make.** Any statement of the form "Gorard's Eq N is wrong" requires:
   - **(A)** independent re-derivation from scratch, cross-checked against ≥2 independent references;
   - **(B)** symbolic verification (Mathematica / SymPy);
   - **(C)** numerical test on a nontrivial case where the correct answer is known;
   - **(D)** at least one manually-worked small case.
   If any of (A)–(D) disagree, we stop and find the bug in our own work before concluding anything.
2. **Independent re-implementation for every empirical finding.** If SetReplace says X, we re-derive X in Python from the rule's semantics and check that they agree on ≥ 5 seeds. Any disagreement blocks publication of the finding.
3. **Name the exact line.** Every critique of a claim cites the TeX line / arxiv equation number. No paraphrases without the verbatim quote adjacent.
4. **Separate Gorard-specific claims from imported-from-the-literature claims.** Many "provable" moves in 2102.09363 (Benincasa–Dowker, Ollivier, Gray, Ollivier, ADM) are *imports* of known results. Their correctness is not Gorard's contribution. We judge each on its own terms and note the attribution.
5. **Never conflate "loose rhetoric" with "computational error."** If a claim is a rhetorical overclaim but the equation is correct, note both. If a computation is wrong, prove it.

## Phase 0 — Catalog (prerequisite for everything else)

**Deliverable.** `notes/claims_catalog.md` — every numbered equation, labeled definition, and prose assertion from the three papers, with:
- TeX line / arxiv eqn number.
- Verbatim statement.
- Classification: **DEF** / **LEM-from-lit** / **EQ-continuum** / **EQ-discrete** / **BRIDGE** (discrete↔continuum) / **CONCL** (claimed conclusion).
- Proof status as stated: *proved here / cited / sketched / asserted / asserted by analogy*.
- First-pass verdict + what verification is needed.

This is the spine. Everything in Phases 1–4 references entries in the catalog by ID.

## Phase 1 — Audit our own empirical work (self-verification first)

Before trusting a single of our findings against Gorard, verify our tools.

### 1A. Re-implement the named EFE rule from scratch in Python.
- `scripts/py_rewriter.py`: minimal single-way rewriter operating on multisets of hyperedges, no SetReplace.
- Run on the same 8 seeds used in `empirical_refutation.md`.
- Compare: event count, final state size, causal-graph |V|, causal-graph |E|, cone-growth table C(r).
- **Pass criterion:** exact agreement on event count and state size for all 8 seeds; causal-graph |V|, |E| agree; C(r) within ±2 for $r \le 20$ (may differ slightly due to event-ordering tiebreakers).
- Disagreement → find the bug, do not publish until resolved.

### 1B. Manual trace on the two dead-end seeds.
- Hand-trace 4-cycle → {{2,u},{u,1},{4,1},{1,u}} → check no length-4 chain remains (already done, notes/empirical_refutation.md).
- Hand-trace 4-path similarly.
- Write out the trace in the notes so it's a reproducible witness, not just a claim.

### 1C. Visualize a small causal graph independently.
- For the 6-cycle, 50-event run: export causal graph to GraphViz from SetReplace, separately export from Python re-implementation.
- Diff the edge lists.
- **Pass criterion:** identical up to vertex-renaming.

### 1D. Nail down the cone-growth exponent with a second method.
- Ratio test: $C(2r)/C(r)$ should approach $2^n$ for growth of exponent $n$. If $n=1$, ratio → 2.
- Bootstrap the fit across 10 random-seeded variations (vary the initial condition slightly) and check the exponent is stable.

**Phase 1 delivers a verified empirical claim** or surfaces a bug. Without this we cannot trust Phase 4 conclusions.

## Phase 2 — Audit Gorard's continuum-side equations

Every equation on the smooth-manifold side is a statement in Riemannian geometry that is either standard or not. For each one we apply the triple check.

### 2A. Gray ball-volume expansion (Gorard Eqs 340, 343)
- Standard: Gray (1973); Gray–Vanhecke (1979); Chavel, *Riemannian Geometry: A Modern Introduction*, Ch. III.6.
- **Symbolic check:** use Mathematica's built-in `RicciTensor` on a metric and compute $\int_B \sqrt{\det g}\, d^d x$ by Taylor expansion; compare coefficient.
- **Numerical check:** on $S^d$ (known $R = d(d-1)$) and on hyperbolic $\mathbb{H}^d$ (known $R = -d(d-1)$), compute the small-ball volume directly and compare to the formula.
- **Expected verdict:** Eqs 340 & 343 are correct standard results.

### 2B. Gray tube-volume expansion (Gorard Eq 342)
- Standard: Gray, *Tubes*, 2nd ed., §4; also Weyl (1939) for Euclidean case, Hotelling (1939), Gray–Vanhecke (1979).
- Correct formula (to be verified from Gray): $V(T_\varepsilon(\gamma)) = \omega_{d-1}\varepsilon^{d-1}L\left(1 - \frac{\varepsilon^2}{2(d+1)}(R - \mathrm{Ric}(u,u)) + O(\varepsilon^4)\right)$.
- Gorard's coefficient: $\frac{d-1}{d+1}$ (no 1/2, no factor-of-2, different combinatorial form).
- **Symbolic check:** compute on $S^2$ directly, expand exactly.
- **Numerical check:** $S^2$ great-circle tube is a spherical zone of area $4\pi\sin\varepsilon$; expand and compare.
- **Expected verdict (pending full verification):** Eq 342 coefficient is wrong by factor $2(d-1)$.
- **If confirmed:** this is the first *computational* error in the paper (not just rhetoric). Document as `notes/eq342_error.md` with the correct Gray derivation step-by-step.

### 2C. Ollivier's theorem (Gorard Eq 344)
- Standard: Ollivier, *Ricci curvature of Markov chains on metric spaces*, JFA 256 (2009), Theorem 6 + Example 7.
- Ollivier's statement: $W_1(m_p^\varepsilon, m_q^\varepsilon) = \delta(1 - \frac{\varepsilon^2}{2(d+2)}\mathrm{Ric}(v,v) + O(\varepsilon^4 + \varepsilon^2 \delta^2))$ with $v = (q-p)/\|q-p\|$.
- Gorard's statement: same prefactor but $R$ (scalar) instead of $\mathrm{Ric}(v,v)$.
- **Numerical check:** on $S^2$, $R=2$, $\mathrm{Ric}(v,v) = 1$ ⇒ predictions differ by factor 2. Compute $W_1$ numerically (optimal transport between two small spherical cap measures) and see which matches.
- **Expected verdict:** Gorard's Eq 344 has a directional-vs-scalar confusion.
- **If confirmed:** the error propagates to Gorard's discrete Ollivier–Ricci argument throughout §3.

### 2D. Metric-in-geodesic-normal-coords (Eqs 337, 338, 772–773, 777)
- Standard: any differential-geometry text; Gray's book has the expansion explicitly.
- **Symbolic check:** Mathematica with a concrete 2D metric (e.g. upper half-plane), verify the expansion.
- Spot check: Eq 338 as printed has a free index $j$ in `\sum_{i=1}^d R_{ij} \delta x^i \delta x^j` — sums over $i$ only, leaving $j$ free. Likely a TeX typo; cross-check with the PDF rendering.

### 2E. Cone-volume formula (Eq 792)
$V(C_t(p)) = a t^n [1 - \frac{1}{6} R_{ij} t^i t^j + O(\|t\|^3)]$
- Standard: cone integration of the ball expansion.
- **Verify coefficient:** the $\frac{1}{6}$ vs $\frac{1}{6(d+2)}$ issue — the coefficient in 343 has $(d+2)$, but in 792 it's just $\frac{1}{6}$. Check if these reconcile under the right integration measure.

### 2F. Each standard-reference theorem cited
Benincasa–Dowker d'Alembertian eq 378–383, Sorkin action eq 384–387. Each needs a correct-citation-check: does Gorard state the result as Sorkin/Benincasa/Dowker do? In particular, line 6080's *swap of weak ergodicity for Poisson* is critical.

**Phase 2 delivers** `notes/continuum_eqs_audit.md` with a triple-check verdict on every continuum equation in §§3.1–3.3 of 2102.09363 (and equivalents in 2004.14810).

## Phase 3 — Audit Gorard's discrete-side equations

### 3A. Discrete Ollivier–Ricci on directed hypergraphs (Eqs 348–356)
- Cited: Eidi–Jost, *Ollivier Ricci Curvature of Directed Hypergraphs*, arXiv:1907.04727.
- **Check:** Gorard's definitions match Eidi–Jost?
- **Verify by direct computation:** compute $\kappa$ for the tested hypergraphs (Figures 66, 67, 68: asymptotically flat / positive / negative), check the sign matches Gorard's claim.
- This is an auditable numerical experiment: construct the specific rule from each caption, evolve, compute discrete Ollivier–Ricci, report value.

### 3B. Discrete causal graph + ADM decomposition
- Check the discrete ADM claim (Eqs 333–336) as a *definition*-level consistency check: is the proposed identification of $\alpha, \beta^i, \gamma_{ij}$ with causal-graph quantities well-defined? Does it converge?
- This is the same tautology I flagged in 2004.14810 — but now with a specific line-by-line TeX trace.

### 3C. Discrete-sectional-curvature formula (Eq 808)
$d(\exp_x(\mathbf{v}_x), \exp_y(\varepsilon \mathbf{v}_y)) = \delta(1 - \frac{\varepsilon^2}{2} K(\mathbf{u},\mathbf{v}) + O(\varepsilon^3 + \varepsilon^2 \delta))$
- This **does** have the directional form ($K(\mathbf{u},\mathbf{v})$ is a sectional curvature, two-argument).
- Check whether this is consistent with Gorard's other formulas (2C) and with standard Riemannian sectional-curvature formulas.

### 3D. Discrete Einstein–Hilbert (Eqs on causal-set / Benincasa–Dowker)
- Separate what Gorard imports from Sorkin/Benincasa/Dowker from what he asserts.
- The critical step 6080 (Poisson replaces weak ergodicity) is the hinge.

**Phase 3 delivers** `notes/discrete_eqs_audit.md` with each discrete-side equation triple-checked.

## Phase 4 — Audit the bridge (discrete → continuum)

The load-bearing claims. Each needs **precise formal statement** and **explicit proof-status verdict**.

### 4A. "Convergence of Ollivier–Ricci to Ricci for discrete hypergraphs"
- Is there a convergence theorem? In the literature (Lin–Lu–Yau 2011, Ollivier 2007, Trillos–Slepčev 2018 for random geometric graphs): yes, under specific sampling hypotheses.
- Does Gorard's §3 invoke such a theorem? **Check line by line.**

### 4B. "Provably satisfies EFE in the continuum limit"
- This is the crux. The line trace (lines 6080 / 6152 / 6202 of the TeX) gave a specific chain: Poisson sampling in a known manifold + BD conjecture.
- Question: does the literature *prove* ⟨S_BD⟩ → S_EH? Dowker–Surya line of work + Cunningham numerics — still conjectural.
- Our verdict should be precise: the chain is *valid as a hypothetical implication* from a known conjecture; what fails is the "Wolfram-model dynamics" link.

### 4C. Empirical direct test
- Build a direct test: pick a small spacetime (Schwarzschild metric near the horizon), Poisson-sample into it, compute the discrete BD action, compare to the EH action evaluated on the continuum metric.
- If agreement is good → confirms the BD/Poisson side of the argument (known, but good to reproduce).
- The test *does not* touch the Wolfram-dynamics claim.

### 4D. The Wolfram-dynamics gap
- Identify the missing theorem: "For Wolfram-model rule R with properties P, the causal graph arising from evolution from seed S converges, in the limit of large T, to a Poisson sample of some Lorentzian manifold $(M,g)$."
- **No such theorem exists, and the named EFE rule cannot satisfy it (see Phase 1 / our empirical refutation).**

**Phase 4 delivers** `notes/bridge_claims_audit.md`: for each bridge claim, *exact formal statement + proof-status verdict with citation*.

## Phase 5 — Independent double-check of every verdict

After Phases 1–4, we have a catalog of correct, incorrect, and open claims. Before the final verdict, every one gets a second-pass check:

- Each "incorrect" verdict is re-derived by a fresh path (separate script, fresh set of references).
- Each "correct" verdict is rechecked by trying to break it (can we find a counterexample? a reference that states it differently?).
- Each "open" verdict is recontextualized (who has the strongest positive / negative evidence in the literature?).

This phase exists because the cost of publishing a wrong "Gorard got this wrong" is high.

**Phase 5 delivers** `notes/verdicts_final.md` with each claim's status double-signed.

## Phase 6 — Formalize what's correct in Lean

For each claim that survives Phase 5 as *correct*:

1. State precisely in Lean (using Mathlib where possible).
2. Prove it, or connect to an existing Mathlib theorem.
3. Commit with the claim-catalog ID in the commit message.

Particular targets for Lean:
- **Theorem A** (edge conservation for $|LHS|=|RHS|$ rules).
- **Theorem B** (linear-cone bound for conservative rules).
- **Theorem C** (|LHS|=|RHS| ⇒ Gorard §3.3 cannot apply).
- The correct Gray tube formula (if Mathlib's differential geometry has enough infrastructure).
- The correct Ollivier theorem for directional Ricci (more speculative — Mathlib's OT + differential geometry isn't quite there yet).

The Lean library becomes **the formal statement of what is and isn't true about Wolfram-model geometry**.

## Phase 7 — Our own direction

Once we know what is actually true, we formulate a positive program.

Candidates:
- **Positive theorem:** for random geometric graphs on a Riemannian manifold (Poisson sampling + proximity edges + $\varepsilon$-scaling), the discrete Ollivier–Ricci converges to $\frac{\mathrm{Ric}(v,v)}{2(d+2)}$ in the appropriate limit. This is Trillos–Slepčev-style but for Ollivier–Ricci specifically.
- **Negative theorem:** no |LHS|=|RHS| rule in the Wolfram-model class can yield a $d \ge 2$ causal graph. Structural, provable, refutes a wide subclass of Gorard's claims in one shot.
- **Lean contribution:** formalization of the correct Gray ball-volume expansion + Ollivier directional statement + the Wolfram-model-as-conservation-system link.

## Concrete next step

Start at **Phase 1A** (Python re-implementation) to bug-audit the empirical work — without a verified empirical basis, we cannot trust Phase 4D's refutation. I'll then move to **Phase 2B / 2C** (numerical test of Eq 342 and Eq 344 on $S^2$), since both are already-suspect equations and the test is cheap.

After each phase I'll come back with a short status report; you can redirect the plan if the findings suggest a different priority.
