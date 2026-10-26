# Plan for the review of G1-G4

The review examines the derivation of general relativity from hypergraph rewriting in arXiv:2004.14810 (G1), 2011.12174 (G2), 2102.09363 (G3) and 2303.07282 (G4). For each claim the review records what the paper states and what holds. Statements that hold are formalised in Lean where the library allows it. Statements that differ from a cited source are recorded with both formulas.

Paper files are `papers/gorard_*.txt`, and the TeX sources are in `papers/tex_*`. Status labels follow `STATUS_OF_GORARD_CLAIMS.md`: PROVED, PROVED-WITH-NATIVE-DECIDE, MEASURED, READ, OPEN.

## Method

1. A statement that a formula differs from a standard result is checked by an independent derivation, by a symbolic computation, by a numerical test on a case with a known answer, and by a hand computation on a small case.
2. A measurement from SetReplace is reproduced by an independent Python implementation of the rewriting semantics. Differences are traced to their cause before the measurement is reported.
3. Every statement about a paper cites the line in `papers/*.txt` and quotes the text.
4. Results from the literature that a paper uses (Benincasa-Dowker, Ollivier, Gray, ADM) are checked against their sources and attributed to them.
5. A formula that is correct and a claim in the prose around it are assessed separately.

## Phase 0: catalogue

`notes/claims_catalog.md` lists the numbered equations, definitions and prose claims of G1 with their TeX and text lines and a classification. Status: present.

## Phase 1: checks of the measurements

Results: `results/phase1_selfaudit/README.md`, `results/phase1_selfaudit/setreplace_reference.md`, `notes/empirical_refutation.md`.

- 1A. `scripts/python/rewriter.py` reimplements the rule of G3 line 6202 with hyperedge identities. On the 9 seeds it agrees with SetReplace 0.3.196 on events fired, final state size and causal-graph vertex count, and on causal-graph edge count on 7 of 9 seeds. The cone-growth exponents differ because the two tools use different update orders. `scripts/python/setreplace_order.py` reimplements the SetReplace order and reproduces its cone counts on the 6-cycle, 8-cycle and 10-path. MEASURED: exponents between 0.77 and 1.26 across four update orders.
- 1B. Hand traces of the 4-cycle and the 4-edge path, on which the rule fires once: in `results/phase1_selfaudit/README.md`.
- 1C. Edge-by-edge comparison of the causal graphs of the two tools on the 6-cycle: not run.
- 1D. A second estimate of the exponent from the ratio C(2r)/C(r), and its spread over perturbed seeds: not run.

## Phase 2: continuum equations of G3 §6

- 2A. Ball-volume expansion, G3 eq. 340 (line 5241) and eq. 343 (line 5306). G3 eq. 343 agrees with Gray (1973) (READ, `FINDINGS.md`, Standard material). The symbolic and numerical checks on S^d and H^d: not run.
- 2B. Tube-volume expansion, G3 eq. 342 (line 5276) and G2 eq. 126 (line 2409). G3 gives the coefficient (d−1)(R − Ric(u,u))/(d+1). The expansion from Fermi normal coordinates gives (R + Ric(u,u))/(6(d+1)), confirmed by the exact series on S² and S³. The comparison of the two coefficients on S² and S³ is PROVED. Result: `results/phase2_continuum/eq342_verdict.md`.
- 2C. Ollivier's theorem, G3 eq. 344 (line 5340). G3 has the scalar curvature R where Ollivier (2009, Example 7) has Ric(v,v). The comparison of the leading terms is PROVED. A Monte Carlo estimate at N = 600 does not resolve the difference (MEASURED). Result: `results/phase2_continuum/eq344_verdict.md`.
- 2D. Volume-element expansion, G3 eq. 338 (line 5210, TeX line 2587). The sum is written over i only and leaves the index j free (READ). Symbolic check on a concrete metric: not run.
- 2E. Cone-volume formula, G3 eq. 369 (line 5774): Vol(C_t(p)) = a t^n [1 − (1/6) R_ij t^i t^j + O(‖t‖³)]. Its relation to the coefficient R/(6(d+2)) of eq. 340: OPEN.
- 2F. Benincasa-Dowker d'Alembertian and action, G3 eqs. 378-387 (lines 5984-6124). G3 replaces weak ergodicity by "the much stronger assumption of uniform Poisson distribution of the rewrite events" (line 6080), and states the convergence of eq. 387 "as proposed by Sorkin, Benincasa and Dowker, and demonstrated numerically by Cunningham" under zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood (lines 6110-6116) (READ). Comparison with the statements in Benincasa and Dowker (2010): OPEN.

## Phase 3: discrete equations of G3 §6

- 3A. Discrete Ollivier-Ricci curvature of directed hypergraphs, G3 eqs. 348-356 (lines 5430-5574), citing Eidi and Jost (arXiv:1907.04727). Comparison with Eidi and Jost, and computation of κ on the hypergraphs of Figures 66-68: not run.
- 3B. Discrete ADM decomposition, G3 eqs. 333-336 (lines 5139-5179): the spatial metric from Δl² = γ_ij Δx^i Δx^j "for some choice of assignments of spatial coordinates", the lapse from Δτ = αΔt and the shift from x^i(t + Δt) = x^i(t) − β^i(t) (READ). Whether these quantities are determined by the hypergraph and causal graph, and whether they converge: OPEN.
- 3C. Sectional-curvature distance formula, G3 eq. 372 (TeX line 2809): d(exp_x(v_x), exp_y(ε v_y)) = δ(1 − (ε²/2) K(u,v) + O(ε³ + ε²δ)). It uses the sectional curvature K(u,v) of the plane of u and v. Comparison with the Riemannian formula: OPEN.

## Phase 4: passages from discrete to continuum

Notes: `notes/continuum_limit_claims.md`, `notes/limit_toolkit.md`.

- 4A. Convergence of discrete Ollivier-Ricci curvature to Ricci curvature. Results exist for random geometric graphs (García Trillos and Slepčev 2018). G1-G3 cite no convergence theorem for hypergraph rewriting (READ).
- 4B. "Provably satisfies the Einstein field equations in the continuum limit" (G3 lines 50-52). The argument in G3 §6 assumes Poisson-distributed rewrite events (line 6080) and the Benincasa-Dowker convergence (lines 6110-6124), and samples the initial hypergraph from the target geometry (lines 6148-6152, 6179) (READ). G3 gives no proof that the evolution of the rule of line 6202 produces Poisson-distributed events.
- 4C. Benincasa-Dowker action on a Poisson sprinkling of a Schwarzschild region, compared with the Einstein-Hilbert action: not run.
- 4D. The statement needed: for a rule R with stated properties, the causal graph of the evolution from a seed converges, as the number of events grows, to a Poisson sample of a Lorentzian manifold. OPEN for every rule. For the rule of G3 line 6202, linear cone growth (`CausalHistory.GorardNamedRuleConeGrowthLinear`) is OPEN, and the measured exponents lie between 0.77 and 1.26 (MEASURED).

## Phase 5: second check of every finding

Each finding that a formula differs from its source is rederived by a second route. Each formula recorded as standard is checked against a second reference. Status: the findings are collected in `FINDINGS.md`, `MAJOR_FLAWS.md` and `STATUS_OF_GORARD_CLAIMS.md`. A separate second-check record does not exist.

## Phase 6: Lean

| Target | Status |
|---|---|
| Edge-count conservation for rules with \|LHS\| = \|RHS\| | PROVED: `Application.size_result_of_conservative`, `size_preserved_by_applications`, `Refutations.gorardNamedRule_applications_preserve_size` |
| Antichain bound k·\|A\| ≤ N for \|LHS\| = \|RHS\| = k | PROVED: `CausalHistory.RuleHistory.antichain_card_le`, `CausalHistory.gorardNamedRule_antichain_card_le` |
| Cone bound 5^t for the rule of G3 line 6202 | PROVED: `CausalHistory.gorardNamedRule_ball_card_le` |
| Linear cone growth for the rule of G3 line 6202 | OPEN: `CausalHistory.GorardNamedRuleConeGrowthLinear` |
| G1 §3.3 applied to the rule of G3 line 6202 | OPEN: needs linear or polynomial cone growth and a notion of convergence that G1 does not state |
| Comparison of the tube and Ollivier coefficients | PROVED as arithmetic: `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`, `Infra.ollivier_gorard_agree_iff`. Gray's and Ollivier's theorems are cited, not formalised. |
| Gray's tube formula and Ollivier's theorem in Lean | OPEN |

## Phase 7: further directions

- For random geometric graphs on a Riemannian manifold (Poisson sampling, proximity edges, scale ε → 0), convergence of the discrete Ollivier-Ricci curvature to Ric(v,v)/(2(d+2)). OPEN.
- For rules with |LHS| = |RHS|, an upper bound on the growth of causal cones. The antichain bound is PROVED. A bound linear in the radius is OPEN even for the rule of G3 line 6202.
- Lean statements of Gray's ball and tube expansions and of Ollivier's theorem. OPEN.
