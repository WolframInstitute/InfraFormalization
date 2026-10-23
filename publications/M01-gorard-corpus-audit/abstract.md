# M01: The derivation of general relativity in four Wolfram model papers, read against its sources

Scope. The paper examines the derivation of general relativity from hypergraph rewriting in arXiv:2004.14810 (G1), 2011.12174 (G2), 2102.09363 (G3) and 2303.07282 (G4). It lists the continuum-limit claims with their lines in the text, groups the findings as S1-S6 (`FINDINGS.md`) and F1-F8 (`MAJOR_FLAWS.md`), and reports measurements of the causal graph of the rule that G3 describes as one "that provably satisfies the Einstein field equations in the continuum limit" (lines 50-52). The status of each finding is stated as PROVED, VACUOUS, MEASURED, READ or OPEN; per-claim detail is in `STATUS_OF_GORARD_CLAIMS.md`.

Results.

1. Two formulas differ from their cited sources. The Wasserstein expansion of G1 eqs. 48 and 80, G2 eq. 197 and G3 eqs. 344 and 373 has the scalar curvature R where Ollivier (2009) has Ric(v,v) (READ). The tube-volume coefficient of G2 eq. 126 and G3 eq. 342 is (d−1)(R − Ric(u,u))/(d+1), and the expansion from Fermi normal coordinates gives (R + Ric(u,u))/(6(d+1)); the two differ by factors of 2 on S² and 6 on S³ (READ; the comparisons of the coefficients are PROVED as arithmetic: `Infra.ollivier_gorard_agree_iff`, `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`).
2. G1 introduces a discrete metric g^ab (Definition 15, line 786) and takes δS/δg^ab (eq. 87, lines 2203-2211) without a construction of the metric components from the hypergraph, and assumes that non-parallel hyperedges "can be considered to be orthonormal" (lines 2063-2065) without a bilinear form (READ). The Lean files `Refutations/F1NoMetric.lean` and `Refutations/F2Orthonormality.lean` are VACUOUS with respect to G1.
3. G1 states asymptotic dimensionality preservation as δS/δg^ab → 0 (eq. 87), the Euler-Lagrange equation of S (READ). The project's encoding of the equivalence is PROVED by `Iff.rfl` (`asymptoticDimPreservation_iff_eulerLagrange`).
4. G3's argument for the rule replaces weak ergodicity by "the much stronger assumption of uniform Poisson distribution of the rewrite events" (line 6080) and uses the Benincasa-Dowker convergence, which G3 describes as "demonstrated numerically by Cunningham" (lines 6110-6112). G3's comparison with numerical relativity starts from a hypergraph obtained by Poisson sampling of the Brill-Lindquist initial data (lines 6148-6152, 6179) (READ).
5. The rule of G3 line 6202 preserves the edge count, every antichain of its causal graph has at most N/4 events, and at most 5^t events lie within directed distance t of an event, for every update order (PROVED: `Refutations.gorardNamedRule_applications_preserve_size`, `CausalHistory.gorardNamedRule_antichain_card_le`, `CausalHistory.gorardNamedRule_ball_card_le`). On cycles, paths and 3D grids of up to 300 edges and 2000 events its cone-growth exponent lies between 0.77 and 1.26, depending on the update order (MEASURED). Linear cone growth is OPEN (`CausalHistory.GorardNamedRuleConeGrowthLinear`).
6. The title of G4 names "Discrete Singularity Theorems". G4 states a discrete singularity theorem as a hope (abstract, lines 75-79) and contains no discrete Raychaudhuri equation, expansion scalar or energy condition (READ, lines 351-357).

The numerical-relativity results of G3 and G4 (CCZ4 on a hypergraph mesh) are outside the scope of these findings.

Companion papers: I05 (the Wasserstein expansion), I06 (the tube-volume coefficient), I07 (measurements of the rule), I01 (edge conservation and causal-graph bounds).

Target venue: arXiv math-ph, gr-qc, cs.LO; Complex Systems.

Length: 30-50 pages with a Lean appendix.

Lean support: the theorems named above; `STATUS_OF_GORARD_CLAIMS.md` lists their axioms. Measurements: `scripts/python/rewriter.py`, `scripts/python/setreplace_order.py` and the SetReplace scripts listed in `notes/empirical_refutation.md`.

Open items: linear cone growth of the rule (O1) and a run on G3's initial data (O5), both in `STATUS_OF_GORARD_CLAIMS.md`.
