# Findings: one line per audited claim

Paper files: G1 = `papers/gorard_2004.14810.txt`, G2 = `papers/gorard_2011.12174.txt`, G3 = `papers/gorard_2102.09363.txt`, G4 = `papers/gorard_2303.07282.txt`. Line numbers refer to these text files.

Status labels: PROVED (Lean, kernel-checked, sorry-free, axioms at most `propext`, `Classical.choice`, `Quot.sound`), MEASURED, READ, OPEN. Per-claim detail with axiom lists: [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md). Groups S1-S6 follow [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md).

## S1. Formulas that differ from the cited sources

| # | Claim | Where | Status |
|---|---|---|---|
| 1 | The Wasserstein distance between ε-balls transported along a geodesic has leading curvature term in the scalar curvature R. Ollivier (2009), which G3 cites, has the Ricci curvature Ric(v,v) in the direction of the geodesic. | G1 eq. 80 (lines 2045-2056); G3 eq. 344 (line 5340) | PROVED as an arithmetic comparison (`Infra.ollivier_gorard_agree_iff`); [eq344_verdict.md](results/phase2_continuum/eq344_verdict.md) |
| 2 | Tube-volume coefficient (d−1)(R − Ric(u,u))/(d+1). Gray (1973) gives (R + Ric(u,u))/(6(d+1)). The two differ by a factor of 2 on S² and 6 on S³. | G2 eq. 126 (line 2409); G3 eq. 342 (line 5276) | PROVED as an arithmetic comparison (`Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`); [eq342_verdict.md](results/phase2_continuum/eq342_verdict.md) |

## S2. Objects used without a definition

| # | Claim | Where | Status |
|---|---|---|---|
| 3 | The discrete Einstein-Hilbert action S[g^ab] = Σ dμ_g R uses a metric g^ab and a measure dμ_g that are not constructed from the hypergraph. | G1 eq. 86 (line 2200), Def 15 (line 786) | READ |
| 4 | The functional derivative δS/δg^ab is applied to a discrete sum. | G1 eq. 87 (lines 2203-2211) | READ |
| 5 | Non-parallel hyperedges "can be considered to be orthonormal"; no bilinear form is defined. | G1 lines 2061-2063 | READ |
| 6 | The expansions of eqs. 64-65 and eq. 80 hold as r → 0 and as ε, δ → 0. G1 sets ε = δ = 1 and states that the ball-volume expansion holds "with exactness when r = 1". | G1 lines 1788, 2056-2060 | READ |

## S3. Equivalences that hold by definition

| # | Claim | Where | Status |
|---|---|---|---|
| 7 | Causal invariance corresponds to discrete general covariance. Both are update-order independence of the causal graph. | G1 lines 1066-1075 | READ; the project's encoding is PROVED by `Iff.rfl` (`causalInvariance_iff_discreteGeneralCovariance`) |
| 8 | Causal invariance gives discrete Lorentz covariance. The constancy of the speed of light "is enforced axiomatically by our definition of the edge lengths". | G1 lines 1083-1088 | READ |
| 9 | Asymptotic dimension preservation "corresponds to the statement" δS/δg^ab → 0, the Euler-Lagrange equation of S. | G1 lines 2203-2211 | READ; the project's encoding is PROVED by `Iff.rfl` (`asymptoticDimPreservation_iff_eulerLagrange`) |

## S4. Passages from discrete to continuum without a proof

| # | Claim | Where | Status |
|---|---|---|---|
| 10 | Σ dμ_g R "becomes" ∫ d⁴x √−g R "subject to a weak ergodicity assumption". No notion of convergence is stated. For causal sets, the corresponding Benincasa-Dowker limit has numerical support (Cunningham 2018) and no proof. | G1 line 2214 (eq. 88) | READ, OPEN |
| 11 | The rule {{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}} "provably satisfies the Einstein field equations in the continuum limit". G3 gives no proof for this rule. G3 assumes Poisson-distributed rewrite events (line 6080) and samples the initial hypergraph from the target geometry (lines 6148-6152, 6179). | G3 lines 50-52, 6202 | READ; see [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md), Claims 1-2 |
| 12 | The Ollivier-Ricci curvature of directed hypergraphs converges to the Ricci curvature in the continuum limit. Convergence theorems exist for random geometric graphs (García Trillos and Slepčev 2018), not for hypergraph rewriting evolutions. | G1 §3.2 | READ, OPEN |

## S5. The rule of G3 line 6202

| # | Claim | Status |
|---|---|---|
| 13 | The rule's evolution has a 3+1-dimensional causal graph. | MEASURED: log-log cone-growth exponents between 0.77 and 1.26 on cycles, paths and 3D grids up to 300 edges and 2000 events, with up to 0.3 variation between update orders. PROVED: edge-count conservation, an antichain bound N/4 and a cone bound 5^t. OPEN: linear cone growth. |
| 14 | Hypergraph ball counts satisfy N(r) = a rⁿ (1 − R r²/(6(n+2)) + O(r⁴)). G1 transfers the Riemannian ball-volume expansion to vertex counts and gives no derivation for hypergraphs. | READ: G1 lines 1780-1796 |

## S6. Titles and abstracts

| # | Claim | Status |
|---|---|---|
| 15 | G4's title names "Discrete Singularity Theorems". G4 contains no discrete Raychaudhuri equation, expansion scalar or energy condition, and states a discrete singularity theorem as a hope (lines 76-78). | READ: G4 lines 1-3, 76-78, 351-357 |
| 16 | "Provably" in G3's abstract applies to a chain that assumes Poisson-distributed rewrite events (line 6080) and the zero-surface-term and Riemann-normal-neighbourhood assumptions of the Benincasa-Dowker limit (lines 6110-6120). | READ |

## Standard material

The continuum material quoted in G1-G3 agrees with the standard references: the Riemannian ball-volume expansion (G3 eq. 343, Gray 1973), the metric, Christoffel, Riemann and Ricci definitions, the variation of the Einstein-Hilbert action (G1 eqs. 89-91), the definitions of abstract rewriting systems and confluence (Baader and Nipkow), the Ollivier-Ricci curvature of metric measure spaces (Ollivier 2009), the ADM decomposition, the FLRW metric and the Benincasa-Dowker d'Alembertian. This is READ, not formalised.

## Results about the Wolfram model

| # | Result | Status |
|---|---|---|
| P1 | A rule with \|LHS\| = \|RHS\| preserves the edge count along every evolution. | PROVED: `Application.size_result_of_conservative` (`Conservation.lean`), `size_preserved_by_applications`, `Refutations.gorardNamedRule_applications_preserve_size` |
| P2a | For a rule with \|LHS\| = \|RHS\| = k and N initial hyperedges, every antichain of the causal graph has at most N/k events, for every update order. | PROVED: `CausalHistory.RuleHistory.antichain_card_le`; for the rule of G3, `CausalHistory.gorardNamedRule_antichain_card_le` (4·\|A\| ≤ N) |
| P2b | The causal graph of the rule of G3 has cone growth C(t) ≤ c(N)·(t+1). | OPEN, stated as `CausalHistory.GorardNamedRuleConeGrowthLinear`. PROVED: C(t) ≤ 5^t (`CausalHistory.gorardNamedRule_ball_card_le`). P2a bounds the events at each longest-path distance, and C(t) counts shortest-path distance, so P2a does not imply P2b. |
| P3 | G1's §3.3 argument for dimension n applies to the rule of G3. | OPEN. It needs P2b and a notion of convergence that G1 does not state. |

## Summary

- G1's §3.3 argument uses a metric, a measure and orthonormality that are not constructed from the hypergraph (S2), and states dimension preservation as the Euler-Lagrange equation (S3).
- G3 gives no proof that the rule of line 6202 satisfies the Einstein equations. The rule conserves edge count and its causal graph satisfies the antichain and cone bounds above (PROVED). Its measured cone-growth exponents are near 1 (MEASURED).
- G3's comparison with numerical relativity assumes Poisson-distributed rewrite events and starts from initial data sampled from the target geometry (S4).
- Two curvature coefficients differ from the cited sources by factors of 2 and 6 on S² and S³ (S1).
