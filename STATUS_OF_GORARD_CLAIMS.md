# Status of the repository's conclusions about JGORARD's claims

Each entry lists the claim with its source line, then what the repository proves, measures and reads from the paper, and what is open.

Status labels:

- **PROVED**: a Lean theorem, kernel-checked, sorry-free, with axioms at most `propext`, `Classical.choice`, `Quot.sound`. The axiom lists below were printed with `#print axioms` through `lake env lean --stdin` on 2026-10-23 after `lake build` (3642 jobs) exited 0.
- **PROVED-WITH-NATIVE-DECIDE**: kernel-checked but depends on `Lean.ofReduceBool` through `native_decide`. Not axiom-clean.
- **VACUOUS**: a Lean theorem that holds, but its statement does not concern the paper's objects. The finding about the paper rests on reading the paper.
- **READ**: a finding about the paper text, with the line numbers in `papers/*.txt`.
- **MEASURED**: a number from a script run, with the script, seeds and sizes.
- **OPEN**: not established. The exact statement needed is given.

Paper files: G1 = `papers/gorard_2004.14810.txt`, G3 = `papers/gorard_2102.09363.txt`.

## Claim 1. The rule {{x,y},{y,z},{z,w},{w,v}} -> {{y,u},{u,v},{w,x},{x,u}} "provably satisfies the Einstein field equations in the continuum limit"

Source: G3 abstract lines 50-52, §1 lines 182 and 271. The rule first appears at G3 line 6202, in the text of §6 and in the captions of Figures 73-77 and 79-83.

READ:

- G3 gives no proof that this rule satisfies the Einstein field equations, weak ergodicity, asymptotic dimension preservation or causal invariance. The rule appears only as the rule used in the §6 comparison (`notes/2102.09363_close_reading.md` §5).
- G3 line 6080 replaces "the assumption of weak ergodicity of the causal graph dynamics with the much stronger assumption of uniform Poisson distribution of the rewrite events". G3 gives no proof that this rule produces Poisson-distributed rewrite events.
- The continuum limit of the Benincasa-Dowker action used at G3 lines 6110-6120 holds under the stated assumptions of zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood. G3 cites numerical support (Cunningham) for these assumptions, not a proof.

PROVED:

| Theorem | File:line | Statement | Axioms |
|---|---|---|---|
| `CandidateCatalog.gorardNamedRule` | `lean/InfraFormalization/CandidateRuleCatalog.lean:91` | Encoding of the rule with x=0, y=1, z=2, w=3, v=4, u=5 | definition |
| `CandidateCatalog.gorardNamedRule_isConservative` | `CandidateRuleCatalog.lean:103` | \|LHS\| = \|RHS\| = 4 | `propext` |
| `Application.size_result_of_conservative` | `Conservation.lean:27` | One application of a conservative rule preserves edge count | `propext`, `Classical.choice`, `Quot.sound` |
| `size_preserved_by_applications` | `Conservation.lean:48` | A chain of applications of a conservative rule preserves edge count | same |
| `trajectory_size_invariant` | `RuleDimensionBounds.lean:61` | Every state of a step-consistent trajectory of conservative rules has the edge count of the initial state | same |
| `Refutations.gorardNamedRule_application_preserves_size` | `Refutations/F7NamedRuleStructure.lean:33` | One application of the named rule preserves edge count | same |
| `Refutations.gorardNamedRule_applications_preserve_size` | `Refutations/F7NamedRuleStructure.lean:41` | A chain of applications of the named rule preserves edge count | same |

The rule is edge-count conserving. No theorem in the repository bounds the growth or the dimension of the rule's causal graph.

MEASURED (cone-growth exponent of the causal graph): the exponent is the slope of a least-squares fit of log C(r) against log r, where C(r) is the number of events within directed graph distance r of the first event, over the middle half of the radii.

| Seed | Seed edges | Events | SetReplace exponent | Python exponent | Causal edges SetReplace / Python |
|---|---:|---:|---:|---:|---|
| directed 4-cycle | 4 | 1 | none (rule halts) | none (rule halts) | 0 / 0 |
| directed 4-edge path | 4 | 1 | none (rule halts) | none (rule halts) | 0 / 0 |
| 6-cycle | 6 | 500 | 0.995 | 0.995 | 1994 / 1994 |
| 8-cycle | 8 | 500 | 0.991 | 1.000 | 1992 / 1992 |
| 10-path | 10 | 500 | 1.014 | 0.995 | 1990 / 1990 |
| 20-cycle | 20 | 1000 | 0.995 | 1.028 | 3980 / 3980 |
| 3x3x3 grid | 54 | 300 | 1.098 | 1.081 | 1146 / 1150 |
| 4x4x4 grid | 144 | 1000 | 0.985 | 1.256 | 3856 / 3856 |
| 5x5x5 grid | 300 | 2000 | 1.014 | 1.055 | 7703 / 7700 |

- SetReplace column: `scripts/run_seeds_v3.wl`, `scripts/causal_dimension.wl`, `scripts/grid3d_test.wl` with SetReplace 0.3.196, as recorded in `notes/empirical_refutation.md` and `results/phase1_selfaudit/setreplace_reference.md`. Not rerun on 2026-10-23.
- Python column: `scripts/python/run_all_seeds.py`, rerun on 2026-10-23. The script exits with status 1 and prints "MISMATCHES DETECTED" for the causal edge counts of the 3x3x3 and 5x5x5 grids.
- The two tools disagree on the exponent for every seed except the 6-cycle. The largest difference is on the 4x4x4 grid, 0.985 against 1.256, with equal event and causal-edge counts. The first cone counts differ there: SetReplace C(r) = 4, 11, 21, 33, 45, 55, 65, 74, and Python C(r) = 1, 3, 7, 15, 26, 43, 61, 82, 99, 118, 138. The cause of the disagreement is not determined.
- A figure-8 seed (14 edges, 1000 events) was run with SetReplace only.
- The largest run has 2000 events. The rule was not run on a Poisson sprinkling of Brill-Lindquist data, the initial data G3 uses.
- An edge-count conserving rule keeps every spatial hypergraph at its initial size, so the spatial ball count is bounded on each run. A bounded ball count holds for every finite hypergraph and does not distinguish this rule from any other. G3 compares runs at 200, 400, 800 and 1600 vertices, a sequence of initial states of growing size, which edge-count conservation within one run does not constrain.

OPEN:

- O1. A bound on the causal-graph cone growth of the rule. Statement needed: for every initial hypergraph with N edges and every single-way evolution of the rule from it, every event e and every t satisfy C_e(t) ≤ c(N)·(t+1), where C_e(t) is the number of events within directed distance t of e and c depends only on N. Out-degree in the causal graph is at most 4, which gives only C_e(t) ≤ (4^(t+1)-1)/3.
- O2 (P2a in `FINDINGS.md`). Statement needed: in a single-way evolution with N edges, every antichain of the causal graph has at most N/4 events. Proof outline: the inputs of an antichain are present together in the state reached by applying the events of its strict down-set. O2 bounds the number of events at each longest-path distance from e. O2 does not bound C_e(t), which counts shortest-path distance, so O2 does not imply O1.
- O3. Neither O1 nor O2 can be stated in the library yet. `causallyPrecedes` (`Causal.lean:35`) relates two applications when a hyperedge value produced by one is consumed by the other. A causal graph needs hyperedge identities, and the library has none (`Causal.lean:44`).
- O4. The cause of the SetReplace and Python exponent disagreement (table above).
- O5. A run of the rule on a Poisson sprinkling of Brill-Lindquist initial data at the resolutions of G3 Table 6.
- The repository does not prove Claim 1 false. Claim 1 does not state a convergence notion, so there is no precise statement to refute (see Claim 3, F5).

## Claim 2. Pure Wolfram model evolution under the rule and the numerical solution "converge to the same limiting geometries", including binary black hole mergers

Source: G3 abstract lines 42-58, §6 lines 6146-6290, Table 6.

READ:

- The initial hypergraph is built "by means of a Poisson point process" so that it is "faithfully embeddable into a given Lorentzian manifold (M, g)" (G3 lines 6148-6152). G3 uses this procedure "to set up the standard Brill-Lindquist binary black hole initial data" (line 6179). The comparison therefore starts from a hypergraph sampled from the target initial-data geometry.
- The hypergraphs in Figures 73-77 are coloured with the analytic Schwarzschild conformal factor ψ of eq. 391 (lines 6185-6192).
- G3 states the masses (0.5M each), the separation (1M), the times (t = 6M, 12M, 24M), the Kerr spin (a/M = 0.6) and the resolutions (100 to 1600 vertices). G3 states no value for the link cut-off distance ("a certain cut-off distance", line 6176), no update order, no number of events per unit of t, and no map from events to the time coordinate t.
- G3 extracts rΨ4 "in the pure Wolfram model case" (line 6212) and reports second-order convergence of the Hamiltonian constraint (Table 6).

Lean: `Refutations/F6Circularity.lean:39` defines `CircularReconstruction`, a pair of maps with the hypothesis `reconstruct (sample t) = t`, and `CircularReconstruction.comp_eq_id` (`:48`, axioms `Quot.sound`) restates the hypothesis. The file does not model the procedure of G3 and does not prove that the procedure satisfies the hypothesis. Status: VACUOUS with respect to Claim 2. The evolved hypergraphs at t = 6M, 12M, 24M are not the sampled initial data, so the comparison at those times is not of the form `reconstruct ∘ sample`.

The `BBH*.lean` files (`BBHInitialData.lean:64` defines `bbhInitial`, a 6-vertex graph of two triangles joined by one edge) and the rules in `DiscoveredRules.lean:66-130` (single-edge left-hand sides) use neither the named rule nor G3's initial data. They do not bear on Claim 2.

OPEN: O5 above.

## Claim 3. Causal-invariant, asymptotically dimensionality-preserving rules satisfy the vacuum Einstein equations in the continuum limit

Source: G1 §3.3, eqs. 86-91, lines 2168-2240.

READ:

- G1 lines 2203-2206 state that asymptotic dimensionality preservation "corresponds to the statement" δS/δg^ab → 0 (eq. 87). This condition is the Euler-Lagrange equation of S.
- G1 line 2214 (eq. 88) states that the sum "becomes" the Einstein-Hilbert integral "subject to a weak ergodicity assumption", with no notion of convergence and no definition of weak ergodicity.
- G1 Def 15 (line 786) introduces a discrete Lorentzian metric g without a construction from the hypergraph. G1 line 2065 assumes non-parallel hyperedges "can be considered to be orthonormal" without a bilinear form.

Lean (all axiom-clean):

| Theorem | File:line | Status |
|---|---|---|
| `asymptoticDimPreservation_iff_eulerLagrange` | `Refutations/F3Tautology.lean:57` | PROVED by `Iff.rfl`. Both sides are the project's encoding `P.variation g = 0`. The encoding of eq. 87 is a READ finding. |
| `hypergraph_does_not_determine_metric`, `metric_construction_is_never_unique`, `no_canonical_metric_from_hypergraph_alone`, `action_depends_on_construction_choice` | `Refutations/F1NoMetric.lean:110, 125, 137, 147` | VACUOUS: the function type `DHyp V → V → V → ℝ` has more than one element |
| `orthonormality_depends_on_form`, `orthonormalising_form_not_unique` | `Refutations/F2Orthonormality.lean:63, 79` | VACUOUS: facts about functions on `Bool × Bool` |
| `becomes_is_underdetermined`, `claim_is_vacuous_without_convergence_notion`, `different_notions_give_different_limits` | `Refutations/F5Illdefined.lean:127, 134, 142` | VACUOUS: facts about the sequence 1/(n+1) and the constant-`True` predicate |

## Claim 4. Causal invariance corresponds to discrete general covariance

Source: G1 lines 1066-1075.

`causalInvariance_iff_discreteGeneralCovariance` (`Refutations/F4Tautology.lean:51`) is PROVED by `Iff.rfl` and depends on no axioms. Both sides are the project's encoding `∀ u v, cg u = cg v`. The identification of the two notions in G1 is a READ finding.

## Claim 5. Tube-volume coefficient (G3 eq. 342) and Ollivier-Ricci identity (G3 eq. 344)

| Theorem | File:line | Statement | Axioms |
|---|---|---|---|
| `Infra.gray_vs_gorard_disagree_on_S2` | `Infra/GrayTubeStatement.lean:86` | The two leading coefficients differ on S² (1/6 against 1/3) | `propext`, `Classical.choice`, `Quot.sound` |
| `Infra.gray_vs_gorard_disagree_on_S3` | `Infra/GrayTubeStatement.lean:96` | The two leading coefficients differ on S³ | same |
| `Infra.ollivier_minus_gorard_leading` | `Infra/OllivierStatement.lean:93` | The leading terms differ by δε²(R − Ric(v,v))/(2(n+2)) | same |
| `Infra.ollivier_gorard_agree_iff` | `Infra/OllivierStatement.lean:107` | For δ, ε ≠ 0 the leading terms agree iff R = Ric(v,v) | same |
| `Infra.s2_gorard_error` | `Infra/OllivierStatement.lean:137` | The S² discrepancy | same |

These theorems are PROVED arithmetic comparisons. The correct coefficients come from Gray 1973 and Ollivier 2009, which are cited and not formalised. Verdicts: `results/phase2_continuum/eq342_verdict.md`, `results/phase2_continuum/eq344_verdict.md`.

## Execution engine

`MultiwayExec.singleWayStep` fires every match of a step, including overlapping matches. On the 4-cycle seed the named rule has four overlapping matches, and the edge count after one step is not 4 (`RuleSignatureExecCorpus.lean:216`, `native_decide`). A Wolfram model single-way update applies non-overlapping matches. Results computed with `singleWayStep` on seeds with overlapping matches are therefore not Wolfram model evolutions of the rule.
