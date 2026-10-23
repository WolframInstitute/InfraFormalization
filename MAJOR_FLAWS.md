# Findings F1-F8 on the constructions of G1-G4

This document lists eight findings about the gravitational constructions in G1-G4, with the paper lines they rest on and the Lean files that accompany them. Per-claim status, with axiom lists, is in [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md).

Paper files: G1 = `papers/gorard_2004.14810.txt`, G3 = `papers/gorard_2102.09363.txt`, G4 = `papers/gorard_2303.07282.txt`.

Status labels: PROVED (Lean, kernel-checked, sorry-free, axioms at most `propext`, `Classical.choice`, `Quot.sound`), MEASURED, READ (from the paper text), OPEN. A Lean theorem whose statement does not concern the paper's objects is marked VACUOUS; the finding then rests on the reading.

## Two coefficient errors

- G3 eq. 342 (tube-volume coefficient). G3 gives $(d{-}1)(R - \mathrm{Ric}(u,u))/(d{+}1)$. Gray (1973) gives $(R + \mathrm{Ric}(u,u))/(6(d{+}1))$. The two differ by a factor of 2 on $S^2$ and 6 on $S^3$. PROVED as arithmetic comparisons: `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`. Gray's formula is cited, not formalised.
- G3 eq. 344 (Ollivier-Ricci identity). G3 uses the scalar curvature $R$ where Ollivier (2009) has $\mathrm{Ric}(v,v)$. PROVED: `Infra.ollivier_minus_gorard_leading`, `Infra.ollivier_gorard_agree_iff`, `Infra.s2_gorard_error`. Ollivier's theorem is cited, not formalised.

Substituting the published coefficients corrects both equations. Details: [`results/phase2_continuum/`](results/phase2_continuum/), [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md).

## F1. G1 introduces a discrete metric $g^{ab}$ without a construction

READ. G1 Def 15 (line 786) introduces "a discrete Lorentzian metric" of signature $(-,+,+,+)$. G1 gives no procedure that computes its components from the hypergraph or the causal graph. G1 §3.3 (eqs. 86-90, lines 2168-2240) takes the functional derivative $\delta S/\delta g^{ab}$, which requires components that can be varied, a space of perturbations and an inner product on it.

Lean: `Refutations/F1NoMetric.lean` defines `MetricConstruction V := DHyp V → V → V → ℝ` and proves `hypergraph_does_not_determine_metric`, `metric_construction_is_never_unique`, `no_canonical_metric_from_hypergraph_alone` and `action_depends_on_construction_choice`. These state that the function type has more than one element. Status: VACUOUS with respect to G1. Sources: [`notes/2004.14810_close_reading.md`](notes/2004.14810_close_reading.md), [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) S2.

## F2. G1 assumes orthonormality without a bilinear form

READ. G1 line 2065: "We also assume that all pairs of hyperedges which are not parallel (i.e. incident to the same set of vertices) can be considered to be orthonormal." Orthonormality is a property of a bilinear form, and G1 does not define one on hyperedges. The sectional curvature and Riemann tensor formulas that follow use this assumption.

Lean: `Refutations/F2Orthonormality.lean` proves `orthonormality_depends_on_form` and `orthonormalising_form_not_unique` for forms on `Bool`. Status: VACUOUS with respect to G1.

## F3. Asymptotic dimension preservation is stated as the Euler-Lagrange equation

READ. G1 lines 2203-2206 (eq. 87) state that asymptotic dimension preservation "corresponds to the statement" $\delta S[g^{ab}]/\delta g^{ab} \to 0$. This condition is the Euler-Lagrange equation of $S$. G1 then concludes that causal-invariant, asymptotically dimension-preserving rules satisfy the vacuum Einstein equations. With this definition the conclusion restates the hypothesis.

Lean: `Refutations/F3Tautology.lean`, `asymptoticDimPreservation_iff_eulerLagrange`, PROVED by `Iff.rfl`. Both sides are the project's encoding `P.variation g = 0`. The encoding of eq. 87 is the READ finding.

## F4. Causal invariance and discrete general covariance

READ. G1 lines 1066-1075 identify causal invariance with discrete general covariance.

Lean: `Refutations/F4Tautology.lean`, `causalInvariance_iff_discreteGeneralCovariance`, PROVED by `Iff.rfl`, no axioms. Both sides are the project's encoding `∀ u v, cg u = cg v`.

## F5. The passage from sum to integral has no stated notion of convergence

READ. G1 line 2214 (eq. 88): "In the continuum limit of an arbitrarily large causal graph, this sum becomes (subject to a weak ergodicity assumption on the dynamics of the causal graph) an integral." G1 does not state the notion of convergence or define weak ergodicity. The closest result in the causal-set literature is the Benincasa-Dowker action limit, for which Cunningham (2018) gives numerical support and no proof.

Lean: `Refutations/F5Illdefined.lean` proves `becomes_is_underdetermined`, `claim_is_vacuous_without_convergence_notion` and `different_notions_give_different_limits` for the sequence $1/(n+1)$ and the constant-`True` predicate. Status: VACUOUS with respect to G1.

## F6. G3's comparison starts from initial data sampled from the target geometry

READ.

1. G3 line 6080 replaces "the assumption of weak ergodicity of the causal graph dynamics with the much stronger assumption of uniform Poisson distribution of the rewrite events". G3 gives no proof that the rule of line 6202 produces Poisson-distributed rewrite events.
2. The continuum limit of the Benincasa-Dowker action (lines 6110-6120) holds under the stated assumptions of zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood. G3 cites numerical support (Cunningham 2018) for these assumptions.
3. The initial hypergraph is built "by means of a Poisson point process" so that it is "faithfully embeddable into a given Lorentzian manifold (M, g)" (lines 6148-6152). G3 uses this procedure for "the standard Brill-Lindquist binary black hole initial data" (line 6179).
4. The hypergraphs of Figures 73-77 are coloured with the analytic Schwarzschild conformal factor ψ (eq. 391, lines 6185-6192).
5. G3 does not state the link cut-off distance (line 6176), the update order, or the number of events per unit of the time coordinate.

The comparison starts from a hypergraph sampled from the target initial data. The evolved hypergraphs at t = 6M, 12M and 24M are not the sampled data, so the comparison at those times is a comparison of an evolution with the numerical solution.

Lean: `Refutations/F6Circularity.lean` defines `CircularReconstruction` with the hypothesis `reconstruct (sample t) = t` and restates it as `CircularReconstruction.comp_eq_id`. The file does not model G3's procedure. Status: VACUOUS with respect to G3.

## F7. The rule of G3 line 6202 conserves edge count; its causal-graph growth is open

READ. G3 states that the rule $\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \to \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$ "provably satisfies the Einstein field equations in the continuum limit" (abstract, lines 50-52). G3 gives no proof for this rule.

PROVED.

- $|LHS| = |RHS| = 4$, so every application and every chain of applications preserves the edge count: `CandidateCatalog.gorardNamedRule_isConservative`, `Refutations.gorardNamedRule_application_preserves_size`, `Refutations.gorardNamedRule_applications_preserve_size`.
- In every evolution of the rule from $N$ hyperedges, with any update order, every antichain of the causal graph has at most $N/4$ events (`CausalHistory.gorardNamedRule_antichain_card_le`), and at most $5^t$ events lie within directed distance $t$ of an event (`CausalHistory.gorardNamedRule_ball_card_le`).

MEASURED. The log-log cone-growth exponent of the causal graph lies between 0.77 and 1.26 on cycles, paths and 3D grids of up to 300 edges and 2000 events. The exponent depends on the update order. Table: [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md), Claim 1.

OPEN. Linear cone growth, stated in Lean as `CausalHistory.GorardNamedRuleConeGrowthLinear`.

## F8. G4's title names discrete singularity theorems; the paper states them as open

READ. The title of G4 is "Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems in Wolfram Model Systems" (lines 1-3). The abstract (lines 76-78) states that the results "offer hope that a more general, perhaps ultimately “Penrose-like”, singularity theorem may be provable in the discrete spacetime case". Lines 351-357 state that a discrete analog of the Raychaudhuri equation is "somewhat non-obvious" and that there has been "no systematic investigation of discrete analogs of standard general relativistic energy conditions". G4 contains no discrete Raychaudhuri equation, no discrete expansion scalar and no discrete energy condition. Source: [`notes/2303.07282_close_reading.md`](notes/2303.07282_close_reading.md).

## Summary

| # | Finding | Status | Lean |
|---|---|---|---|
| F1 | No construction of the discrete metric | READ | `Refutations/F1NoMetric.lean`, VACUOUS |
| F2 | Orthonormality without a bilinear form | READ | `Refutations/F2Orthonormality.lean`, VACUOUS |
| F3 | Dimension preservation stated as the Euler-Lagrange equation | READ; encoding PROVED by `Iff.rfl` | `Refutations/F3Tautology.lean` |
| F4 | Causal invariance identified with general covariance | READ; encoding PROVED by `Iff.rfl` | `Refutations/F4Tautology.lean` |
| F5 | No notion of convergence for "becomes" | READ | `Refutations/F5Illdefined.lean`, VACUOUS |
| F6 | Initial data sampled from the target geometry | READ | `Refutations/F6Circularity.lean`, VACUOUS |
| F7 | Edge-count conservation and causal-graph bounds | PROVED, MEASURED; linear growth OPEN | `Refutations/F7NamedRuleStructure.lean`, `CausalHistory.lean` |
| F8 | Title names theorems the paper states as open | READ | none |
