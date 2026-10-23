# Major structural flaws in the JGORARD corpus

Distinguishes the *arithmetic errors* (minor — patchable by substituting correct formulas) from the *structural/conceptual flaws* (major — cannot be fixed by arithmetic). The major ones need to be exposed, proven false, and replaced by genuine constructions if the program is to be salvaged.

This document is the canonical reference for the *major* side. For the *minor* side (Eq 342 tube coefficient, Eq 344 Ollivier directional/scalar) see [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) (S1 class) and [`results/phase2_continuum/`](results/phase2_continuum/).

## Minor flaws (arithmetic; fixable)

- **Eq 342 (tube-volume coefficient).** Wrong algebraic form: $(d{-}1)(R - \mathrm{Ric}(u,u))/(d{+}1)$ vs correct $(R + \mathrm{Ric}(u,u))/(6(d{+}1))$. Factor-2 off on $S^2$, factor-6 off on $S^3$. Status: refuted (four rails), correct form formalised in Lean as `Infra.GrayTubeLeading` with concrete disagreement proofs `gray_vs_gorard_disagree_on_S2/S3`.
- **Eq 344 (Ollivier Wasserstein).** Scalar $R$ vs directional $\mathrm{Ric}(v,v)$. Factor-2 off on $S^2$. Status: refuted against Ollivier's cited JFA 2009 theorem, correct form formalised in Lean as `Infra.OllivierIdentityLeading`.

These can be *patched* by substituting the right formula. The rest of §3 remains structurally flawed regardless.

## Major structural flaws

Each is *not fixable by arithmetic substitution*. Each needs a separate research fix.

### F1 — The discrete metric tensor `g^{ab}` is never constructed

**Where.** G1 Def 15 (2004.14810 TeX line 325, text line 786), G1 Eq 25, G1 §3.3 Eqs 86–90. G2 §5 and G3 §5 reuse.

**Statement of the flaw.** Every formula that mentions $g^{ab}$, $\sqrt{-g}$, $d\mu_g$, $\delta/\delta g^{ab}$, or the Christoffel symbols $\Gamma^\rho_{\mu\nu}$ on the *discrete* side uses an object whose components are never defined. JGORARD writes "let $g$ be a discrete Lorentzian metric of signature $(-,+,+,+)$" (Def 15) without providing any formula or procedure for constructing its components from the hypergraph / causal-graph combinatorics.

**Why it's major (not just an arithmetic oversight).** The central §3.3 argument computes $\delta S[g^{ab}]/\delta g^{ab}$ — a *functional derivative with respect to the metric components*. This requires:
- the metric to have components you can vary;
- a vector space of metric perturbations;
- an inner product (to take a gradient).

None of these exists on a discrete hypergraph without extra choices. JGORARD makes the extra choices implicitly ("by analogy"). The whole §3.3 "derivation" is a continuum manipulation applied to a discrete symbol without defining the object.

**What refutation looks like.** Lean-level formalisation showing that:
- a naive coercion of the hypergraph to a matrix of distances does not give a non-degenerate metric tensor,
- any construction of $g^{ab}$ on a discrete hypergraph requires auxiliary data (e.g., a chosen basis at each vertex), and
- different choices of auxiliary data give different "metrics", so there is no canonical one — meaning the §3.3 computation is choice-dependent and undefined absent those choices.

**Status in docs.**
- `notes/2004.14810_close_reading.md` §3.3 analysis.
- `notes/severity_taxonomy.md` S2.
- `FINDINGS.md` S2 table row 3.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F1NoMetric.lean`:
- `MetricConstruction V := DHyp V → V → V → ℝ` — the weakest type inhabited by any procedure "hypergraph → bilinear form".
- `hypergraph_does_not_determine_metric` — exhibits two distinct constructions (constant-zero and constant-one), showing `g^{ab}` is not pinned down by hypergraph data alone.
- `metric_construction_is_never_unique (Φ)` — for *any* construction `Φ`, `Ψ := Φ + 1` is a distinct construction.
- `no_canonical_metric_from_hypergraph_alone` — no unique canonical `Φ` exists.
- `action_depends_on_construction_choice` — any injective `S : MetricConstruction → ℝ` gives different action values under different constructions.
- All axiom-clean. These theorems are facts about the function type `MetricConstruction V` and do not mention G1. The finding that Def 15 (`papers/gorard_2004.14810.txt` line 786) gives no construction is a reading of the paper.

**Sharpening (2026-05, macro-observer note).** The macro-observer analysis recorded in `notes/phajek_macro_observer_notes.txt` gives the precise positive form of this flaw. A graph does not determine a metric — it determines a *moduli of Riemannian manifolds*. Edge-length embeddings into $\mathbb{R}^n$ followed by shape detection (TDA / DEC / manifold-learning) produce candidate geometries as submanifolds of $\mathbb{R}^n$, and both the embedding and the detection are many-valued. The non-uniqueness is not an artefact of a crude coercion — it is unavoidable. By the **Nash embedding theorem**, every Riemannian manifold embeds isometrically in some $\mathbb{R}^n$, so the single assumption "graph shortest-path distance = geodesic distance of the assigned metric" is *already* satisfied by a positive-dimensional family of manifolds. No procedure resting on that assumption can pin down a unique target. The §3.3 functional-derivative computation is therefore underdetermined for a strictly stronger reason than the absent components: even granting components, the manifold they would belong to is a class, not a point. Discrete invariants — clique size bounding embedding dimension, discrete curvature constraining curvature, the clique complex constraining topology — act as *obstructions* that narrow this moduli but do not collapse it; collapsing to finitely many classes requires large-scale / Gromov coarse-graining data the corpus never supplies.

**Sharpening (2026-05-30, paclet-design note).** The moduli observation is no longer a critique only — it has become structural in PHAJEK's `SyntheticInfrageometry` paclet. The *primitive* synthetic operations now come as one-parameter families of inequivalent definitions:
- `InfraPerpendicularQ` (`resources/SyntheticInfrageometry/Kernel/InfraEquality.wl`) exposes Schoenberg, Centroid (balanced-feet test), and four-corner-wedge methods, each a distinct invariant.
- `FindInfraShellCenter` (`resources/SyntheticInfrageometry/Kernel/InfraShell.wl`) exposes bisector, chord, and equidistant methods.
- `FindLineStructure` / `InfraLineStructure` (`resources/SyntheticInfrageometry/Kernel/InfraLineStructure.wl`) treats a "line" as a *consistent path system*, with multiple T1–T5 methods and an explicit tie-break study; the structure is the choice.

These primitives realize F1 at the synthetic level: *every* basic geometric construction admits a moduli of inequivalent realisations, and the paclet treats this as a feature (an explicit `Method` argument) rather than a flaw. The conclusion is that JGORARD's `g^{ab}` is not the only object that lacks a canonical definition — perpendicularity, the centre of a shell, and the notion of a line all share the same structure. Any derivation that quietly fixes a choice (as G1 Def 15 does for the metric) is choosing one representative of a moduli without admitting it, and competing equally-valid derivations exist for every alternative method.

### F2 — Fiat orthonormality of non-parallel hyperedges

**Where.** G1 §3.2 TeX line 840 (text line 2065). Reused in G2 §5, G3 §5.

**Statement.** "We also assume that all pairs of hyperedges which are not parallel (i.e. incident to the same set of vertices) can be considered to be orthonormal."

**Why it's major.** Orthonormality is a property of a bilinear form $g(v, w)$. With no bilinear form defined, the statement is vacuous. Moreover, the subsequent machinery — sectional curvature, Riemann tensor — depends on treating pairs of "tangent vectors" as orthonormal, which requires the bilinear form to exist and to render them orthonormal. JGORARD uses this fiat assumption to *transport* Riemannian-geometry formulas onto the hypergraph side without constructing the geometric structures those formulas depend on.

**What refutation looks like.** Lean-level proof that the assumption is *non-constructive*: no bilinear form on the hyperedge set renders every non-parallel pair orthonormal without additional choices.

**Status.** Documented in `notes/severity_taxonomy.md` S2, `notes/2004.14810_close_reading.md`.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F2Orthonormality.lean`:
- `Form E := E → E → ℝ`; `Orthonormal g e₁ e₂ := g e₁ e₁ = 1 ∧ g e₂ e₂ = 1 ∧ g e₁ e₂ = 0`.
- `orthonormality_depends_on_form` — orthonormality is a property of the form, not of the hyperedges: exhibits `g₁` (Kronecker) making `(true, false)` orthonormal, and `g₂ ≡ 0` for which it fails.
- `orthonormalising_form_not_unique` — two distinct forms both render the same pair orthonormal.
- All axiom-clean. These theorems are facts about functions on `Bool × Bool` and do not mention G1. The finding that line 2065 of `papers/gorard_2004.14810.txt` assumes orthonormality without a bilinear form is a reading of the paper.

### F3 — "Asymptotic dimensionality preservation" is tautological

**Where.** G1 §3.3 TeX line 890 (Eq 87, text lines 2203-2206), and the subsequent "derivation" of the Einstein equations.

**Statement.** JGORARD defines "asymptotic dimensionality preservation" as the condition
$$\frac{\delta S[g^{ab}]}{\delta g^{ab}} \to 0$$
and then concludes that conservative + asymptotically-dimensionality-preserving rules satisfy the vacuum Einstein equations. But the above equation *is* the Euler-Lagrange equation of the Einstein-Hilbert action; saying "the Euler-Lagrange equation holds in the limit" and deducing "the equations of motion hold" is tautological.

**Why it's major.** It masquerades as a derivation ("we have shown that causally-invariant and asymptotically-dimensionality-preserving rules give GR") when it is a restatement of the definition. A reader who takes JGORARD's abstract at face value will believe GR has been derived.

**What refutation looks like.** Lean-level proof that, if we *define* "asymptotic dimensionality preservation" the way JGORARD does, the "Einstein equations" claim follows by definitional unfolding alone — no combinatorial or geometric content. I.e., prove the implication is *logically trivial*.

**Status.** Documented in `notes/severity_taxonomy.md` S3, `notes/corpus_assessment.md`.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F3Tautology.lean`:
- `asymptoticDimPreservation_iff_eulerLagrange : AsymptoticDimPreservation P g ↔ EulerLagrange P g := Iff.rfl`. Both definitions have the body `P.variation g = 0`. The encoding follows G1 eq. 87 (`papers/gorard_2004.14810.txt` lines 2203-2206). The encoding is a reading of the paper, and the theorem holds because the two definitions are equal.
- Axiom-clean (`#print axioms` confirms `[propext, Classical.choice, Quot.sound]` only).

### F4 — "Causal invariance ⇒ discrete general covariance" tautology

**Where.** G1 §2.3.

**Statement.** Causal invariance is *defined* as update-order independence of the causal structure. "Discrete general covariance" is *defined* in G1 §2.3 as the same thing. The biconditional "causal invariance ⇔ general covariance" is thus two definitions of the same phenomenon.

**Status.** Documented.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F4Tautology.lean`:
- `causalInvariance_iff_discreteGeneralCovariance : CausalInvariance cg ↔ DiscreteGeneralCovariance cg := Iff.rfl`. Both definitions have the body `∀ u v, cg u = cg v`. The identification follows G1 lines 1066-1075 and is a reading of the paper.
- `#print axioms` reports "does not depend on any axioms".

### F5 — "Discrete sum → continuum integral under weak ergodicity"

**Where.** G1 Eq 88 TeX line 898 (text line 2214); reused verbatim in G2 §5 and G3 §5.

**Statement.** "In the continuum limit of an arbitrarily large causal graph, this sum becomes (subject to a weak ergodicity assumption on the dynamics of the causal graph) an integral."

**Why it's major.** Neither *"becomes"* (which topology? $\Gamma$-convergence? Mosco? pointwise? $L^p$?) nor *"weak ergodicity"* (precise definition?) is specified. The closest rigorous version in the causal-set-theory literature is the Sorkin–Benincasa–Dowker conjecture, which is *open* — partial numerical support (Cunningham 2018) only. JGORARD asserts it as established.

**What refutation looks like.** Pin down the precise claim, then either (a) show that no existing convergence theorem delivers it under Wolfram-model-specific hypotheses, or (b) construct a rule whose discrete sum provably does not converge to the continuum integral in any reasonable topology.

**Status.** Documented; Lean stub `ContinuumLimitClaim` in `Limit.lean`.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F5Illdefined.lean`:
- `ConvergenceNotion := (ℕ → ℝ) → ℝ → Prop` — abstract parameter standing in for the unspecified "topology of convergence" in JGORARD's "becomes".
- `becomes_is_underdetermined` — exhibits a sequence (`n ↦ 1/(n+1)`) and a target (`0`) for which two natural notions disagree: `StandardLimit` affirms, `EventuallyEquals` denies.
- `claim_is_vacuous_without_convergence_notion (s L) : ∃ C, C s L` — for any sequence and target, there is a convergence notion under which the claim holds.
- `different_notions_give_different_limits (s L₁ L₂)` — for the same sequence, there are notions giving any two target values. "Becomes" is not a function of the sequence alone.
- All axiom-clean.

**Sharpening (2026-05, macro-observer note).** The "becomes" is underdetermined not only in its topology but in whether the limit object exists as a probability measure at all. A continuum limit of a sequence of finite rewriting states is a *projective limit* of finite-dimensional laws. The macro-observer note (`notes/phajek_macro_observer_notes.txt`) records HVLE's argument that such a projective family need not extend to a countably-additive probability measure: it may extend only to a *charge* (a finitely-additive or signed set function), or run into Suslin-type non-measurability, because the Kolmogorov extension theorem requires topological regularity the rewriting setting does not supply (Orbanz framework). This is an obstruction *independent* of the F1–F4, F6, F7 structural flaws and independent of the unspecified-topology problem above — even after a topology is fixed, the joint law of the limiting object can fail to exist. Scope boundary: marginal weak-convergence statements (a single counting measure converging to Lebesgue, Wasserstein-rate bounds on one-dimensional projections — the kind proved in the A-series of this project) are unaffected; the obstruction bites at the joint law of the whole limiting process, which is exactly the object G1 Eq 88 silently assumes.

**Sharpening (2026-05-30, synthetic-measure note).** PHAJEK's `SyntheticInfrageometry` paclet now exposes a *synthetic* measure-theoretic primitive `InfraMeasure` (`resources/SyntheticInfrageometry/Kernel/Tools.wl`), with companions `InfraBoundary` and an `infraRepType` classifier (renamed from `VisitMeasure` in the unification commit `9f34fb4`). This makes the F5 distinction structural: a measure attached to a graph is now an *infrageometric construction* of its own — built directly from the synthetic data — and is not identified with the probability measure of any continuum limit. Whether such a synthetic measure can be realised as the marginal of a probability law on a continuum object is a separate question (the HVLE projective-limit obstruction recorded in the previous sharpening). G1 Eq 88 conflates the two: it writes the "discrete sum" as if it were already a finite-state expectation of a continuum-side integral. The synthetic-side primitive shows this is a category error — the discrete object is a different kind of mathematical entity, and the bridge between the two is the obstruction, not an identity.

### F6 — G3's comparison starts from initial data sampled from the target geometry

**Where.** G3 = `papers/gorard_2102.09363.txt`: line 6080 (Poisson replacement), lines 6148-6152 and 6179 (sampled initial data), lines 6185-6192 (colouring by the analytic conformal factor).

**Paper text.**
1. Line 6080 replaces "the assumption of weak ergodicity of the causal graph dynamics with the much stronger assumption of uniform Poisson distribution of the rewrite events". G3 gives no proof that the named rule produces Poisson-distributed rewrite events.
2. The continuum limit of the Benincasa–Dowker action (lines 6110-6120) holds under the stated assumptions of zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood. G3 cites numerical support (Cunningham 2018) for these assumptions.
3. The initial hypergraph is built "by means of a Poisson point process" so that it is "faithfully embeddable into a given Lorentzian manifold (M, g)" (lines 6148-6152). G3 uses this procedure for "the standard Brill-Lindquist binary black hole initial data" (line 6179).
4. The hypergraphs in Figures 73-77 are coloured with the analytic Schwarzschild conformal factor ψ (eq. 391, lines 6185-6192).

**Finding (READ).** The comparison between the rule and the numerical solution starts from a hypergraph sampled from the target initial-data geometry. The rule is never run from initial data that does not encode the target geometry. The paper does not state the link cut-off value (line 6176), the update order, or the number of events per unit of the time coordinate.

**Lean.** `Refutations/F6Circularity.lean` defines `CircularReconstruction` with the hypothesis `reconstruct (sample t) = t` and restates it as `CircularReconstruction.comp_eq_id`. The file does not model G3's procedure and does not prove that the procedure satisfies the hypothesis. The evolved hypergraphs at t = 6M, 12M and 24M are not the sampled initial data. Status: the Lean file is VACUOUS with respect to G3. See `STATUS_OF_GORARD_CLAIMS.md`, Claim 2.

### F7 — The named rule conserves edge count. No dimension bound is proved

**Where.** G3 abstract lines 50-52 and line 6202.

**Statement.** G3 states that the rule
$$\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \to \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$$
"provably satisfies the Einstein field equations in the continuum limit". G3 gives no proof for this rule.

**PROVED.** The rule has $|LHS|=|RHS|=4$ (`CandidateCatalog.gorardNamedRule_isConservative`), so every application and every chain of applications preserves the edge count (`Refutations.gorardNamedRule_application_preserves_size`, `Refutations.gorardNamedRule_applications_preserve_size`, `Application.size_result_of_conservative`, `size_preserved_by_applications`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

**MEASURED.** The log-log cone-growth exponent of the causal graph lies between 0.985 and 1.256 on cycles, paths and 3D grids of up to 300 edges and 2000 events. The SetReplace and Python runs disagree on the exponent for every seed except the 6-cycle, by up to 0.271 on the 4x4x4 grid, and the cause is not determined. Table and scripts: `STATUS_OF_GORARD_CLAIMS.md`, Claim 1.

**OPEN.** A bound on the causal-graph cone growth of the rule (O1 in `STATUS_OF_GORARD_CLAIMS.md`). Edge-count conservation alone does not give such a bound. A bounded spatial ball count holds for every finite hypergraph, so it does not distinguish this rule.

### F8 — G4 title-body gap: "Discrete Singularity Theorems"

**Where.** G4 (arXiv:2303.07282) title, abstract, §1.

**Statement.** Title promises discrete Raychaudhuri, discrete singularity theorems. Body contains: *no* discrete Raychaudhuri equation, *no* discrete expansion scalar, *no* discrete energy condition, *no* discrete stress-energy tensor; zero occurrences of "shear" or "vorticity". Paper's own conclusions explicitly mark these as open problems.

**Status.** Documented in `notes/2303.07282_close_reading.md`, `FINDINGS.md` S6.

## Summary table

| # | Flaw | Type | Doc | Lean formalisation |
|---|---|---|---|---|
| F1 | Discrete $g^{ab}$ never constructed | structural | [severity_taxonomy §S2#3](notes/severity_taxonomy.md) | `Refutations/F1NoMetric.lean` (statements about project definitions) |
| F2 | Fiat orthonormality | structural | [severity_taxonomy §S2#5](notes/severity_taxonomy.md) | `Refutations/F2Orthonormality.lean` (statements about project definitions) |
| F3 | Dim-preservation tautology | logical | [severity_taxonomy §S3#9](notes/severity_taxonomy.md) | `Refutations/F3Tautology.lean` (statements about project definitions) |
| F4 | Causal-inv ⇒ GC tautology | logical | [severity_taxonomy §S3#7](notes/severity_taxonomy.md) | `Refutations/F4Tautology.lean` (statements about project definitions) |
| F5 | Discrete sum → integral ill-defined | bridge | [2004.14810_close_reading](notes/2004.14810_close_reading.md) | `Refutations/F5Illdefined.lean` (statements about project definitions) |
| F6 | G3 initial data sampled from the target geometry | methodological (READ) | [2102.09363_close_reading](notes/2102.09363_close_reading.md) | `Refutations/F6Circularity.lean` restates its own hypothesis and does not model G3 |
| F7 | Named rule conserves edge count, cone exponent measured near 1 | PROVED (conservation) + MEASURED (exponent) | [empirical_refutation](notes/empirical_refutation.md), [phase1_selfaudit](results/phase1_selfaudit/) | `Refutations/F7NamedRuleStructure.lean` (conservation only). Dimension bound OPEN |
| F8 | G4 title-body gap | overclaim | [2303.07282_close_reading](notes/2303.07282_close_reading.md) | n/a |

The Lean files in `lean/InfraFormalization/Refutations/` prove facts about the project's own definitions. F3 and F4 hold by `Iff.rfl`. F1, F2 and F5 are facts about function types and the constant-`True` predicate. F6 restates its own hypothesis. F7 proves edge-count conservation for the named rule. No file proves a bound on the dimension of the named rule's causal graph. The link from each Lean statement to the paper is a reading of the paper text, listed per claim in [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md).

F8 is an overclaim — the 2303.07282 paper's title promises discrete singularity theorems that are not in the body (JGORARD concedes this in the paper's conclusion).
