# Major structural flaws in the Gorard corpus

Distinguishes the *arithmetic errors* (minor — patchable by substituting correct formulas) from the *structural/conceptual flaws* (major — cannot be fixed by arithmetic). The major ones need to be exposed, proven false, and replaced by genuine constructions if the program is to be salvaged.

This document is the canonical reference for the *major* side. For the *minor* side (Eq 342 tube coefficient, Eq 344 Ollivier directional/scalar) see [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) (S1 class) and [`results/phase2_continuum/`](results/phase2_continuum/).

## Minor flaws (arithmetic; fixable)

- **Eq 342 (tube-volume coefficient).** Wrong algebraic form: $(d{-}1)(R - \mathrm{Ric}(u,u))/(d{+}1)$ vs correct $(R + \mathrm{Ric}(u,u))/(6(d{+}1))$. Factor-2 off on $S^2$, factor-6 off on $S^3$. Status: refuted (four rails), correct form formalised in Lean as `Infra.GrayTubeLeading` with concrete disagreement proofs `gray_vs_gorard_disagree_on_S2/S3`.
- **Eq 344 (Ollivier Wasserstein).** Scalar $R$ vs directional $\mathrm{Ric}(v,v)$. Factor-2 off on $S^2$. Status: refuted against Ollivier's cited JFA 2009 theorem, correct form formalised in Lean as `Infra.OllivierIdentityLeading`.

These can be *patched* by substituting the right formula. The rest of §3 remains structurally flawed regardless.

## Major structural flaws

Each is *not fixable by arithmetic substitution*. Each needs a separate research fix.

### F1 — The discrete metric tensor `g^{ab}` is never constructed

**Where.** G1 Def 15 (2004.14810 line 325), G1 Eq 25, G1 §3.3 Eqs 86–90. G2 §5 and G3 §5 reuse.

**Statement of the flaw.** Every formula that mentions $g^{ab}$, $\sqrt{-g}$, $d\mu_g$, $\delta/\delta g^{ab}$, or the Christoffel symbols $\Gamma^\rho_{\mu\nu}$ on the *discrete* side uses an object whose components are never defined. Gorard writes "let $g$ be a discrete Lorentzian metric of signature $(-,+,+,+)$" (Def 15) without providing any formula or procedure for constructing its components from the hypergraph / causal-graph combinatorics.

**Why it's major (not just an arithmetic oversight).** The central §3.3 argument computes $\delta S[g^{ab}]/\delta g^{ab}$ — a *functional derivative with respect to the metric components*. This requires:
- the metric to have components you can vary;
- a vector space of metric perturbations;
- an inner product (to take a gradient).

None of these exists on a discrete hypergraph without extra choices. Gorard makes the extra choices implicitly ("by analogy"). The whole §3.3 "derivation" is a continuum manipulation applied to a discrete symbol without defining the object.

**What refutation looks like.** Lean-level formalisation showing that:
- a naive coercion of the hypergraph to a matrix of distances does not give a non-degenerate metric tensor,
- any construction of $g^{ab}$ on a discrete hypergraph requires auxiliary data (e.g., a chosen basis at each vertex), and
- different choices of auxiliary data give different "metrics", so there is no canonical one — meaning the §3.3 computation is choice-dependent and undefined absent those choices.

**Status in docs.**
- `notes/2004.14810_close_reading.md` §3.3 analysis.
- `notes/severity_taxonomy.md` S2 #3.
- `FINDINGS.md` S2 table row 3.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F1NoMetric.lean`:
- `MetricConstruction V := DHyp V → V → V → ℝ` — the weakest type inhabited by any procedure "hypergraph → bilinear form".
- `hypergraph_does_not_determine_metric` — exhibits two distinct constructions (constant-zero and constant-one), showing `g^{ab}` is not pinned down by hypergraph data alone.
- `metric_construction_is_never_unique (Φ)` — for *any* construction `Φ`, `Ψ := Φ + 1` is a distinct construction.
- `no_canonical_metric_from_hypergraph_alone` — no unique canonical `Φ` exists.
- `action_depends_on_construction_choice` — any injective `S : MetricConstruction → ℝ` gives different action values under different constructions. Corollary: `δS/δg^{ab}` in G1 Eq 87 is a function of the construction choice, not of the hypergraph.
- All axiom-clean.

### F2 — Fiat orthonormality of non-parallel hyperedges

**Where.** G1 §3.2 line 840. Reused in G2 §5, G3 §5.

**Statement.** "We also assume that all pairs of hyperedges which are not parallel (i.e. incident to the same set of vertices) can be considered to be orthonormal."

**Why it's major.** Orthonormality is a property of a bilinear form $g(v, w)$. With no bilinear form defined, the statement is vacuous. Moreover, the subsequent machinery — sectional curvature, Riemann tensor — depends on treating pairs of "tangent vectors" as orthonormal, which requires the bilinear form to exist and to render them orthonormal. Gorard uses this fiat assumption to *transport* Riemannian-geometry formulas onto the hypergraph side without constructing the geometric structures those formulas depend on.

**What refutation looks like.** Lean-level proof that the assumption is *non-constructive*: no bilinear form on the hyperedge set renders every non-parallel pair orthonormal without additional choices.

**Status.** Documented in `notes/severity_taxonomy.md` S2 #5, `notes/2004.14810_close_reading.md`.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F2Orthonormality.lean`:
- `Form E := E → E → ℝ`; `Orthonormal g e₁ e₂ := g e₁ e₁ = 1 ∧ g e₂ e₂ = 1 ∧ g e₁ e₂ = 0`.
- `orthonormality_depends_on_form` — orthonormality is a property of the form, not of the hyperedges: exhibits `g₁` (Kronecker) making `(true, false)` orthonormal, and `g₂ ≡ 0` for which it fails.
- `orthonormalising_form_not_unique` — two distinct forms both render the same pair orthonormal.
- `gorard_orthonormality_is_non_canonical` — Gorard's §3.2 fiat does not single out a unique form.
- All axiom-clean.

### F3 — "Asymptotic dimensionality preservation" is tautological

**Where.** G1 §3.3 line 890 (Eq 87), and the subsequent "derivation" of the Einstein equations.

**Statement.** Gorard defines "asymptotic dimensionality preservation" as the condition
$$\frac{\delta S[g^{ab}]}{\delta g^{ab}} \to 0$$
and then concludes that conservative + asymptotically-dimensionality-preserving rules satisfy the vacuum Einstein equations. But the above equation *is* the Euler-Lagrange equation of the Einstein-Hilbert action; saying "the Euler-Lagrange equation holds in the limit" and deducing "the equations of motion hold" is tautological.

**Why it's major.** It masquerades as a derivation ("we have shown that causally-invariant and asymptotically-dimensionality-preserving rules give GR") when it is a restatement of the definition. A reader who takes Gorard's abstract at face value will believe GR has been derived.

**What refutation looks like.** Lean-level proof that, if we *define* "asymptotic dimensionality preservation" the way Gorard does, the "Einstein equations" claim follows by definitional unfolding alone — no combinatorial or geometric content. I.e., prove the implication is *logically trivial*.

**Status.** Documented in `notes/severity_taxonomy.md` S3 #9, `notes/claim_assessment.md`.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F3Tautology.lean`:
- `gorard_dim_preservation_is_euler_lagrange : AsymptoticDimPreservation P g ↔ EulerLagrange P g := Iff.rfl` — the biconditional is definitional unfolding.
- `gorard_section_3_3_contentless` — the Gorard chain (conservative ∧ causal-invariant ∧ asymp-dim-pres ⇒ vacuum EFE) reduces on its EFE leg to the identity function on `AsymptoticDimPreservation P g`.
- Axiom-clean (`#print axioms` confirms `[propext, Classical.choice, Quot.sound]` only).

### F4 — "Causal invariance ⇒ discrete general covariance" tautology

**Where.** G1 §2.3.

**Statement.** Causal invariance is *defined* as update-order independence of the causal structure. "Discrete general covariance" is *defined* in G1 §2.3 as the same thing. The biconditional "causal invariance ⇔ general covariance" is thus two definitions of the same phenomenon.

**Status.** Documented.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F4Tautology.lean`:
- `gorard_causal_invariance_is_general_covariance : CausalInvariance cg ↔ DiscreteGeneralCovariance cg := Iff.rfl`.
- `#print axioms` reports "does not depend on any axioms" — the cleanest possible certificate; the biconditional is Lean-definitional, i.e., it is literally the same proposition twice.

### F5 — "Discrete sum → continuum integral under weak ergodicity"

**Where.** G1 Eq 88 line 898; reused verbatim in G2 §5 and G3 §5.

**Statement.** "In the continuum limit of an arbitrarily large causal graph, this sum becomes (subject to a weak ergodicity assumption on the dynamics of the causal graph) an integral."

**Why it's major.** Neither *"becomes"* (which topology? $\Gamma$-convergence? Mosco? pointwise? $L^p$?) nor *"weak ergodicity"* (precise definition?) is specified. The closest rigorous version in the causal-set-theory literature is the Sorkin–Benincasa–Dowker conjecture, which is *open* — partial numerical support (Cunningham 2018) only. Gorard asserts it as established.

**What refutation looks like.** Pin down the precise claim, then either (a) show that no existing convergence theorem delivers it under Wolfram-model-specific hypotheses, or (b) construct a rule whose discrete sum provably does not converge to the continuum integral in any reasonable topology.

**Status.** Documented; Lean stub `ContinuumLimitClaim` in `Limit.lean`.

**Lean status.** Formalised in `lean/InfraFormalization/Refutations/F5Illdefined.lean`:
- `ConvergenceNotion := (ℕ → ℝ) → ℝ → Prop` — abstract parameter standing in for the unspecified "topology of convergence" in Gorard's "becomes".
- `becomes_is_underdetermined` — exhibits a sequence (`n ↦ 1/(n+1)`) and a target (`0`) for which two natural notions disagree: `StandardLimit` affirms, `EventuallyEquals` denies.
- `claim_is_vacuous_without_convergence_notion (s L) : ∃ C, C s L` — for any sequence and target, there is a convergence notion under which the claim holds.
- `different_notions_give_different_limits (s L₁ L₂)` — for the same sequence, there are notions giving any two target values. "Becomes" is not a function of the sequence alone.
- All axiom-clean.

### F6 — G3's circular "derivation" of EFE

**Where.** G3 §5, TeX lines 6080 (weak ergodicity → Poisson replacement) and 6152 (Poisson-sample the target manifold).

**Statement.** G3's headline claim is that a specific rule "provably satisfies the Einstein field equations in the continuum limit." The chain of reasoning:
1. Define discrete d'Alembertian $B^{(d)}$ on causal graphs (from Benincasa–Dowker causal-set theory).
2. *Replace the weak-ergodicity assumption with the much stronger assumption of uniform Poisson distribution.* [Verbatim, TeX line 6080.]
3. Under Poisson sampling, $\langle B^{(d)}_\rho \phi \rangle \to \Box \phi - \tfrac12 R \phi$ (Benincasa–Dowker 2010, conjectural).
4. Build the initial hypergraph by Poisson-sprinkling vertices into the known Schwarzschild / Kerr spacetime. [TeX line 6152.]
5. Observe that the BD-action counting on this sample recovers the curvature of the manifold we started with.

**Why it's major.** The target manifold is *input* to the construction, not output. Any derivation in which the thing-to-be-derived is pre-assumed is circular. The "Wolfram-model rewriting rule" label is preserved rhetorically but has been replaced mathematically by "Poisson point process on a given Lorentzian manifold."

**Status.** Documented in `notes/2102.09363_close_reading.md`; the precise line references (6080, 6152) are explicit in the close-reading note.

### F7 — The named rule is structurally 1-dimensional

**Where.** G3 abstract + G3 TeX line 6202.

**Statement.** G3 advertises the specific rule
$$\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \to \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$$
as "provably satisfying the Einstein field equations in the continuum limit." Edge-conservation ($|LHS|=|RHS|=4$) forces the state size to be constant and, empirically on every tested seed, the causal cone grows linearly. Such a causal graph cannot have GH-limit dimension $\geq 2$, let alone 3+1.

**Status.**
- Empirical refutation: `results/phase1_selfaudit/README.md` (SetReplace + independent Python rewriter agree on 9 seeds: cone dimension ≈ 1).
- Structural theorem: `InfraFormalization.Application.size_result_of_conservative` (Lean, machine-verified, axiom-clean).
- Full "no $n \ge 2$ GH limit for conservative rules" is pending a state-size-per-level argument (not currently proved).

### F8 — G4 title-body gap: "Discrete Singularity Theorems"

**Where.** G4 (arXiv:2303.07282) title, abstract, §1.

**Statement.** Title promises discrete Raychaudhuri, discrete singularity theorems. Body contains: *no* discrete Raychaudhuri equation, *no* discrete expansion scalar, *no* discrete energy condition, *no* discrete stress-energy tensor; zero occurrences of "shear" or "vorticity". Paper's own conclusions explicitly mark these as open problems.

**Status.** Documented in `notes/2303.07282_close_reading.md`, `FINDINGS.md` S6 #15.

## Summary table

| # | Flaw | Type | Doc | Lean formalisation |
|---|---|---|---|---|
| F1 | Discrete $g^{ab}$ never constructed | structural | [severity_taxonomy §S2#3](notes/severity_taxonomy.md) | ✓ `Refutations/F1NoMetric.lean` |
| F2 | Fiat orthonormality | structural | [severity_taxonomy §S2#5](notes/severity_taxonomy.md) | ✓ `Refutations/F2Orthonormality.lean` |
| F3 | Dim-preservation tautology | logical | [severity_taxonomy §S3#9](notes/severity_taxonomy.md) | ✓ `Refutations/F3Tautology.lean` |
| F4 | Causal-inv ⇒ GC tautology | logical | [severity_taxonomy §S3#7](notes/severity_taxonomy.md) | ✓ `Refutations/F4Tautology.lean` |
| F5 | Discrete sum → integral ill-defined | bridge | [2004.14810_close_reading](notes/2004.14810_close_reading.md) | ✓ `Refutations/F5Illdefined.lean` |
| F6 | G3 circular "derivation" | methodological | [2102.09363_close_reading](notes/2102.09363_close_reading.md) | structurally exposed |
| F7 | Named rule is 1-D | empirical + structural | [empirical_refutation](notes/empirical_refutation.md), [phase1_selfaudit](results/phase1_selfaudit/) | T1 (proved) + empirical |
| F8 | G4 title-body gap | overclaim | [2303.07282_close_reading](notes/2303.07282_close_reading.md) | n/a |

F1–F5 are now formalised in `lean/InfraFormalization/Refutations/`. F6–F8 are exposed sufficiently for citation purposes (F6 is methodological, F7 is empirical, F8 is an overclaim with no body content to formalise).
