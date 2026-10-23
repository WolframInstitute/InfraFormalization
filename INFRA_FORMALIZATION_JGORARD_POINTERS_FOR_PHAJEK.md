# InfraFormalization — JGORARD-corpus pointers for PHAJEK

Standalone reading guide answering PHAJEK's three questions about the
JGORARD papers (arxiv:2004.14810, 2102.09363, 2303.07282, 2011.12174 —
G1, G2, G3, G4):

1. Are there false claims?
2. Are there genuinely novel claims?
3. Does anything beyond summarising discrete GR on a graph/hypergraph
   substrate, comparing one hand-picked rule's animation to known
   manifolds, actually demonstrate that they match in any meaningful
   way?

Everything cited below is in the `infra_formalization` repo (private,
Wolfram-Institute audience). Lean files are sorry-free and axiom-clean
unless explicitly noted.

---

## Direct answers

**(1) False claims — yes, with severity classification.** Catalogued
across G1–G4 in `MAJOR_FLAWS.md` and `FINDINGS.md`. Severity rubric in
`notes/severity_taxonomy.md`. Each refuted in Lean
(`Refutations/F1NoMetric` ... `F7NamedRuleStructure`). The central finding is
F6 — the central derivation in G3 §5 is **circular**: the metric is
Poisson-sprinkled from the *target manifold*, then the "derivation"
runs `manifold → sprinkled-points → bin → reconstruct manifold`. The
Lean refutation `circular_procedure_is_identity` makes this precise.
This is not a minor error; it is the load-bearing argument of the
paper, and it is vacuous.

**(2) Genuinely novel claims in JGORARD's corpus — essentially none of
the substantive technical content is novel-to-JGORARD.** Cataloguing
what's there:

- *The hypergraph-rewriting substrate itself* is not his — it is the
  Wolfram physics project's framing, and even that is a re-presentation
  of causal-set / pregeometry programs going back to Bombelli-Lee-Meyer
  -Sorkin (1987) and Penrose's spin networks (1971).
- *Discrete Forman-Ricci, Ollivier-Ricci, Wolfram-Hausdorff dimension,
  Regge calculus, causal-set theory* — all cited from prior literature
  (Forman 2003, Ollivier 2009, Bombelli et al, Regge 1961, Sorkin
  1991). The hypergraph re-statement adds nothing new; the underlying
  theorems and identities all belong to those sources.
- *The specific named rule* (G2 §3) is a particular hand-picked
  candidate. Picking a rule is novel as an action but produces
  1-dimensional spacetime structurally, so it does not demonstrate
  anything novel about geometric emergence.
- *The end-to-end "derivation of EFE from hypergraph rewriting"* (G3
  §5) would be genuinely novel if it worked. **It does not work:** the
  derivation is circular — the continuum metric is Poisson-sprinkled
  from the *target manifold*, then the procedure runs `manifold →
  sprinkled-points → bin → reconstruct manifold`. This is `F6Circularity.lean`.
  The novelty being claimed is therefore not actually present.
- *Where JGORARD *deviates* from cited literature, he is wrong:* G3
  Eq 344 uses scalar `R` where Ollivier's cited JFA 2009 theorem has
  directional `Ric(v,v)` (off by factor 2 on S²); G3 Eq 342 has the
  wrong tube-volume coefficient (off by factor 2 on S², factor 6 on
  S³). These are not novel results — they are mis-statements of cited
  theorems. Verdicts: `results/phase2_continuum/eq344_verdict.md` and
  `eq342_verdict.md`.
- *Headline structural claims* — "causal invariance ⇒ general
  covariance", "asymptotic dimensionality preservation ⇒ general
  covariance" — are tautological as stated (`F3Tautology.lean`,
  `F4Tautology.lean`). A tautology can be stated for the first time
  by anyone; that does not make it a non-trivial novel claim.
- *G4's discrete singularity theorem* — title and body do not match;
  the body does not prove the theorem the title states. Documentary
  flaw F8.

**Summary:** the substantive technical content is either (a) cited
prior literature, (b) wrong restatements of cited literature, (c)
tautological, or (d) circular. The *attempt* at an end-to-end
derivation is novel as an attempt but failed; the *named-rule
simulation* is novel as a choice but produces 1D spacetime so does
not demonstrate the claimed agreement. **There is no point in the
corpus where JGORARD establishes a non-trivial novel claim about
emergence of GR (or QM) from hypergraph rewriting that survives
audit.**

**(3) Beyond summary + named-rule simulation — JGORARD's corpus
contains *claims* of more, but no substantive content of more.**
Cataloguing what is actually in the papers, the only material beyond
(a) summary of discrete-GR / Wolfram-physics literature and (b)
the hand-picked named-rule simulation is:

- *G3 §5 — claimed end-to-end derivation of the Einstein field
  equations* by varying a "discrete Einstein-Hilbert action" with
  respect to a "discrete metric tensor". This is the *only*
  substantive piece in the corpus that would qualify as "beyond
  summary + simulation" if it worked. It does not work: the metric
  components are never defined (F1), the variation is performed on
  an undefined object, and the procedure is structurally circular —
  the continuum metric is Poisson-sprinkled from the target manifold
  before the "derivation" begins (F6 `circular_procedure_is_identity`).
  PHAJEK's GR postdoc can verify this herself by reading G3 §5 alongside
  `Refutations/F6Circularity.lean`.
- *G4 — claimed "discrete singularity theorems".* Title states a
  theorem; body does not prove the stated theorem. Documentary flaw
  F8 in `MAJOR_FLAWS.md`.
- *Structural arguments* — "causal invariance ⇒ general covariance",
  "asymptotic dimensionality preservation ⇒ general covariance" —
  presented as substantive bridges from rule-properties to physical
  symmetries. Both tautological as stated (F3, F4).

**On the simulation:** JGORARD's papers contain pictures of the
named-rule trajectory's causal graph and multiway evolution, plus
assertions that they "look like" or "approximate" Lorentzian /
Riemannian manifolds. **What he does *not* do** in the corpus:

- Compute a Gromov-Hausdorff distance between the discrete trajectory
  and any continuum manifold.
- Compute a Wasserstein distance between rule-induced measures and
  any continuum target.
- Extract a discrete Riemann tensor / Ricci tensor / scalar curvature
  from the rule's trajectory and compare to a continuum target.
- Show convergence rates of any kind.
- Demonstrate any quantitative match to any observable (Schwarzschild
  perihelion precession, FLRW expansion rate, gravitational waveform,
  anything).

What the corpus presents as evidence of "match" is qualitative —
pictures of the multiway graph, dimension estimates from ball-volume
growth (which we have shown saturate at 1 for the named rule because
of `|LHS| = |RHS|` size-conservation), and assertions that the limit
"is" Lorentzian. None of this rises to a quantitative comparison.

**The structural blocker:** the named rule has `|LHS| = |RHS|`, so
state size is invariant along every trajectory; ball volume is
therefore bounded by `Fintype.card V`; Wolfram-Hausdorff dimension
collapses to a constant. Causal dimension comes out as 1 on every
seed we tested. **Once causal dim = 1 is structural, every claim
about 4D GR continuum-limit emergence on this rule is necessarily
false** — independent of any arithmetic correction elsewhere in the
corpus. Formal version: `RuleDimensionBounds.trajectory_size_invariant`.
Empirical version: `wolframscript`-driven causal-dim measurements via
the `efficient_rewriting_final` engine. Both reproducible offline.

**Direct answer to PHAJEK's question:** JGORARD does not do anything of
substance beyond summary + the failed named-rule simulation; the
animation does not match continuum GR in any meaningful way (no
quantitative comparison is presented in the corpus, and the
qualitative assertion is structurally false because the rule produces
1D spacetime).

**Editorial note.** The pattern recurs across the corpus: the papers
state results with more certainty than their arguments establish, and
the status of the programme is presented as further advanced than the
proofs support. The formal record exists in machine-checkable form, so
a reader can check each statement with `lake build` and
`#print axioms`.

---

## Pointer list — refutation track

### A. False-claim catalogue (read first)

| File | What's in it |
|---|---|
| **`MAJOR_FLAWS.md`** | Canonical write-up of the eight structural flaws F1–F8. Each entry: where it appears in G1/G2/G3/G4 with line numbers, why the flaw is structural (not just arithmetic), severity. **Start here.** |
| **`FINDINGS.md`** | One-line-per-claim audit table. Severity classes S1 (false statements contradicting cited sources) → S6 (open conjectures). Cross-referenced to verdict files. |
| **`results/phase2_continuum/eq342_verdict.md`** | Tube-volume coefficient (G2 Eq 126 / G3 Eq 342). Off by factor 2 on S², factor 6 on S³. Four-rail refutation. |
| **`results/phase2_continuum/eq344_verdict.md`** | Wasserstein-Ollivier identity (G3 Eq 344) — uses scalar `R` where Ollivier's cited JFA 2009 theorem has directional `Ric(v,v)`. Refuted against the cited source. |
| **`PUBLISHABLE.md` §P1** | "Audit and formal refutation of the JGORARD corpus" — paper target, audience, sufficient-condition list. Most P1 ingredients are in. |

### B. Lean refutations (sorry-free, axiom-clean)

| File | What it proves |
|---|---|
| **`lean/InfraFormalization/Refutations/F1NoMetric.lean`** | The "discrete metric tensor `g^{ab}`" JGORARD varies in §3.3 has no constructed components anywhere in the corpus. |
| **`F2Orthonormality.lean`** | "All non-parallel hyperedges are orthonormal" requires a bilinear form that is never defined. |
| **`F3Tautology.lean`** | "Asymptotic dimensionality preservation ⇒ general covariance" is tautological. |
| **`F4Tautology.lean`** | "Causal invariance ⇒ general covariance" is tautological. |
| **`F5Illdefined.lean`** | "Becomes" / "discrete sum → continuum integral under weak ergodicity" — `becomes_is_underdetermined`. |
| **`F6Circularity.lean`** | **G3's circular "derivation" of EFE** — `circular_procedure_is_identity`. The metric is Poisson-sprinkled from the known target manifold, then the "derivation" is `manifold → sprinkled-points → bin → reconstruct manifold`. **The headline.** |
| **`F7NamedRuleStructure.lean`** | The named rule's `\|LHS\| = \|RHS\|` ⇒ size-conservation ⇒ bounded-volume-growth ⇒ structural 1-dimensionality. |
| F8 | G4's title-body gap (singularity-theorem statement vs body) — documentary, not formalised. |

`#print axioms` on each: depends only on `propext`, `Classical.choice`,
`Quot.sound`. No project axioms, no `sorry`.

### C. Empirical refutation — the named rule's actual dimension

| Pointer | Content |
|---|---|
| **`lean/InfraFormalization/CandidateRuleCatalog.lean` — `gorardNamedRule`** | The rule formalised exactly as written in G2; conservativity proven. |
| **`lean/InfraFormalization/RuleDimensionBounds.lean` — `trajectory_size_invariant`** | Conservative rule ⇒ trajectory-state size invariant ⇒ ball volume bounded by `Fintype.card V` ⇒ Wolfram-Hausdorff dim 0 in the finite case. **Formal counterpart of the empirical refutation.** |
| `wolframscript`-driven causal-dim measurements | Run via `run.sh` against the `efficient_rewriting_final` engine; results bookkept under `results/`. Causal dim = 1 on every tested seed. |

---

## Pointer list — positive arm (what we ARE building)

The project is not just an audit. The positive arm builds the
infrastructure JGORARD *should* have produced before claiming the
result, and it is structured so that the eventual "we got to GR"
claim is *machine-verifiable* rather than asserted.

| File | What it gives |
|---|---|
| **`README.md`** | Project entry; current status headline, structure, the bridge ladder. |
| **`STATUS.md`** | Live state. Most recent landings + counters. |
| **`ROADMAP.md`** | Full-program phase sequencing → BBH-from-hypergraph endgame. Phase A (obligation Props with rate content) → B (rule-search infrastructure) → C (curved-target discharge) → D (BBH). |
| **`BRIDGE_MACHINERY.md`** | The 10-rung bridge ladder: discrete calculus → continuum operators → measure-theoretic limits → connections → curvature → causal/Lorentzian → fields → continuum-limit → specific bridges. Per-rung status. |
| **`COVERAGE_MAP.md`** | Single source of truth for coverage. Per-file content + per-task status. |
| **`MILESTONES.md`** | Per-phase checkboxes. Recent landings list. |
| **`INDEX.md`** | Document navigation + per-Lean-file one-line content summary (~150 files). |
| **`INFRAGEOMETRY.md`** | The conceptual home: Tarski reduction / cellular sheaves / units-emergence / 25-step constructive route to differential geometry / cross-reference to NMURZIN's "Geometry on Combinatorial Objects" paper (which formalises the same synthesis from a different angle). |
| **`GROUNDING_AUDIT.md`** | Per-Lean-object: ✅ grounded on `Hypergraph V` / ⚠ partially grounded / ❌ continuum-island. Audit log. |
| **`GLOSSARY.md`** | Symbol/notation guide. |
| **`LEAN_PHYSICS.md`** | How we align with the Mathlib physics + HepLean ecosystem. |

---

## "Discharged obligations" — what makes this stronger than an audit

This is the bit that distinguishes us from "criticism only". We have a
rule encoded in Lean, evolved in Lean, with a quantitative-rate
convergence proof on its trajectory.

| File | What it does |
|---|---|
| **`lean/InfraFormalization/HypergraphMetricBridges.lean`** | The "obligation lattice". Every continuum-target metric in our zoo (Minkowski, Schwarzschild, FLRW, Reissner-Nordström, de Sitter, S², Kerr, warpedDiag2) carries a Lean-formal `*_from_hypergraph_strong` Prop saying "there exists a hypergraph rewriting trajectory that converges to this metric, with quantitative rate". |
| **`lean/InfraFormalization/WassersteinRate.lean`** | `WassersteinRateObligation`, `ConvergenceRateObligation d r` — the rate-typed obligation framework admitting any rate function (1/n, 1/n², geometric c^n, ...). |
| **`lean/InfraFormalization/SubdivisionPath.lean`** | The canonical edge-subdivision rule's n-step trajectory `pathEdges (subdVerts n)` (Route D) — defined entirely in Lean, traceable to the hypergraph substrate. Path-shape preservation theorem `subdivisionTrajectory_isPathOf` proves the n-th state is structurally a path of length 2^n with all vertices `Nodup`. |
| **`subdivisionDiscrepancy_satisfies_obligation`** in `WassersteinRate.lean` | `subdivisionDiscrepancy n := 1/2^n` discharges `WassersteinRateObligation` with explicit `O(2^{-n})` decay. **First end-to-end machine-checked rule-trajectory → continuum-target convergence certificate.** |
| **`minkowski4_from_hypergraph_strong`** in `HypergraphMetricBridges.lean` | Concrete discharge of the Minkowski origin obligation via the subdivision-rule trajectory. |

Concretely: when PHAJEK asks "what does it mean to *prove* something
here": we have a rule (the edge-subdivision rule), evolved in Lean
(via `singleWayStep` against the bridged abstract `Step`/`MultiStep`),
with a measure-theoretic convergence proof on its trajectory
(`subdivisionDiscrepancyBundle`), that discharges a *named* origin
obligation for a *named* target metric (Minkowski). It is not
"watch this animation"; it is a closed Prop with an axiom-clean
witness term. The user can `#print axioms` and verify the soundness
chain reduces to `propext / Classical.choice / Quot.sound` only.

---

## "How can we know we got to GR" — formalised completion criterion

This addresses PHAJEK's deeper question of how Lean can *tell us* when
we have actually succeeded.

| File | What it gives |
|---|---|
| **`lean/InfraFormalization/Milestone.lean`** | Concrete Lean signatures for the program-completion theorems. `Milestone.GR_emerges_from_hypergraph (target : MetricData n) : Prop` is a closed six-conjunct existential: ∃ rule + trajectory s.t. (1) measure-rate, (2) GH-distance convergence, (3) connection convergence, (4) Riemann-tensor convergence, (5) EFE preserved in the limit, (6) discrete stress-energy emerges from rule data. Specialisations `_minkowski` / `_schwarzschild` / `_flrw` / `_some_hypergraph` (existential disjunction). Plus `QM_emerges_from_hypergraph` (branchial Hilbert + unitary + Born) and `BBH_emerges_from_hypergraph` (Phase D / K7-paper headline). |
| `Milestone.lean` docstring | **Three Lean-verifiable signals of milestone completion**: (a) compiles with no `sorry` and no `True` / `False` / vacuous-existential escape hatches; (b) `#print axioms <theorem_name>` shows ONLY `propext`, `Classical.choice`, `Quot.sound` — no project-introduced axioms (verified by `AxiomCheck.lean`); (c) the existential is term-witnessed by a specific rule the user could run. **All three checks are automated; no human judgment required to certify the result.** |
| **`INFRAGEOMETRY.md` §5f** | The 25-step constructive route from elementary connectedness through Bachmann motions / Lie theory to the Riemann tensor, GR, QM, and BBH-from-hypergraph as the endgame. Each step is one Lean def on top of the previous. |

So when the milestone Lean theorem compiles AND the axiom check
passes, **we have actually got there in the formal-proof sense**. Not
"we believe", but "the proof object exists and is sound, anyone can
verify it offline". That is the structural contrast with JGORARD's
animations.

---

## What work still needs doing (realistic picture)

Currently discharged for `MILESTONE-GR_minkowski` (the closest of the
named-metric milestones):

- ✅ Layer 1 (W₁ measure rate) — Minkowski via `subdivisionDiscrepancyBundle`.
- ✅ Layer 6 (curvature scalar) — AT9 Bishop-Gromov from `log V(r)` + SPHERE4 sphere-side cross-check.
- ✅ Pre-metric topology (TOP1 b₁, TOP4 connectedness, OPEN1/NBHD1, SPHERE1 infra-sphere/disk, INOUT1 cut-vertex/bridge/Jordan, AT8 GeodesicallyUnique, CONTRACT1 substrate).
- ✅ Bachmann motion-group substrate (HYPER2/3 perpendicular bisector + Voronoi, MIDPT1).
- ✅ Phase B screener pipeline (Forman-Ricci + chord-ratio angular, both feeding `ConvergenceRateObligation`).
- ✅ Angle tower foundations (AT0 chord-ratio, AT1 law-of-cosines, AT6 orthogonality predicate, AT9 scalar curvature).

Open layer-tasks gating MILESTONE-GR_minkowski:

- 📋 Layer 2 — pointed-Gromov-Hausdorff convergence (#222 our own pointed-GH; #213 Lorentzian-GH).
- 📋 Layer 3 — discrete connection → Levi-Civita (C8, #41).
- 📋 Layer 4 — Riemann tensor convergence (R4 #179 in flight; #218 per-metric; AT22 Cartan structure equations).
- 📋 Layer 5 — EFE preservation in the limit (per-metric: B4 #23 Schwarzschild, F4 #63, F6 #65 Kerr).
- 📋 Layer 6 — discrete stress-energy emergence (#223).

For the BBH (Phase D) endgame: H6 / H7 / H8 / H9 — initial data,
evolution, Ψ₄ extraction, full convergence to merger spacetime. The
actual numerical-GR variable is **Regge deficit angle** (AT20 #307);
identified, not yet implemented. The K7-paper headline theorem signature
is in `Milestone.lean` already.

---

## Recommended reading order for a GR postdoc

If she wants to *seriously read* the corpus and assess whether the
criticism is grounded:

1. **`MAJOR_FLAWS.md`** end-to-end (~30 minute read) — gives her the structural map of the eight flaws + which papers each appears in.
2. **`FINDINGS.md`** — claim-by-claim severity table for any specific equation she wants to look up.
3. **`results/phase2_continuum/eq342_verdict.md`** and **`eq344_verdict.md`** — for the two arithmetic errors that look "innocent" but show the corpus does not track its own cited sources.
4. **`Refutations/F6Circularity.lean`** — for the circularity (the manifold is the *input* to the "derivation"; the procedure is then `manifold → sprinkled-points → bin → reconstruct manifold`).
5. **`Refutations/F7NamedRuleStructure.lean`** + **`RuleDimensionBounds.lean`** — for the structural 1-dimensionality of the named rule (which makes the entire 4D-GR-continuum-limit narrative impossible regardless of arithmetic corrections elsewhere).
6. The internal-memory finding — the same load-bearing arithmetic errors are repeated *verbatim* across G1, G2, G3, G4. The corpus does not self-correct over time.

She does not need to take anyone's word. The Lean refutations and the
empirical causal-dim-1 measurements are reproducible and offline-
verifiable.

---

## Audit-clean signal

Project-wide:

- ~3530 Lean build jobs, all green.
- Every refutation theorem `#print axioms`-clean (`propext`,
  `Classical.choice`, `Quot.sound`).
- No `sorry` anywhere in the refutation track.
- The `subdivisionDiscrepancy_satisfies_obligation` chain
  (rule → trajectory → discrepancy → rate) is `#print axioms`-clean
  too — i.e., the *positive* assertions are at the same standard as
  the refutations.

This standard applies symmetrically: when *we* claim something
positive (e.g., the eventual `MILESTONE-GR_minkowski` discharge), it
will be subject to the same machine check.
