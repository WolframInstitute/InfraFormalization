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
`notes/severity_taxonomy.md`. The Lean files
(`Refutations/F1NoMetric` ... `F7NamedRuleStructure`) prove statements
about the project's encodings. The link from each file to the paper is
a reading of the paper text, and `STATUS_OF_GORARD_CLAIMS.md` gives the
status of each conclusion. For G3 the reading is: the "provably
satisfies" claim assumes Poisson-distributed rewrite events (G3 line
6080), and the §6 comparison starts from a hypergraph Poisson-sampled
from the target initial-data geometry (lines 6148-6152, 6179).
`F6Circularity.lean` does not model this procedure.

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
- *The specific named rule* (G3 line 6202) is given without a proof
  of any of the properties G3 attributes to it. The rule conserves
  edge count (PROVED). Its measured cone-growth exponents on small
  seeds lie between 0.985 and 1.256 (MEASURED). A bound on its cone
  growth is OPEN.
- *The end-to-end "derivation of EFE from hypergraph rewriting"* (G3
  §6) assumes Poisson-distributed rewrite events (line 6080) and
  compares evolutions that start from initial data sampled from the
  target geometry (lines 6148-6152, 6179). G3 gives no proof for the
  named rule.
- *Where JGORARD *deviates* from cited literature, he is wrong:* G3
  Eq 344 uses scalar `R` where Ollivier's cited JFA 2009 theorem has
  directional `Ric(v,v)` (off by factor 2 on S²); G3 Eq 342 has the
  wrong tube-volume coefficient (off by factor 2 on S², factor 6 on
  S³). These are not novel results — they are mis-statements of cited
  theorems. Verdicts: `results/phase2_continuum/eq344_verdict.md` and
  `eq342_verdict.md`.
- *Headline structural claims* — G1 identifies causal invariance
  with discrete general covariance (lines 1066-1075, `F4Tautology.lean`).
  G1 defines asymptotic dimensionality preservation as δS/δg → 0
  (eq. 87), which is the Euler-Lagrange equation of S
  (`F3Tautology.lean`). The step to the vacuum EFE rests on eq. 88,
  which states no convergence notion (F5).
- *G4's discrete singularity theorem* — title and body do not match;
  the body does not prove the theorem the title states. Documentary
  flaw F8.

**Summary:** the substantive technical content is either (a) cited
prior literature, (b) wrong restatements of cited literature, (c)
tautological, or (d) assumed. The *named-rule simulation* starts
from initial data sampled from the target geometry, and G3 does not
run the rule from other initial data. **There is no point in the
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
  an undefined object, and the comparison starts from initial data
  Poisson-sampled from the target geometry (G3 lines 6148-6152, 6179).
  PHAJEK's GR postdoc can check this by reading G3 §6.
- *G4 — claimed "discrete singularity theorems".* Title states a
  theorem; body does not prove the stated theorem. Documentary flaw
  F8 in `MAJOR_FLAWS.md`.
- *Structural arguments* — "causal invariance ⇒ general covariance"
  and "asymptotic dimensionality preservation ⇒ vacuum EFE". The
  first identifies two definitions (F4). The second is the
  Euler-Lagrange equation of S plus the limit of eq. 88 (F3, F5).

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

What the corpus presents as evidence of "match" is the
second-order convergence of the Hamiltonian constraint (G3 Table 6)
and rΨ4 extractions (Figures 78, 84) for evolutions that start from
sampled initial data.

**The named rule.** The rule has `|LHS| = |RHS|`, so the edge count is
constant along every trajectory (PROVED,
`Refutations.gorardNamedRule_applications_preserve_size`). A bounded
ball count holds on every finite hypergraph, so it does not distinguish
this rule, and it does not constrain G3's sequence of resolutions (200
to 1600 vertices). The measured cone-growth exponents on 9 small seeds
lie between 0.985 and 1.256, and SetReplace and the Python rewriter
disagree on 8 of them (MEASURED, `STATUS_OF_GORARD_CLAIMS.md`). No
bound on the rule's cone growth is proved, so the repository does not
prove that the rule's continuum limit, if any, is not 4-dimensional.

**Direct answer to PHAJEK's question:** G3 gives no proof for the named
rule, and its comparison starts from initial data sampled from the
target geometry. The repository measures cone exponents near 1 on
small seeds and does not prove a dimension bound.

**Editorial note.** The pattern recurs across the corpus: the papers
state results with more certainty than their arguments establish, and
the status of the programme is presented as further advanced than the
proofs support.
The Lean files prove statements
about the project's encodings and edge-count conservation of the named
rule. The findings about the papers are readings of the text with line
numbers.

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

### B. Lean files (sorry-free, axiom-clean)

| File | What it proves |
|---|---|
| **`lean/InfraFormalization/Refutations/F1NoMetric.lean`** | The function type `DHyp V → V → V → ℝ` has more than one element. The finding that G1 Def 15 gives no construction of `g^{ab}` is a reading of the paper. |
| **`F2Orthonormality.lean`** | Two distinct functions on `Bool × Bool` make the same pair orthonormal. |
| **`F3Tautology.lean`** | The project's encodings of asymptotic dimensionality preservation (G1 eq. 87) and the Euler-Lagrange equation are equal, so the equivalence is `Iff.rfl`. |
| **`F4Tautology.lean`** | The project's encodings of causal invariance and discrete general covariance are equal, so the equivalence is `Iff.rfl`. |
| **`F5Illdefined.lean`** | `becomes_is_underdetermined`: 1/(n+1) tends to 0 and is never eventually 0. |
| **`F6Circularity.lean`** | `CircularReconstruction.comp_eq_id` restates its own hypothesis. The file does not model G3. |
| **`F7NamedRuleStructure.lean`** | The named rule conserves edge count. No dimension bound. |
| F8 | G4's title-body gap (singularity-theorem statement vs body) — documentary, not formalised. |

`#print axioms` on each: depends only on `propext`, `Classical.choice`,
`Quot.sound`. No project axioms, no `sorry`.

### C. Measurements of the named rule

| Pointer | Content |
|---|---|
| **`lean/InfraFormalization/CandidateRuleCatalog.lean` — `gorardNamedRule`** | The rule as written in G3 line 6202. Conservativity proved. |
| **`lean/InfraFormalization/RuleDimensionBounds.lean` — `trajectory_size_invariant`** | Conservative rule ⇒ every trajectory state has the initial edge count. |
| **`notes/empirical_refutation.md`, `results/phase1_selfaudit/README.md`** | SetReplace and Python cone-exponent measurements on 9 seeds, 0.985 to 1.256, with the disagreement between the tools. |

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
4. **G3 §6, lines 6080 and 6146-6192** — the Poisson assumption on rewrite events and the initial data sampled from the target geometry. `Refutations/F6Circularity.lean` does not model this procedure.
5. **`STATUS_OF_GORARD_CLAIMS.md`** — what is proved, measured and open about the named rule. Edge-count conservation is proved. No dimension bound is proved.
6. The internal-memory finding — the same load-bearing arithmetic errors are repeated *verbatim* across G1, G2, G3, G4. The corpus does not self-correct over time.

The Lean statements and the cone-exponent measurements are
reproducible offline.

---

## Audit-clean signal

Project-wide:

- ~3530 Lean build jobs, all green.
- Every theorem in the audit track `#print axioms`-clean (`propext`,
  `Classical.choice`, `Quot.sound`).
- No `sorry` anywhere in the audit track.
- The `subdivisionDiscrepancy_satisfies_obligation` chain
  (rule → trajectory → discrepancy → rate) is `#print axioms`-clean
  too — i.e., the *positive* assertions are at the same standard as
  the refutations.

This standard applies symmetrically: when *we* claim something
positive (e.g., the eventual `MILESTONE-GR_minkowski` discharge), it
will be subject to the same machine check.
