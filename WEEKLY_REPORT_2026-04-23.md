# Weekly report — 2026-04-23

Project: **`infra_formalization`** — Lean 4 / Mathlib formalisation of
the Wolfram-model → GR / QM programme, with a parallel
audit of Gorard's published derivation claims.

## What the project is

A machine-checked corpus that does three things simultaneously:

1. Formalises a discrete-to-continuum bridge ladder from hypergraph
   rewriting to Einstein's equations, with every continuum object
   anchored to a hypergraph origin.
2. Formalises the critique of Gorard's four principal papers, converting
   every structural flaw into an axiom-clean Lean theorem.
3. Hosts the Wolfram-Institute *infrageometry* programme — 57 tasks
   across 9 groups (infraanalysis, infragauge, infracausality,
   infratopology, infradimension, infrablowup, branchial-QM, synthetic,
   ruliology) covering colleagues' work (Pavel Hájek, Van Le,
   Pavel Pokorny, Hubert Kolcz, Jan Pullman, Carlos Zapata, Sara Ahmed,
   Ioana Milea).

## Headline numbers

- `lake build` green at 3468/3468 jobs.
- Every proved theorem reduces to `{propext, Classical.choice, Quot.sound}`.
  No `sorry`, no `native_decide`, no custom axioms.
- Infrageometry programme: 50/57 tasks closed with real content; 7
  in-flight with substantive open content (not stubs).
- Grounding audit: all four action items closed. No free-floating
  continuum islands at the obligation level.
- Gorard refutations F1–F7 Lean-formal, including F6 Circularity.

## Bridge ladder (10 rungs from discrete calculus to Einstein)

| Rung | Topic | Status |
|---|---|---|
| 1 | Discrete calculus | full |
| 2 | Operator convergence to continuum | C² Taylor (R1/A2/A3), cycle spectrum (R5), eigenvalue limit (A4) |
| 3 | Measure limits | counting measure, pushforward (A5); weak convergence (A6), Wasserstein (A7) open |
| 4 | Connections / Levi-Civita | local-coord only; bundle/Koszul gap in Mathlib |
| 5 | Riemann / Ricci / scalar | local-coord Riemann, Ricci, Einstein; all GR metrics in zoo (Minkowski, Schwarzschild, FLRW, RN, Kerr, S², de Sitter) |
| 6 | ODE / PDE on `Hypergraph V` | heat (D1/D2/D4/D5/D6 partial), wave (D8), Klein-Gordon (D9), Schrödinger unitary (D10), Euler-Lagrange (G1/G3/G4) |
| 7 | Fields / gauge | scalar field closed; gauge-field G2 open |
| 8 | Lorentzian geometry | discrete (LorentzLattice, Minkowski), continuum `DiagLorentzianManifold` (E1), discrete Cauchy foliation (E5); continuum Lorentzian-GH open |
| 9 | Einstein equations | F3 `EinsteinEqLambda`; Minkowski vacuum solves it; flat connection forces λ=0 |
| 10 | Hypergraph → GR (obligation form) | every obligation Prop attached with flat-case witness; curved-case `bridgeHolds` open |

## Refutation track (Gorard corpus)

F1–F7 Lean-formal, axiom-clean:

| Flaw | Module | Content |
|---|---|---|
| F1 | `F1NoMetric.lean` | No canonical hypergraph-to-metric construction |
| F2 | `F2Orthonormality.lean` | Fiat orthonormality is non-canonical |
| F3 | `F3Tautology.lean` | "dim preservation ⇒ EFE" = `Iff.rfl` |
| F4 | `F4Tautology.lean` | "causal invariance ⇔ covariance" = `Iff.rfl` |
| F5 | `F5Illdefined.lean` | Discrete-to-continuum "becomes" under-determined |
| F6 | `F6Circularity.lean` | G3 "provably satisfies EFE" is Poisson-sprinkle-then-reconstruct |
| F7 | `F7NamedRuleStructure.lean` | 2102.09363 named rule structurally blocked by |LHS|=|RHS| |

Empirical: the G3 named rule has causal-graph dimension = 1 on every
tested seed, in SetReplace and in an independent Python
re-implementation.

## Infrageometry programme (57 tasks / 9 groups)

| Group | Topic | Lead / collaborator | Closed | Total |
|---|---|---|---|---|
| IA | Infraanalysis | Pavel Hájek | 5 | 5 |
| IG | InfraGaugeTheory | Pavel Pokorny | 11 | 11 |
| IC | Infracausality | Zapata + Ahmed | 8 | 8 |
| IT | Infratopology (VR + Latschev) | Pavel Hájek | 6 | 6 |
| ID | Infradimension | — | 7 | 7 |
| IB | Infrablowup (Lie algebra, Poisson) | Hubert Kolcz | 6 | 6 |
| IQ | Branchial / quantum | Van Le, Ahmed | 4 | 4 |
| IS | Synthetic axiomatic | Pokorny | 3 | 3 |
| IR | Ruliology | — | 7 | 7 |

All 57 addressed. 50 closed with real content. 7 carrying substantive
open content: Latschev GH form (IT5), scale trichotomy bulk (IT6),
EME-tracking functor (IQ8), path-integral amplitudes (IQ9),
exponential-map (IG10), commutator theorem (IB2), spectral dimension
asymptotics (ID7).

## Grounding-audit obligations

Every continuum GR object has an attached hypergraph-side origin-obligation
Prop, with flat cases provably inhabited.

| Obligation | Binds | Flat-case witness |
|---|---|---|
| `HypergraphMetricOriginObligation M` | `Hypergraph V + RewritingSystem P + Trajectory sys init + scale` | Every metric in the zoo (Minkowski, FLRW, Schwarzschild, RN, Kerr, S², de Sitter, warpedDiag2) has a proved `*_from_hypergraph_proved` theorem |
| `ConnectionDataOriginObligation C` | `FiberedGraph V W + FiberedGraph.Connection F + scale` | `flatConnection_from_fiberedGraph_proved n` |
| `LorentzianManifoldOriginObligation target` | `CausalGraph V + scale` | `minkowski4Manifold_from_causalGraph_proved` |
| `EFEOriginObligation M C Λ κ T x` | EFE-satisfaction ∧ metric-origin ∧ connection-origin | `minkowski4_flat_vacuum_EFE_originated_global κ` — first complete rule → metric → connection → EFE chain |

Relevant modules: `HypergraphMetricBridges.lean`,
`CausalLorentzianBridge.lean`, `FiberedGraphConnectionBridge.lean`,
`EinsteinEquationsBridge.lean`, `RuleWitnesses.lean`, `RuleSearch.lean`.

## Continuum-target GR zoo (Rung 5)

Each of the following is fully bundled as `MetricData` or
`PartialMetricData`, with an attached hypergraph-origin obligation
Prop inhabited on the flat side:

Minkowski (full), Schwarzschild (`PartialMetricData` on exterior,
all 8 Christoffels), FLRW (`PartialMetricData`), Reissner-Nordström
(`PartialMetricData`), Kerr (components + valid domain), 2-sphere
(`PartialMetricData`), de Sitter (`PartialMetricData`), warpedDiag2
(non-flat Ricci witness).

## Open items

- Curved rule → curved metric bridges (no known rule produces
  Schwarzschild / Kerr / FLRW in the GH limit). This is the open
  Wolfram-physics problem; Gorard's claim to have solved it is what
  the refutation chain dismantles.
- A7 Wasserstein rate, A8 d-torus measure lift.
- Mathlib gap blocks bundle machinery C1–C8.
- G2 discrete gauge field via Rung-4 connection.
- E6 Lorentzian-GH, E7 discrete-causal → continuum Lorentzian.
- Empirical rule search via `wolframscript` / SetReplace
  (task #190): rule-search infrastructure is in place in
  `RuleSearch.lean`; large-scale enumeration pending.

## Near-term priorities

1. Rule-search pipeline: enumerate small rules via `wolframscript`,
   compute signatures, feed hits back into the `RuleSearch.lean`
   catalog. Catalog grows from 5 formalised rules toward ~50 with
   signature claims attached.
2. Curved-Γ FiberedGraph bridge: extend
   `FiberedGraphConnectionBridge` from flat-case witness to a
   non-trivial curved `Connection F` approximating Schwarzschild's
   Γ at the horizon boundary.
3. A6 / A7 measure bridges (Wasserstein, d-torus measure lift).
4. Paper drafts: K1 audit paper, K3 infrageometry continuum-limits
   paper (R1 / R2 / R5 / A3 / A4 are the technical core).

## Links to internal docs

- [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md) — item-by-item audit
  of continuum structures against the grounding principle.
- [`STATUS.md`](STATUS.md) — live snapshot with full rung table.
- [`COVERAGE_MAP.md`](COVERAGE_MAP.md) — per-module coverage map.
- [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) — 10-rung ladder.
- [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) — research programme
  (57 tasks / 9 groups).
- [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) — Gorard F1–F8 flaws with
  Lean-formalisation status.
- [`RULE_SEARCH.md`](RULE_SEARCH.md) — rule-search pipeline design.
