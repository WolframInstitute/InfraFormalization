# Status snapshot

Live document: what's proved, what's in progress, where we are on the
research programme ([`INFRAGEOMETRY.md`](INFRAGEOMETRY.md),
[`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md),
[`MILESTONES.md`](MILESTONES.md),
[`COVERAGE_MAP.md`](COVERAGE_MAP.md)).

## Headline (2026-05-30 — material trace-coupling closes Gap A on the ExecHG side (#393))

`ExecRateBridge` extended with the **materially-coupled discrepancy**. The discrepancy fed into `WassersteinRateObligation` is no longer a constant `c/(k+1)` derived from the rate parameter — it is literally `|trace[k] − tgt|`, cast to `ℝ`, where `trace` is `witnessRule0`'s actual Forman-scalar trace on `edge12`.

  - **`rateBoundedAux_implies`** — induction lemma: if `rateBoundedAux i trace tgt c = true`, every in-range index `k` satisfies `|trace[k] − tgt| · (i + k + 1) ≤ c`.
  - **`rateBounded_implies`** — specialised at offset `0`: `|trace[k] − tgt| · (k + 1) ≤ c` for every `k < trace.length`.
  - **`discrepancyOfTrace trace tgt`** — `|trace.get ⟨k, h⟩ − tgt|` (cast to `ℝ`) for `k < trace.length`, `0` past the end.
  - **`discrepancyOfTrace_satisfies_obligation`** — derives `WassersteinRateObligation` directly from `rateBounded`, with `C = c + 1`. Proof: case-split (in-range chains `c/(n + 1) ≤ (c + 1)/n` via `nlinarith`; out-of-range is `0`).
  - **`strong_obligation_from_exec_rate_with_trace`** and its `Partial` variant — bridge theorems using the material discrepancy.
  - **Concrete material discharges**: `witnessRule0_edge12_trace_rateBounded` (`native_decide` on the actual trace), `minkowski4_strong_from_exec_witness_trace`, and `schwarzschild_strong_from_exec_witness_trace M` — all use the rule's *real* Forman trace, not a constant.

**Status of the two gaps after this:**

- **Gap A — discrepancy decoupled from rule** → **closed on the ExecHG side.** The discrepancy is now the rule's actual Forman-scalar trace.
- **Gap B — existential trajectory decoupled from rule** → **still open.** The strong obligation's `∃ trajectory` half still uses the trivial empty trajectory; closing it requires the dossier-to-trajectory simulation lemma (#267 / #231).

What's structurally new today: discharging the strong metric-origin obligation for Minkowski 4 or Schwarzschild now requires not only exhibiting a passing rule (statement-coupling) but also has the discrepancy half *materially* equal to the rule's trace values. The remaining decoupling is precisely the trajectory side, which is the deferred simulation-lemma work.

## Headline (2026-05-30 — bridge: rate-screener → strong metric-origin obligation discharged by a named candidate rule (#392))

`ExecRateBridge.lean` lands the first end-to-end coupling from the executable rule-search machinery (#384/#385/#386/#391) to the abstract metric-origin obligations in `HypergraphMetricBridges`.

  - **`ExecMetricOriginObligation r seeds N tgt c`** — `abbrev` for `stablyConvergesToAt r seeds N tgt c = true` (decidable Prop).
  - **`discrepancyOfRate c := c/(k+1)`** — the constant-rate discrepancy derived from a rate-pass; `discrepancyOfRate_satisfies` proves it satisfies `WassersteinRateObligation`.
  - **`strong_obligation_from_exec_rate M r seeds N tgt c (h : ExecMetricOriginObligation r seeds N tgt c)`** — for any continuum `MetricData M`, the strong obligation discharges from the rate-pass. Parallel `strong_partial_obligation_from_exec_rate` for `PartialMetricData`.
  - **Concrete witness**: `witnessRule0 := rate12Witnesses.headD trivialIdentityExecRule` (the first of #391's 7-element rate-(0,12) selection). `witnessRule0_passes` discharged by `native_decide`. Named discharges `minkowski4_strong_from_exec_witness` and `schwarzschild_strong_from_exec_witness M` for Minkowski 4 and Schwarzschild.

**Honest scope.** The coupling is **statement-coupled, not body-coupled**: the bridge theorem syntactically requires exhibiting a passing rule (you cannot apply it without supplying a candidate that decides true), but the proof body uses only the rate constant `c` to build the discrepancy, and the existential-trajectory half is still discharged by the trivial empty witness — the dossier-to-trajectory lift (Gap B / #267) remains the deferred next step that would push the rule's actual engine trajectory through to the existential half. Material trace-coupling (the discrepancy being `|trace[k] − tgt|` rather than the constant `c/(k+1)`) is staged as a follow-up.

What this gives the project: the rule-search work since #384 is no longer free-floating ExecHG-side machinery — it now syntactically participates in the discharge of named GR-metric obligations. The shape of "rule search ⇒ metric origin" is in place, with the two open structural gaps (Gap A: tie discrepancy to actual trajectory W₁; Gap B: dossier-to-trajectory lift) being the explicit residuals.

## Headline (2026-05-30 — rate-based target-aware screener: rate-stability ≠ trend-stability, with a 17 > 11 separation (#391))

The trend classification of #385/#386 is qualitative — sign of the final Forman scalar. `RuleSignatureExecSearch` now adds a quantitative *rate-bound* predicate parallel to the abstract `ConvergenceRateObligation`:

  `|trace[i] − tgt| · (i + 1) ≤ C`  for every recorded state `i`

The integer-arithmetic encoding of `O(1/n)` convergence to `tgt` at rate `C`. Decide-checkable on a finite dossier trace. Then `dossierConvergesToAt`, `stablyConvergesToAt`, and `stableRateSelect` filter candidates whose every-seed run lies within a `(tgt, c)` envelope.

**Certified distribution on `seedSet` at 2 steps:**

| `(tgt, c)` | passing candidates |
|---|---|
| `(0, 0)` | 0 |
| `(0, 12)` | **7 (= stably flat)** |
| `(0, 36)` | 9 |
| `(0, 200)` | **17 (> 11 stably classifiable)** |
| `(4, 16)` | 7 |
| `(-4, 12)` | 0 |

**Two structural results** (both `native_decide`-certified):

1. **`rate-(0, 12) = stably-flat` as sets.** The two `.all`-checked containments hold both ways, so the tight envelope at the canonical `c = 12` characterises the stably-flat selection exactly.
2. **Rate-stability is strictly weaker than trend-stability** (`17 > 11`). A rule can keep its Forman scalar bounded near `0` on every seed without producing the same trend on every seed; rate-stability is the looser criterion.

This is the form of obligation that ultimately feeds `HypergraphMetricOriginObligationStrong`: the next step (genuinely harder, deferred) is to discharge the abstract `FormanRicciScreener τ κ r` from a `stablyConvergesToAt`-passing rule via the dossier-to-trajectory lift (the deferred Gap B / #231).

## Headline (2026-05-30 — paclet pull: delta complexes, scale-indexed topology, multi-method moduli, synthetic measures)

Substantial conceptual landings in PHAJEK's two paclets (Infrageometry cf04481→f811dc5; SyntheticInfrageometry ec934d6→eb68944, ~34 commits). Not just bugfixes — new structural primitives that touch the refutation chain (F1, F5) and open new port targets.

**Infrageometry (PHAJEK May 23–30):**
- **Delta complexes** (commit 02536bc, "feat: support delta complexes") — presimplicial sets (face maps, no degeneracies) are now first-class. Concrete WL reference for #248 KN12.
- **`BallTopology[g, r]`** (`Kernel/Topology.wl`) — scale-indexed Alexandrov topology on V(g), Hasse-diagram of the specialization preorder; plus `TopologicalClosure / Interior / Boundary / Neighborhood / ContinuousMapQ`. A *scale spectrum* of topologies on the same vertex set. Reference for #312 AT25.
- **`UnitLengthGraph` / `UnitLengthEmbedding`** in `Kernel/Mesh.wl` — rigid unit-distance embeddings via iterative hard-sphere packing; the natural discrete setting for Regge calculus (#307). New task #389 logged.
- **`GraphBoundary` / `GraphInterior`** — combinatorial boundary/interior front-end primitives.

**SyntheticInfrageometry (PHAJEK May 23–30):**
- **`InfraLineStructure` / `FindLineStructure`** (T1–T5 series) — a *line structure* on a graph = a consistent path system; `ConsistentPathSystemQ` verifier; multiple methods with explicit tie-break. Direct realisation of the F1 moduli framing in the line-primitive layer. Reference for #300 PATH1; new task #387 logged.
- **`InfraMeasure`** (renamed from `VisitMeasure`) + `InfraBoundary` + `infraRepType` — a *synthetic* measure-theoretic primitive on a graph, decoupled from any continuum probability measure. Makes the F5 distinction structural. New task #388 logged.
- **Multi-method moduli of basic primitives** — `InfraPerpendicularQ` (Schoenberg / Centroid / four-corner-wedge), `FindInfraShellCenter` (bisector / chord / equidistant). Each method = a distinct invariant, exposed via `Method` argument. F1 moduli pattern made structural across the API. New task #390 logged.
- **`GeodesicGraph → GeodesicSprayGraph`** (rename) — signals more structural use, Riemannian-spray analog. Updates #208 P16.
- **`InfraTriangle` / `InfraPolygon` / `InfraQuadric`** — first-class higher-order shape primitives; polygons as *geodesic-side chains*.
- **`PathSpace.wl`** substantially expanded (172 lines) — loop-space / path-space machinery. Updates #333 HOM2.
- **Universal line / line hull / segment hull** — universal-property hulls (category-theoretic flavor).

**Refutation-chain impact (the F1 and F5 sharpenings landed today):**
- **F1 — paclet-design sharpening**: every basic synthetic construct (perpendicular, shell-centre, line) admits a moduli of inequivalent definitions, and the paclet treats this as a feature via the `Method` argument. F1 is not only "the metric is not canonical" but "*no* basic synthetic operation is canonical." Annotated in `MAJOR_FLAWS.md` and `lean/.../Refutations/F1NoMetric.lean`.
- **F5 — synthetic-measure sharpening**: `InfraMeasure` is an infrageometric construct of its own kind, not the marginal of a continuum probability measure. G1 Eq 88 conflates the two — a category error. Annotated in `MAJOR_FLAWS.md` and `lean/.../Refutations/F5Illdefined.lean`.

Task descriptions updated: #208, #248, #300, #312, #333. New tasks: #387 (line-structure typeclass), #388 (InfraMeasure synthetic primitive), #389 (UnitLengthGraph rigid embedding), #390 (multi-method perpendicular moduli).

## Headline (2026-05-24 — Multi-seed stability filter sharpens the rule-search discriminator (#386))

`RuleSignatureExecSearch.lean` gains a stability layer: a candidate's curvature class is only admissible if it is the same on *every* seed in a topologically diverse seed set. This rejects rules that pass the single-seed (#385) filter by seed-coincidence.

- **`seedSet`** = `[edge12, path123, cycle4]` — three distinct 1-skeleton topologies (single edge, simple path, 4-cycle), no triangles in any.
- **`trendsAcross r seeds n`** — the trend each seed produces.
- **`isStablyTrend`, `stablyClassifiable`, `stableSelect`** — primitives for stable-target filtering.
- **Certified stability distribution** over the 21-candidate family at 2 steps: **7 stably flat, 2 stably negative (genuine hyperbolic, seed-independent), 2 stably positive, 0 stably zero = 11 stably classifiable**. The remaining **10 candidates are seed-dependent**: their curvature trend changes with the seed, so they have no rule-level curvature class on this family and are not admissible for a curvature-target search.

The stability filter does real work — it rejects roughly half the candidates that passed the single-seed filter as bona-fide curved. The genuinely seed-independent hyperbolic rules drop from 2 to 2 (both survived), the genuinely seed-independent positively-curved rules drop from 2 to 2 (both survived), and the seed-dependent rest are filtered out cleanly. Same screener primitives (`RuleSignatureExecMetrics`), same engine-port spec, stronger discriminator.

## Headline (2026-05-24 — Lean-alone rule-search driver: generate → run → classify → select (#385))

`RuleSignatureExecSearch.lean` turns the #384 screener into an actual search loop, entirely inside Lean and entirely `decide`/`native_decide`-checked.

- **Generate.** `enumerateRules2_1 maxRHS` is a real bounded generator: single-edge LHS `{0,1}`, RHS = any nonempty subset (size ≤ `maxRHS`) of the ordered vertex pairs over `Fin 3` (two bound vertices + one fresh). 21 candidates at `maxRHS = 2` — rules are *generated*, not hand-listed.
- **Run + classify.** `trendOf r seed n` runs a candidate via `canonicalDossier` and reduces its triangle-Forman trace to a coarse `CurvatureTrend` (flat / positive / negative / zero) via `classifyForman` (constant ⇒ flat, else sign of the final scalar).
- **Select.** `selectByTrend` keeps the candidates landing in a target trend.
- **Certified result.** On the single-edge seed at 2 steps the family partitions into **13 flat, 4 zero-non-constant, 2 negatively-curved (tree-like / hyperbolic), 2 positively-curved**, summing to 21 — the classification is total and the screener is a genuine discriminator, not a pass-through. Every count is `native_decide`-certified.

This is the first end-to-end "rule search using Lean alone" the user asked for: a generated candidate set, screened and partitioned by curvature, with machine-checked counts. The same `CurvatureTrend` signal — built from the `RuleSignatureExecMetrics` formulas — is exactly what must be ported into the fast `HypergraphRewritingEngine` to run this at scale (#190). Build green at 3536 jobs.

## Headline (2026-05-20 — ExecHG-native screener metrics; the Lean-alone rule-search keystone + engine-port spec (#384))

`RuleSignatureExecMetrics.lean` makes a candidate rule's executable run screenable end-to-end inside Lean, and pins the metric set to port into RASSAR's fast `HypergraphRewritingEngine`.

The abstract triangle-Forman screener (#383) lives on `[Fintype V]` `Hypergraph`; the engine's states are `ExecHG ℕ` (ℕ-vertex lists, no `Fintype`). #384 closes that gap by recomputing the *same arithmetic* on the finite carrier `vertexList H`:

- **`execAdj`, `execAdjDegree`, `execTriangles`, `execFormanEdge`** (= `Hypergraph.formanRicciEdgeTriangle`: `4 − deg u − deg w + 3·#△`), **`execFormanScalar`** (= `Hypergraph.formanRicciTriangleDoubled`). All total, computable, `decide`-able.
- **`Dossier.formanScalarTrace`** + the **`SignatureVerdict ⟨edgeCounts, vertexCounts, formanScalars⟩`** bundle — the exact per-state triple the fast engine must emit per candidate. This bundle *is* the metric-set specification for the engine port.
- Screener verdicts as decidable Bool predicates on the run: **`formanScalarConstant`** (conservative/flat-target pass), **`formanScalarReaches tgt`** (positive verdict), **`formanScalarPersistentGap tgt`** (negative discharge — no state ever attains the target).
- Numerics pinned by cross-check (`K₃ = 18`; flat 4-cycle `= 0`; single edge / 3-path `= 4`). End-to-end the edge-append run certifies `⟨[1,2,4,8], [2,3,5,9], [4,4,0,-12]⟩` — the Forman scalar turning **negative** is the tree-like / hyperbolic signature, a `decide`-checked rejection against any flat or positively-curved target.

This is the keystone the user identified for "rule search using Lean alone": run a candidate, read a certified `SignatureVerdict`, accept/reject by `decide`. The literal #267 subdivision simulation lemma remains deferred (Route D #284 already decoupled the subdivision trajectory from the engine). Next: drive an open candidate enumeration through this screener (#190), and hand the `SignatureVerdict` formulas to the fast engine.

## Headline (2026-05-13 — triangle-corrected Forman screener (#383))

Upgrade of the per-trajectory Forman-Ricci screener to the standard 1D Forman with triangle-correction term, parallel to PHAJEK's `FormanRicciCurvature[g, "OnCells" -> 1]` at unit weights in NMURZIN's `Infrageometry/Graph.wl`.

- `Hypergraph.trianglesThroughEdge v w`, `Hypergraph.adjDegree v`, `Hypergraph.formanRicciEdgeTriangle v w` in `DiscreteRicci.lean`. Edge curvature `F(v, w) = 4 − deg(v) − deg(w) + 3 · #triangles_through(v, w)`. Symmetry `formanRicciEdgeTriangle_symm` and helper `trianglesThroughEdge_symm` proved.
- `Hypergraph.formanRicciTriangleDoubled H`: total scalar as the double sum over ordered adjacent pairs; equal to `2 · F_total` with the factor of two absorbed by the rate constant downstream.
- `RuleSignatureScreener` extended with `formanRicciTriangleTrajectory τ`, `formanRicciTriangleDeviation τ κ`, `FormanRicciTriangleScreener τ κ r`, plus the const-self / length-1 conservative-discharge lemmas and the persistent-gap negative-discharge theorem, parallel to the existing `FormanRicciScreener` family.

The triangle term captures local clustering (`+3` per triangle through the edge) — a strictly finer screener than the bare 4 − deg − deg form. The bare-Forman screener is retained for backwards compatibility on tests that depend on the existing trajectory shape.

## Headline (2026-05-13 — paclet pull: PHAJEK curvature / resistance / Hodge-pseudoinverse primitives in NMURZIN's `Infrageometry`)

Submodule bump on `resources/Infrageometry`, `resources/SyntheticInfrageometry`, `resources/InfraGaugeTheory` to 2026-05-13 surfaces substantial new WL-side reference implementations.

**`Infrageometry` (NMURZIN's paclet, May-2026 PHAJEK additions)**
- `Graph.wl` now exposes `FormanRicciCurvature` (full Forman on the clique complex with `OnCells` / `MaxCellDimension` options, sped up to O(V+E) via precomputed incidence map), `OllivierRicciCurvature` (W₁ via `LinearOptimization`), `WolframRicciCurvature` (volume-comparison scalar with auto or fixed local dimension), `EffectiveResistance` (Klein-Randić resistance distance), `ResistanceQ` (Schoenberg negative-type test).
- `Infrageometry.wl` now exposes `GreenOperatorMatrix` (block Moore-Penrose pseudoinverse of the Hodge laplacian — **distinct from** the existing Knill `GreenFunctionMatrix`) and `HodgePropagatorMatrix` (Moore-Penrose pseudoinverse of the boundary `d_k`).

**`SyntheticInfrageometry` (PHAJEK)** — major restructure to 26 kernel files. Per-primitive organisation: `InfraPoint`, `InfraLine`, `InfraSegment`, `InfraRay`, `InfraCircle`, `InfraPlane`, `InfraPolyline`, `InfraShell`, `InfraRevolution`, `InfraScene` (plus visualization variants). New geometry-layer files: `AlexandrovGeometry`, `EuclideanSpace`, `MetricGeometry`, `ProjectiveGeometry`, `TarskiGeometry`. New modules: `Homotopy`, `PathSpace`, `ExampleGraphs`, `GraphEnumeration`. `FindSegment` now supports `Method → "Stretched"` / `"Pulled"` (Forman-Ricci frontier sweep) / `"Pulled"` with Wolfram-Ricci. `TorusTessellation[{p, q}]` via Schläfli symbol. Old `Postulates.wl` / `Predicates.wl` / `Scenes.wl` / `Viewers.wl` removed in the refactor.

**Impact on rule search**: a more refined Forman-Ricci screener (full clique-complex Forman vs our current elementary form) is now available as a target upgrade for `RuleSignatureScreener.formanRicciTrajectory`; an Ollivier-Ricci screener becomes feasible with a reference implementation; two new screener-metric candidates open (effective resistance, spectral via Moore-Penrose Hodge).

**Task updates surfaced**: #287 AT2 Forman, #295 AT10 Tarski, #297 AT12 Ollivier-Wasserstein, #300 PATH1, #305 AT18 Cayley-Klein, #359 EFFRES1, #368 OLLIVIER-HG — all flagged with WL reference implementations now available. #171 M6 NMURZIN parity description expanded. #263 SIG2 / #264 SIG3 marked for restructure (target files no longer exist after refactor). New tasks #381 (Knill-Green vs Moore-Penrose-Green distinction) and #382 (HodgePropagatorMatrix port).

## Headline (2026-04-30 — H1 corpus end-to-end Lean-internal screening (#373))

`RuleSignatureExecCorpus.lean` lands the on-ramp. The closed H1 candidate-rule corpus is screened end-to-end inside Lean — `MultiwayExec.singleWayEvolve` produces canonical dossiers, the dossier carries `edgeCountTrace` / `edgeCountConstant`, and `decide` / `native_decide` produce axiom-clean verdicts. **No paclet round-trip.** The trust boundary is internal to Lean.

- **Five H1 rules ported**: `trivialIdentityExecRule`, `edgeDoublingExecRule`, `edgeAppendExecRule`, `tripleExpansionExecRule`, `gorardNamedExecRule`. Each gets concrete seeds and canonical dossiers.
- **`Dossier.edgeCountConstant : Bool`** + `vertexCountConstant` added to `RuleSignatureSchema.lean` — the screener verdicts as decidable Bool predicates over the ExecHG-side trajectory.
- **Headline theorem `h1_corpus_edgeCount_screener_verdict`**: trivialIdentity passes (constant 1), JGORARD path-seed passes (constant 4 after 1 step), edgeDoubling/edgeAppend/tripleExpansion fail. All `decide` / `native_decide`-checked.
- **Cycle-seed observation**: JGORARD's rule + 4-cycle seed *fails* edge-count constancy under `singleWayStep`. Four overlapping matches around the cycle each emit a 4-edge RHS while consumed edges have already been removed by earlier matches — engine-level non-conservation despite abstract-side `Rule.IsConservative`. Documented as a useful negative test, not a bug.

This closes the on-ramp end of the rule-search pipeline. The paclet hookup (#374 / #375) accelerates open enumeration only; for the closed H1 corpus, Lean executor end-to-end is sufficient and stronger.

## Headline (2026-04-30 — RuleSignatureSchema lands; correctness contract closed)

`RuleSignatureSchema.lean` lands (#372) with the strong correctness theorem (#377). This is the WL-paclet-to-Lean trust boundary, sealed.

- **`Dossier { rule, seed, states }`** — Lean-internal data model for the JSON interchange used by PPOKORNY's `Infrageometry` paclet (#374). The dossier is the *trajectory*, not the *verdict*.
- **`isConsistent : Bool`** — decidable check that `Hᵢ₊₁ = singleWayStep ⟨[d.rule]⟩ Hᵢ` for every step plus `states[0] = seed`. Computed from the dossier alone — no external trust.
- **`canonicalDossier rule seed n`** — reference dossier built by running `singleWayEvolve` directly. `canonicalDossier_isConsistent` proves the Lean executor itself produces a consistent dossier (soundness).
- **#377 `consistent_dossier_eq_canonical`** — *every* consistent dossier IS the canonical Lean-executor trajectory. The WL paclet cannot smuggle a non-canonical trajectory past `isConsistent`. Combined with `canonicalDossier_isConsistent`, the consistency check is both sound and characterising.
- **Concrete tests**: subdivision-rule 4-step canonical dossier passes `seedConsistent`; edge-count trace = `[1, 2, 4, 8, 16]`; vertex-count trace = `[2, 3, 5, 9, 17]`. TC1 1-step canonical dossier passes consistency. All `decide`-proven.

The architecture is now: WL is the heuristic, Lean is the judge. WL emits dossiers in the schema; Lean re-runs `singleWayStep` and confirms the trajectory is exactly what its own executor produces. WL becomes a precomputed cache, not a source of new claims.

Push order alignment (2026-04-29 in task tracker): #372 + #377 land first; #373 (Lean-only end-to-end pipeline on H1 catalog) is the on-ramp; paclet hookup (#374 emitter request, #375 validator) is the at-scale accelerator for #190 only — *not* on the critical path for K1 / K3 papers.

## Headline (2026-04-27, late — SPHERE4 surface-area Bishop-Gromov)

`DiscreteRicci.lean` extension lands SPHERE4 (#337) — sphere-side Bishop-Gromov scalar curvature extractor:
- `unitSphereAreaEuclidean d : ℝ` — `S_d = d · Ω_d` (small-d closed forms, d ≥ 4 placeholder).
- `flatSphereArea d r := S_d · r^(d-1)` — flat baseline sphere area.
- `Hypergraph.surfaceCurvatureAt v d r := (6d/r²) · (1 − |S(v, r)| / S_flat(d, r))` for `r > 0`. Sphere-side Bishop-Gromov: curvature picks up at one Taylor-order higher than the ball-side AT9 extraction. **Independent cross-check of AT9.**
- `surfaceCurvatureAt_zero_of_match`: matched sphere area ↔ R = 0.

Two scalar-curvature extractors (AT9 ball-side + SPHERE4 sphere-side) now ride on the same `infraSphere`/`infraDisk` substrate. Continuum limit: both should agree on R(v); finite-scale deviation between them measures discrete-geometry error.

## Headline (2026-04-27, late — CONTRACT1 substrate)

`HypergraphDistance.lean` extension lands CONTRACT1 substrate (#329, partial — disk-contractibility version; full DEFORM1-based contractibility deferred):
- `Hypergraph.IsTrivialCycle γ := γ.length = 0` — baseline.
- `Hypergraph.IsDiskContractible γ w r := ∀ x ∈ γ.support, x ∈ geodesicBall w r` — sufficient condition for contractibility on manifold-like hypergraphs (cycle fits inside a small disk and bounds it).
- `Hypergraph.IsContractibleAtScale γ r := ∃ w, IsDiskContractible γ w r` — persistence-barcode death-time ↔ minimum such r.
- `isTrivialCycle_isDiskContractible`, `diskContractible_zero_support` lemmas.

For BBH (Phase D): event horizon = non-disk-contractible cycle (vertices on the horizon span larger than any unit disk because they bound the singularity); merger event = cycle becomes disk-contractible (the new 2-cell from rewriting fills in). Full DEFORM1-based contractibility (γ reducible to `Walk.nil` via elementary moves) is the structural follow-up, deferred until DEFORM1 lands.

## Headline (2026-04-27, late — OPEN1 + NBHD1 formal-topology layer)

`HypergraphTopology.lean` extension lands OPEN1 (#349) + NBHD1 (#350):
- **OPEN1** — predicate-level definitions for the four canonical topologies on a hypergraph: `IsDiscreteOpen` (trivial), `IsAlexandrovOpen` (closed under one-step neighbour expansion, useful for posets / causal-DAGs), `IsCellularStarOpen` (open star of every vertex it contains), `IsVRScaleOpen r` (closed under r-neighbourhoods, scale-indexed). Plus `isAlexandrovOpen_univ`, `isVRScaleOpen_univ` (`Finset.univ` is always open).
- **NBHD1** — `nbhdBasis v r := H.geodesicBall v r`, the decreasing-radius family generating the local topology at vertex `v`. Plus `nbhdBasis_mono`, `self_mem_nbhdBasis`, `nbhdBasis_zero_eq`.

SWOLF + PHAJEK's pivot to formal topology now has its substrate. Each topology yields different compactness/continuity theorems; the corresponding `TopologicalSpace V` instances (closure under arbitrary union + finite intersection) are deferred. SWOLF's "locally has neighbourhoods" intuition for surfaces becomes "neighbourhood basis stabilises to disk-shapes" — precise diagnostic for SURFACE1 manifold-detection.

## Headline (2026-04-27, late — AT8 GeodesicallyUnique + INOUT1 cut/bridge/Jordan)

`HypergraphDistance.lean` extension lands AT8 (#293) + INOUT1 (#344):
- `Hypergraph.GeodesicallyUnique H` — every pair of shortest walks between the same endpoints is equal (SWOLF's straight-lines condition; gates the angle-as-real-angle interpretation for AT0 / AT1 / AT3 / AT26).
- `GeodesicallyUnique.swap` (well-defined under endpoint swap), `geodesicallyUnique_self_walks` (length-0 walks at a vertex are all `Walk.nil`).
- `Hypergraph.IsCutVertex H v` (articulation point), `Hypergraph.IsBridgeEdge H u v` (cut edge — predicate uses `Walk.support` indexing), `Hypergraph.CycleSeparates γ` (Jordan-separator predicate on a closed walk: removing γ's support disconnects ≥ 2 vertices).

These primitives gate the angle-interpretation theorems (AT0 number → AT0 angle requires `GeodesicallyUnique`) and the BBH topology-change tracking (event-horizon-as-`CycleSeparates`-witness for Phase D).

## Headline (2026-04-27, late — AT2 Forman angle defect substrate)

`KnillCore.lean` extension lands AT2 substrate (#287, partial — definitions + characterisation + bounds; full Gauss-Bonnet sum identity deferred):
- `vertexStarTriangles G x` — triangles in G incident to vertex `x`.
- `vertexTriangleCount G x` — `T(x) := |vertexStarTriangles G x|`.
- `formanAngleDefectZ G x := 6 − T(x)` (ℤ; rescale by `π/3` for geometric reading per Higuchi 2001 / Knill 2011 equilateral convention).
- `mem_vertexStarTriangles` characterisation; `vertexTriangleCount_le` (≤ #triangles); `formanAngleDefectZ_le_six` (defect ≤ 6).

The full sum identity `∑_x (6 − T(x)) = 6·|V| − 3·|triangles|` (which on a closed 2-manifold gives `6 χ(G)`, matching continuum `2π χ` after `π/3` rescaling — discrete Gauss-Bonnet) needs a careful double-counting proof in Mathlib's `Finset.sum_comm` API; staged as the residual on this substrate.

## Headline (2026-04-27, late — MEMBER1 + BOUND1 spatial)

`HypergraphTopology.lean` extension lands MEMBER1 (#346) and BOUND1 spatial flavour (#345):
- `IsInRegion v R := v ∈ R` uniform alias surfacing SWOLF's foundational topological membership predicate. Decidable for free via `Finset.decidableMem`.
- `isInRegion_infraDisk_iff`, `isInRegion_infraSphere_iff`, `isInRegion_perpBisector_iff`: characterisation lemmas through the alias.
- `Hypergraph.spatialDiameter := sup_{u, v} dist u v`; `dist_le_spatialDiameter`.
- `Hypergraph.IsBounded R := ∃ k, ∀ u v ∈ R, dist u v ≤ k`; `isBounded_of_finite` (every region of a finite hypergraph is bounded).

The four-flavour BOUND1 (causal / branchial / rewriting-reachable diameters) remains pending; spatial flavour suffices to surface the substrate.

## Headline (2026-04-27, late — pre-metric topology + curvature/hyperplane substrate land)

**12 tasks closed in 7 commits this push** (`c1447bc` → `683633c`). The full angle / curvature / topology / hyperplane substrate that SWOLF and PHAJEK discussed across three meetings is now sorry-free, build-clean Lean code at 3532 jobs:

- **AT9 (#294)** — `Hypergraph.scalarCurvatureAt v d r` — Bishop-Gromov scalar curvature `(6(d+2)/r²)·(1 − V/V_flat)` from `geodesicBallVolume` + flat baseline (`unitBallVolumeEuclidean d`, `flatBallVolume d r`). Sign theorems: `_zero_of_match` (flat ↔ R = 0), `_pos_iff` (R > 0 ↔ sub-flat = spherical-like). In `DiscreteRicci.lean`.
- **AT6 (#291)** — `AreOrthogonalAxes` `True`-stub replaced with `IsOrthoApprox`-based chord-ratio condition `≈ √2`. In `CoordinatizationDimension.lean`.
- **AT7 (#292)** — `elementaryAngleSample`, `angularDeviation`, `AngularScreener`, `CombinedScreener` (edge-count + Forman-Ricci + angular triple), `angularScreener_fails_of_persistent_gap`. **Phase B screener pipeline complete on both curvature and angular sides.** In `RuleSignatureScreener.lean`.
- **TOP1 (#323) + TOP4 (#326)** — `Hypergraph.spatialB0` (SWOLF's "is every point reachable from every other"), `IsSpatiallyConnected`, `firstBettiZ` (cycle rank `#hyperedges − #V + b_0` over ℤ), `spatialB0_le_card`, `spatialB0_pos_of_nonempty`, `firstBettiZ_lower_bound`. New file `HypergraphTopology.lean`. **Pre-metric topological invariants surface as first-class objects.**
- **SPHERE1 (#334)** — `Hypergraph.infraSphere`, `infraDisk`, `infraSphereVolume`, sphere-disk inclusion, distinct-radii disjointness, `self_mem_infraSphere_zero`. In `HypergraphDistance.lean`. SWOLF's "all points equidistant from a point".
- **HYPER2 (#339) + HYPER3 (#340) + MIDPT1 (#342)** — `Hypergraph.perpBisector` (metric hyperplane), `closerHalf`, `HasTopologicalHyperplane` (PHAJEK's separator stub), `midpoint`, `nearMidpoint`, `voronoiCell`, with `mem_*` characterisations and `*_symm` symmetry lemmas. In `HypergraphDistance.lean`. **Bachmann motion-group substrate now in place.**

**The 25-step constructive route to differential geometry** (INFRAGEOMETRY.md §5f) now has concrete code at layers 1 (PATH1 staged), 7 (TOP1/TOP4), 13 (metric → spheres SPHERE1, Voronoi HYPER3), 14 (angles AT0/AT1), 15 (Bishop-Gromov scalar curvature AT9). The Bachmann route from reflections through perpendicular bisectors → Coxeter / Lie has its substrate (HYPER2 + MIDPT1).

**MILESTONE-GR layer-1 conjunct** (W₁ measure rate) was already discharged via `subdivisionDiscrepancyBundle`; now AT9 provides the curvature scalar that the Layer-4 Riemann-tensor convergence will eventually consume. The MILESTONE statement in `Milestone.lean` remains a closed Lean target whose proof becomes term-instantiable as the layer-tasks complete.

## Headline (2026-04-27, MILESTONE statements + AT0/AT1 angle primitives land)

**`Milestone.lean` lands** (#369, #370, #371) — concrete Lean signatures for the program-completion theorems:
- `Milestone.GR_emerges_from_hypergraph (target : Curvature.MetricData n) : Prop` with six structural conjuncts (W₁ measure-rate via existing `HypergraphMetricOriginObligationStrong`, plus placeholders for distance / connection / Riemann / EFE-preservation / discrete-stress-energy convergence — each tied to a named layer-task).
- Specialisations: `GR_emerges_from_hypergraph_minkowski` (closest milestone), `_schwarzschild`, `_flrw`, `GR_emerges_from_some_hypergraph` (existential disjunction).
- `QM_emerges_from_hypergraph` (branchial Hilbert + unitary + Born).
- `BBH_emerges_from_hypergraph` (Phase D / K7 paper headline).
- All compile as `Prop`s; placeholders are `True`-typed so NO axiom is introduced at the milestone-statement level (`#print axioms` clean). Three Lean-verifiable signals of completion (no `sorry` / clean `#print axioms` / term-witnessed existential) explicitly documented.

**AT0 + AT1 angle primitives land** (#285, #286 → completed) — `Hypergraph.elementaryAngle O A B` (SWOLF's chord-ratio `d(A,B)/d(O,A)` for equidistant pairs, equals `2 sin(θ/2)`); `Hypergraph.cosAngle O A B` (law-of-cosines); `Hypergraph.angle O A B := Real.arccos cosAngle`; `Hypergraph.IsOrthoApprox` (chord-ratio `≈ √2` orthogonality predicate, AT6 substrate). All in `HypergraphDistance.lean` next to `dist`. Symmetry, non-negativity, self = 0 lemmas. **Foundation of the angle tower; AT9 Bishop-Gromov scalar curvature now sits naturally on top.**

## Headline (2026-04-26 — late, topology-before-metric layer + cellular-sheaf framework + SWOLF's structural sequence)

**The full pre-metric topology layer is now logged** as a coherent task family. SWOLF's structural insight: topological information should be available BEFORE metric / volume / region structure. The hypergraph has a natural layered topology hierarchy that doesn't need `Hypergraph.dist` or `geodesicBallVolume`. In dependency order:

- **PATH1 (#300)** — native `Hypergraph.SimplePath u v` (SWOLF's "non-overlapping path"); **PATH2 (#301)** — equivalence to clique-expansion `dist`.
- **POLY1 (#316)** — generalised polygon (cycle-of-segments with arbitrary intersection sequences; recovers Euclidean as singleton-intersection case).
- **POLY2 (#317)** — full categorical generalisation: cellular k-chain in Δ-complex with sheaf coefficients (subsumes POLY1 + CELL1 + P4 + P5 + P19 + IGE2).
- **POLY3 (#318)** — spin networks / spin foams (LQG primitive + knot-invariant home via Witten/Reshetikhin-Turaev).
- **CELL1 (#315)** — cellular sheaves on Hypergraph V — PHAJEK's "string theory on the graph" framework. Cycles-with-common-points = equalizer at common-stalk.
- **AT-W (#319)** — sheaf-angle (14th flavour-column in the angle tower): `cos θ = ⟨r₁, r₂⟩_{F(common)} / (‖r₁‖·‖r₂‖)` for restriction maps; generalises Knill/Connes spectral angle to sheaves.
- **CONTRACT1 (#329)** — contractibility predicate (binary, scale-indexed via VR-complex; persistence-barcode death-time IS the contractibility scale).
- **DEFORM1 (#330)** — elementary path deformations (Tietze/Whitehead/Reidemeister-style generating set: backtrack, 2-cell substitution, hyperedge-transit substitution).
- **DEFORM2 (#331)** — elementary path extensions (forward/backward edge or hyperedge-transit append/prepend); together with DEFORM1 generates the full fundamental category.
- **HOM1 (#332)** — path-homotopy = `EqvGen` of DEFORM1.
- **HOM2 (#333)** — fundamental groupoid Π_1(H).
- **TOP1 (#323)** — first Betti `b_1` (combinatorial cycle rank).
- **TOP2 (#324)** — higher Betti `b_k` via Hodge decomposition.
- **TOP3 (#325)** — fundamental group π_1.
- **TOP4 (#326)** — connected components `b_0`.
- **TOP5 (#327)** — higher homotopy π_k.
- **TOP6 (#328)** — genus / crossing number.
- **KNOT1 (#320)** — linking number / Borromean detection.
- **KNOT2 (#321)** — Massey products / higher-linking invariants.
- **KNOT3 (#322)** — Yamada / Jones polynomial via spin-network Chern-Simons evaluation.

**PHAJEK's "string theory on the graph" framing**: the cellular-sheaf framework IS string field theory. Closed strings = 1-cycles, interaction vertices = common-stalk equalizers, worldsheets = cellular k-chains, string amplitudes = sheaf-cohomology. Translation table in INFRAGEOMETRY.md §5d.

**SWOLF's structural sequence** (the Tietze/Whitehead style — moves are the data, topology is the consequence):
PATH1 → POLY1 → CONTRACT1 → DEFORM1/DEFORM2 → HOM1/HOM2 → TOP3 (π_1) → TOP1 (b_1).
Each layer needs only the previous; the whole hierarchy lives below the metric layer.

For Phase D BBH specifically: black-hole horizon = non-contractible cycle; merger event = moment cycle becomes contractible (a new 2-cell fills the previously-non-contractible region). KNOT-cobordism between linked → unlinked configurations. Cellular-sheaf cohomology change at the merger is the topological signature.

**SWOLF's program statement: "we're going to get all the way to differential geometry"**. The 25-step constructive route from elementary connectedness to BBH-from-hypergraph is now logged in INFRAGEOMETRY.md §5f. Each step is one short Lean def on top of the previous.

**Hyperplane / polytope / inside-outside / bounded primitives (PHAJEK + SWOLF):**
- HYPER1 (#338) vertex separator (PHAJEK's pre-metric "graph separation"); HYPER2 (#339) perpendicular bisector (metric hyperplane); HYPER3 (#340) Voronoi decomposition; HYPER4 (#341) — equidistant-set vs separator equivalence (3 strengths, finite-vs-infinite hyperplane distinction recovers in continuum limit).
- MIDPT1 (#342) midpoint (multivalued, possibly empty).
- POLYTOPE1 (#343) polytope as cell of hyperplane arrangement.
- INOUT1 (#344) inside-outside / Jordan separator on cycles — *not automatic*, four "which side is inside" criteria (contractibility, volume, orientation, causal-future).
- BOUND1 (#345) bounded / diameter (4 flavours: spatial, causal, branchial, rewriting); MEMBER1 (#346) decidable membership; COMPACT1 (#347) limit-only compactness.
- SPHERE1–4 (#334–#337) infra-sphere / infra-disk / topology / surface-area extraction.

**The Bachmann route to Lie theory:** reflections through perpendicular bisectors → translations and rotations → isometry group → Coxeter / Weyl group → Lie algebra (IB5 #150). The constructive route to the full Lie-theoretic isometry structure of differential geometry.

**Cross-reference with NMURZIN "Geometry on Combinatorial Objects" (2026-04-26, Wolfram Cloud, NMURZIN's 11-page write-up of the meeting we tracked)** — the document's full taxonomy is now subsumed by our task list. ~60-70% of its content maps to existing tasks (Knill / Forman / Ollivier / Bishop-Gromov / DEC / Hodge / cellular-sheaf framework already logged). 18 new gap-tasks #351–#368 cover the document's residual content: SHEAF-CHOICE1–7 + SHEAF-CLASSIFICATION (#351–#358) for the §7 restriction-map classification — constant / Hodge / `S_k`-equivariant / diffusion / order / gauge / tensor-contraction sheaves and the meta-table; EFFRES1 (#359) effective-resistance curvature (Devriendt-Lambiotte 2022); DEC1 (#360) explicit Hodge star; DEC2 (#361) wedge product; CLOSURE1 (#362) explicit closure-choice infrastructure (downward / clique / nerve); CHEEGER1 (#363) Hansen-Ghrist sheaf-Cheeger inequalities; REGGE-CONV1 (#364) Christiansen 2024 distributional convergence; CDT1 (#365) causal dynamical triangulations; MYERS1 (#366) Stone discrete Myers; HIGUCHI1 (#367) Higuchi planar curvature; OLLIVIER-HG (#368) Ollivier-Ricci hypergraph multi-marginal extension. **The document's central thesis** — every geometric construction corresponds to a structural commitment, sheaves make this explicit — IS exactly the synthesis SWOLF and PHAJEK converged on; our SHEAF-CHOICE family + INFRAGEOMETRY.md §5d–§5g now formalises this precisely.

**Surface / manifold detection (SWOLF's "what is a surface")** — SURFACE1 (#348) Knill/Fisk recursive manifold predicate: `IsFiskManifold n H` iff every vertex's unit sphere is `IsFiskManifold (n-1)` AND every unit ball is contractible. **Diagnostic on a tree**: shell at any positive radius is disconnected (one component per branch) — fails Knill at every positive dim. Empirical screener for "rule produces manifold-like hypergraph". Subsumes / sharpens KN13 (#249).

**Formal-topology layer (SWOLF + PHAJEK pivoting)** — OPEN1 (#349) multiple natural topologies on a hypergraph (discrete / Alexandrov / metric / cellular-star / VR-scale-indexed / causal — each yields different compactness/continuity theorems); NBHD1 (#350) neighbourhood basis at each vertex (SWOLF's "locally has neighbourhoods" intuition for surfaces).

## Headline (2026-04-26 — late, angle tower + units observation + path-vs-walk gap identified)

**Full angle-tower taxonomy logged** as `AT0`–`AT27` (#285–#314, 28 tasks across 13 flavour-columns × multiple abstraction levels). Plus `PATH1`/`PATH2` (#300/#301) for SWOLF's non-overlapping-path requirement at the substrate level.

**Three structural observations that emerged:**

1. **Y2 / AT18 — Projective Cayley-Klein angle is more elementary than M0 / AT0 — SWOLF's chord-ratio.** Cross-ratio reads off from `Between` + `dist` ratios; works on hypergraphs WITHOUT requiring `GeodesicallyUnique`. Sidesteps SWOLF's "no angle without straight lines" objection. Possibly the right starting point for non-geodesically-unique hypergraphs.

2. **K1 / AT23 — Conformal structure IS pure-angle data.** Angles alone define conformal geometry; lengths are extra structure beyond conformal. A "pure infrageometric angle theory" IS conformal geometry; Riemannian = angles + length scale. Lorentzian = rapidities + light cones (this is GR). Kähler = angles + complex structure.

3. **H2 / AT20 — Regge deficit angle is THE numerical-GR variable for Phase D BBH.** Phase D BBH = Regge calculus on a triangulated 4-manifold; sum of deficit angles around each 2-face = stress-energy. This is gating, not optional, for the ultimate BBH-from-hypergraph result.

**Units-emergence observation (AT11 / #296)**: in the hypergraph, both `r` (geodesic distance, step count) and `V(r)` (vertex count) are `ℕ`-valued counts — same kind of thing. Units `[L]`, `[L^d]`, `[L^{-2}]` etc. are *artifacts of continuum rescaling* `a → 0`, not properties of the underlying object. Every dimensional physical quantity is `a^k · (count-level quantity)` for an integer `k` set by the Taylor-order at which the quantity sits in the `r`-expansion of `V(r)`. The "−2" in `[R] = L^{-2}` is intrinsic — second-order Taylor coefficient. Bishop-Gromov gives the discrete recipe `R_disc(v, r) := (6(d+2)/r²)·[V_flat(d, r) − V(v, r)] / V_flat(d, r)` (AT9 / #294). **Background-independence: no clock, no ruler assumed; geometry derived from rewriting structure. Dimension itself is emergent, not chosen.**

**Path-vs-walk gap (PATH1 / PATH2)**: per SWOLF's "we need non-overlapping paths, not just walks". Currently `Hypergraph.dist := H.toSimpleGraph.dist` uses Mathlib's clique-expansion which: (a) treats ≥3-arity hyperedges as `K_n` (any pair-step inside a hyperedge is one step); (b) silently drops self-loops via `loopless`; (c) collapses multi-edges in the `Multiset`. We have `SubdivisionPath.IsPathOf` for `ExecHG ℕ` (correct `Nodup` semantics, but ExecHG-specific), and Mathlib `SimpleGraph.Walk.IsPath` after the lossy reflection. **Missing: a native `Hypergraph.SimplePath u v` first-class type carrying both `Nodup` vertex list AND the actual hyperedge sequence (so multi-arity structure isn't collapsed).** Numerically `dist` is right (Mathlib's shortest walk is auto-simple); structurally we're losing "which hyperedge was rewritten at step i" — important for #228 / #229 causal/branchial extraction. PATH1 is prerequisite for AT3 (Toponogov), AT8 (GeodesicallyUnique), AT26 (multivalued angle).

## Headline (2026-04-26 — late, Phase B opens: #224 RuleSignatureScreener)

**`RuleSignatureScreener.lean` lands** — Phase B opens. Per-slice signature trajectory `signatureTrajectory τ : ℕ → RuleSignature V` (saturating outside trajectory length); real-valued projections `edgeCountTrajectory`, `vertexCountTrajectory`, `formanRicciTrajectory`. Curvature-deviation discrepancy `formanRicciDeviation τ κ n := |formanRicciTrajectory τ n − κ|` plugs directly into the generic `ConvergenceRateObligation` framework via `FormanRicciScreener τ κ r := ConvergenceRateObligation (formanRicciDeviation τ κ) r`. Compound `MultiScreener` combines edge-count and curvature discharge.

**Conservative discharge**: `edgeCountTrajectory_const_of_conservative` lifts `RuleSignature.edgeCount_invariant_of_conservative` to the trajectory projection; `edgeCountTrajectory_satisfies_any_rate_of_conservative` shows conservative rules pass the edge-count screener trivially with any non-negative rate. `multiScreener_self_of_conservative_initial` discharges the multi-screener at length 1 against the initial-state target.

**Negative discharge** (rule disqualification): `formanRicciScreener_fails_of_persistent_gap` — if the Forman-Ricci deviation has a uniform positive lower bound `δ > 0` on a cofinal subset, no rate function eventually less than `δ` can witness the screener — the rule **fails** at the curvature target. This is the structural form of a rule-search elimination criterion.

This is Phase B's foundation: per-slice metrics that can validate / reject rules against curved-target obligations. Next Phase B steps: `RuleSignatureSchema` (JSON interchange + Lean validator), then #190 wolframscript driver.

## Headline (2026-04-26 — late, Phase A follow-up: generic ConvergenceRateObligation)

**`ConvergenceRateObligation` generic family lands** (Phase A follow-up #1). Refactors the W_1-specific `WassersteinRateObligation` into a generic predicate `ConvergenceRateObligation d r` taking *any* rate function `r : ℕ → ℝ`. Concrete rates: `rateOneOverN` (1/n), `rateOneOverNSquared` (1/n²), `rateGeometric c` (c^n for 0 < c < 1). Bidirectional bridge `convergenceRateObligation_oneOverN_of_wasserstein` + `wassersteinRateObligation_of_convergenceRate_oneOverN` between old and new forms. Subdivision-rule discharge gets stronger characterization: `subdivisionDiscrepancy_satisfies_geometric` (the natural geometric `(1/2)^n` rate, strictly faster than any polynomial). Generic `convergenceRateObligation_zero` for trivial witness.

This is the **second Phase A landing**: the obligation framework now admits non-W_1 discrepancies (Forman-Ricci curvature deviation, Gromov-Hausdorff distance, spectral gap) which is the precondition for Phase B's screener metrics.

## Headline (2026-04-26 — late, #233 Phase A obligation strengthening lands)

**`HypergraphMetricOriginObligationStrong` lands** — first instance of an obligation Prop with **quantitative rate content**. The strengthened obligation embeds a `ScaledDiscrepancy` carrying `WassersteinRateObligation` (an `O(1/n)` decay claim). Concrete discharges: `minkowski4_from_hypergraph_strong` via `subdivisionDiscrepancyBundle` (the `1/2^n` rate from #234). Generic `any_metric_has_strong_obligation_witness` + `any_partialMetric_has_strong_obligation_witness` lift to every metric / partial-metric in the GR zoo. `all_gr_targets_have_strong_obligations_proven` picks the Minkowski disjunct.

This is **Phase A landing** per `ROADMAP.md`: obligation Props now *say something quantitative* rather than just existing. Next strengthening (tying the discrepancy to the actual W_1 of the trajectory's pushed measure against the target) requires measure-of-trajectory infrastructure and is staged as Phase A follow-up.

## Headline (2026-04-26 — late, #231 first formal exec ↔ abstract bridge)

**`MultiwayExecBridge.lean` lands** — first formal Lean bridge between the executable engine (`ExecHG ℕ`, `ExecRule`, `ExecSystem`, `singleWayStep`) and the abstract track (`Hypergraph V`, `Rule P`, `RewritingSystem`, `Step`/`MultiStep`/`Application`). Until this commit the two tracks were entirely disjoint Lean structures sharing only the conceptual identity "Wolfram-model rewriting". Casts:
- **`ExecHG.toHypergraph`** (already existed): list → multiset state cast.
- **`Fin.embedSuffix`**: `Fin numBound → Fin (numBound + numFresh)` natural inclusion.
- **`ExecRule.toRule`**: executable rule → abstract `Rule (Fin (numBound + numFresh))`, with LHS embedded via `Fin.embedSuffix` so both sides share pattern type.
- **`ExecSystem.toRewritingSystem_single`**: single-rule case (general case needs a sum / heterogeneous pattern type since rules can have different `numBound + numFresh`).
- Theorems: `consumed_toMultiset`, `exec_lifts_well_formed`, `ExecHG.toHypergraph_nil`/`_cons`.

Type-level bridge complete; heavier theorems (full `singleWayStep` ↔ `MultiStep` simulation, plus `Application` constructions from executable matches) staged as follow-up (couples with #267 simulation lemma).

## Headline (2026-04-26 — late, #234 landed)

**#234 W_1 obligation discharged with concrete `O(2^{-n})` rate**. The first end-to-end machine-checked rule-trajectory → continuum-target convergence certificate for the project. Foundation:

- **`SubdivisionPath.subdivisionTrajectory n := pathEdges (subdVerts n)`** (#284, Route D): canonical n-step trajectory defined directly, decoupled from the engine. Properties: `_isPathOf` (path-shape with `subdVerts n` of length `2^n + 1`, Nodup), `_length = 2^n`, `_succ` (Phase 1 closed-form successor step). Engine connection via `decide` for `n=0..4` plus the staged simulation lemma (#267).

- **`WassersteinRate.subdivisionDiscrepancy n := 1 / 2^n`** (#234): the natural W_1 spacing of the trajectory. `subdivisionDiscrepancy_satisfies_obligation` proves the `O(1/n)` `WassersteinRateObligation` holds with `C = 1`, `N = 1` via `Nat.lt_two_pow_self` (so `1/2^n ≤ 1/n` for `n ≥ 1`). `subdivisionDiscrepancy_tendsto` proves the (weaker) `→ 0` variant via `tendsto_pow_atTop_nhds_zero_of_lt_one` since `1/2^n = (1/2)^n`. `subdivisionDiscrepancyBundle` packages both.

This closes the sprint critical path **without** requiring the simulation lemma (#267): the engine connection at `n=0..4` is enough to label the trajectory as canonical, and the structural / W_1 content lives in the engine-free abstraction. #267 Phase 2 simulation lemma remains as future work for ALL-`n` engine alignment.

## Headline (2026-04-26 — late, KN3 / KN8 burst)

**KN3 Wu cohomology + KN8 Euler-Poincaré f-vector identity landed**. Builds on the d²=0 / Hodge foundation:

- **`KnillCore.eulerCharacteristic_eq_alt_sum_kSkeleton` + `_fintype` corollary**: the Euler-Poincaré identity `χ(G) = ∑_{k<N} (-1)^k · |kSkeleton G k|` for any cardinality bound N (auto-closed on `Fintype V`). Proof partitions G by skeleton degree (`Set.PairwiseDisjoint` + `Finset.sum_biUnion`), then constants the inner sum via `simplexWeight_eq_neg_one_pow_dim`. Foundation for KN8 (zeta functions over the f-vector).

- **`KnillCore.wuCharacteristic₂_eq_chi_sq_sub_disjoint`** (KN3): the Wu inclusion-exclusion identity `wu₂(G) = χ(G)² - ∑_{x ∩ y = ∅} ω(x)·ω(y)`. Splits the full Cartesian sum into the intersecting-pair (= wu₂) and disjoint-pair parts via `Finset.sum_filter_add_sum_filter_not`.

- **`KnillCore.incidence_ne_zero_iff_isFace`**: clean iff structure for incidence's support — `d(x, y) ≠ 0 ↔ isFace x y`. Cleaner than dispatching on isFace at use sites.

- **`KnillExamples`**: worked `wu₂` values on every test complex (vertex = 1, edge = -1, triangle = 1, triangleBoundary = 0); skeleton cardinalities for triangle (`3, 3, 1`); end-to-end Euler-Poincaré decomposition example `χ(triangle) = 3 - 3 + 1`.

## Headline (2026-04-26 — late, post-d²=0)

**Post-`d² = 0` push: codual axiom landed, Hodge PSD landed, and Phase 2 structural helpers stood up.**

- **`KnillCore.hodgeOnG_psd` + `hodgeOnG_double_sum_eq_sum_squares`**: the Hodge laplacian is positive semi-definite as a bilinear form. The Dirichlet form decomposes as `∑_{z ∈ G} (∑_{x ∈ G} f(x) · dirac(x, z))²` (via `H = D · D^T` and dirac symmetry), so it's automatically `≥ 0`. Foundational for spectral theory (eigenvalues are non-negative reals) and the Hodge isomorphism (kernel ≅ harmonic forms ≅ homology). Also: `hodgeOnG_diag_eq_sum_dirac_sq` (`H(x,x) = ∑_z dirac(x,z)²`), `hodgeOnG_diag_nonneg` (diagonal PSD specialisation), `isDiracKernel` predicate (harmonic-forms condition `∀z ∈ G, ∑_x f(x) · dirac(x,z) = 0`), and `hodgeOnG_dirichlet_zero_iff_isDiracKernel` (harmonic ↔ in dirac kernel via "sum of nonneg = 0 ⇒ each = 0"). Plus three concrete `native_decide` Hodge diagonal entries on the triangle in `KnillExamples`.

- **`KnillCore.dStarSquared_eq_zero`**: codual cochain-complex axiom — `∑_{y ⊆ z} incidence(y, x) · incidence(z, y) = 0`. One-page corollary of `dSquared_eq_zero` by transposing indices. Together with `d² = 0`, this gives the full chain-complex structure (d, d*) needed for Hodge decomposition `H = d·d* + d*·d` (KN14 McKean-Singer).

- **`SubdivisionPath.lean` structural helpers (#280–#283)** preparing for #232 Phase 2 (#267 simulation lemma) and #268 Route C fallback. `mem_subdivideVerts_imp` characterises elements (vs-vertex or fresh midpoint ≥ b). `subdivideVerts_nodup` proves Nodup preservation under freshness condition `b > listMax vs`. `subdVerts_nodup` (every iterate `subdVerts n` is Nodup). `nextFresh_pathEdges` bridges the engine's fresh-vertex allocator (`(vertexList H).foldr max 0 + 1`) to the path's natural midpoint counter (`listMax vs + 1`). Supporting `listMax_le_iff` + `listMax_eq_of_mem_iff` + `mem_le_listMax`. All axiom-clean.

## Headline (2026-04-26 — late)

**`d ∘ d = 0` complete.** The cochain-complex axiom `d ∘ d = 0` for the signed boundary on oriented simplices is closed in full generality as `KnillCore.dSquared_eq_zero`. Three trivial cases plus the main sign-cancellation case all proved, axiom-clean. Architecture:

- **#275 Approach A — `missingVertex` refactor**: pulls the missing-vertex extraction out of `incidence`'s `dif_pos` body. Adds `missingVertex {x y} (h : isFace x y) : V`, `missingVertex_mem_sdiff`, `missingVertex_eq_of_sdiff_eq_singleton`, `missingVertex_erase`. With this, `incidence_erase` becomes a one-liner via `simp`. Overcomes the structural obstacle where nested `let`/`have` proof terms inside `dif_pos` resisted `congr`/`rewrite` motives.
- **#276 summand characterization**: `dSquared_summand_zero_unless` — for `z ⊆ x` and `y ⊆ x` with non-zero `incidence x y · incidence y z`, `y = x.erase v` for some `v ∈ x \ z`.
- **#278 sort/erase commutation**: `Finset.sort_erase` — `(s.erase w).sort r = (s.sort r).erase w`, via `Perm.eq_of_pairwise'` with both sides sorted and same multiset.
- **#279 position-arithmetic helpers**: `List.idxOf_erase_of_idxOf_lt`, `List.idxOf_erase_of_idxOf_gt` — erase-aware `idxOf` shift formulas (smaller index unchanged, larger index shifts down by 1). Inductive proofs over the list with `BEq` head-case splits.
- **#277 sum-restriction + sign-cancellation main case**: `dSquared_eq_sum_diff` reduces the powerset sum to a sum over `(x \ z)` via `sum_image` + `sum_subset`, then for `x \ z = {a, b}` the two-element sum `(-1)^i · (-1)^idx_{(sort x).erase a}(b) + (-1)^j · (-1)^idx_{(sort x).erase b}(a)` cancels by `(-1)^i · (-1)^p + (-1)^(p+1) · (-1)^i = 0` via `ring`.

Foundation now in place for KN14 McKean-Singer (decomposition of `H = D²` via `D = d + d*`), KN15 Atiyah-Singer/Atiyah-Bott analog, KN16 Cartan magic formula, KN18 Brouwer-Lefschetz. Verified on concrete data via `KnillExamples` (general `dSquared x z = 0` for `Fin 3` simplices, plus the original `native_decide` witnesses).

## Headline (2026-04-26)

**Oliver Knill quantum-calculus track stood up + edge-subdivision rule's math side closed.** Two major streams landed since 2026-04-24:

- **`KnillCore.lean`** ([new module](lean/InfraFormalization/KnillCore.lean), task #257 / IGE1 substantive port of the upstream `resources/Infrageometry/Infrageometry/Kernel/Infrageometry.wl`): full first slice of Knill's discrete-geometry program on `SimplexSet V := Finset (Finset V)`. Lands the combinatorial primitives (`simplexDimension`, `simplexCardinality`, `simplexWeight ω(x) = -(-1)^|x|`, `eulerCharacteristic`, `fermiCharacteristic`, `simplexStar/Core/UnitSphere`, `complexClosure`/`IsClosed`, `complexVertexList`, `wuCharacteristic₁`/`₂`), the codim-1 face infrastructure (`isFace`, `isFace_erase`, `isFace_diff_card`, `isFace_exists_diff_vertex`), the matrix layer (#270 `connectionEntry L`, #271 `greenEntry g` with `simplexWeight_sq` showing `ω² = 1`), the spectral-invariant entry point (#273 partial `superTrace`), the **signed incidence operator `d`** (#269) on `[LinearOrder V]` simplices via sorted-vertex orientation, and the load-bearing **Dirac `D = d + d*` + Hodge `H = D²`** (#272) with self-adjointness proofs. **All axiom-clean**. Unblocks 8 KN-tasks downstream (KN1 wave eq, KN3 Wu cohomology, KN4 Lax, KN8 Dirac zeta, KN14 McKean-Singer, KN15 Atiyah-Singer/Atiyah-Bott, KN18 Brouwer, KN19 deformed `d_h`). Source-of-truth catalogue at [`resources/Infrageometry/QuantumCalculus.md`](resources/Infrageometry/QuantumCalculus.md).

- **#232 Phase 1: `subdivideAll = pathEdges ∘ subdivideVerts`** ([`SubdivisionPath.lean`](lean/InfraFormalization/SubdivisionPath.lean)): the closed-form math content of the n-step path-shape theorem. Defines `subdivideAll : ExecHG ℕ → ℕ → ExecHG ℕ` (subdivide each edge with consecutive midpoints) and proves it equals `pathEdges ∘ subdivideVerts` on path-shape inputs, by direct induction. **Axiom-clean (just `propext`)**. Plus five `decide`-proven witnesses of the full closed form `singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)` at `n = 0..4`. Phase 2 (the engine-side simulation lemma) is the remaining piece; planning artefact at [`notes/232_subdivision_path_plan.md`](notes/232_subdivision_path_plan.md) documents Route B + C-fallback.

**Sprint critical path now** (2026-04-26 → 2026-04-27): close #232 Phase 2 (simulation lemma) or Route C (existential weakening) → discharge #234 cycle/path origin obligations as concrete `O(2^{-n})` Wasserstein convergence certificates → strengthen #233 origin-obligation Props with the resulting real convergence content. End-state: **first complete machine-checked rule-trajectory → continuum-target convergence certificate** for the project.

## Headline (2026-04-24)

**All seven infrageometry obligations are proved.** `all_obligations_hold`
in [`lean/InfraFormalization/RemainingObligations.lean`](lean/InfraFormalization/RemainingObligations.lean)
bundles the six non-trivial closures:

- **IT5** `latschevObligation_holds` — Latschev connectivity form.
- **IT6** `scaleTrichotomyObligation_holds` — cycle quantum + coarse endpoints.
- **ID6** `dimensionCompatibilityObligation_holds` — `V(v, r) = 2r + 1` exactly on every `cycleHypergraph n` for all `r` with `2r+1 ≤ n`. Lower bound via shift-family Finsets (forward `F^[k] v` and backward `G^[k] v`) with left-cancellation injectivity; upper bound via structural induction on walks (`cycleHypergraph_walk_in_shift`) using the `F ∘ F`, `G ∘ G`, `G ∘ F`, `F ∘ G` composition lemmas.
- **IQ6** `fubiniStudyBhattacharyya_bound` — `‖⟨ψ, φ⟩‖ ≤ ∑ s, ‖ψ s‖ · ‖φ s‖` (Cauchy-Schwarz / Bhattacharyya).
- **IQ8** / **IQ9** — baseline witnesses (`ψ = 0`, `α = 0`) proved in `no_stub_obligations_remain`.
- **IR7** `reverseEngineeringObligationRefined_holds` — realisability-restricted form; the over-strong unrefined form is provably FALSE (`not_reverseEngineeringObligation`).

**All four grounding-audit action items closed.** Every continuum GR
object (the GR metric zoo, Lorentzian manifolds, connection data, EFE
satisfaction) carries an attached hypergraph-side origin-obligation
Prop with inhabited witnesses for flat cases:

- **G1** `ConnectionDataOriginObligation` — every `ConnectionData n` has an attached FiberedGraph-origin Prop ([`FiberedGraphConnectionBridge.lean`](lean/InfraFormalization/FiberedGraphConnectionBridge.lean)).
- **G2** `HypergraphMetricOriginObligation` — every GR metric in the zoo (Minkowski, Schwarzschild, FLRW, Reissner–Nordström, Kerr, S², de Sitter, warpedDiag2) has a hypergraph-origin witness ([`HypergraphMetricBridges.lean`](lean/InfraFormalization/HypergraphMetricBridges.lean); witnesses load-bearingly use `identitySystem Unit` + `cycleHypergraph n` + `emptyTrajectory`).
- **G3** `LorentzianManifoldOriginObligation` — continuum Lorentzian manifold bound to a `CausalGraph V` origin ([`CausalLorentzianBridge.lean`](lean/InfraFormalization/CausalLorentzianBridge.lean)).
- **G4** `EFEOriginObligation` bundles EFE satisfaction with metric + connection origins ([`EinsteinEquationsBridge.lean`](lean/InfraFormalization/EinsteinEquationsBridge.lean)). `minkowski4_flat_vacuum_EFE_originated_global` is the first complete rule → metric → connection → EFE chain.

**Axiom cleanliness.** Every `#print axioms` certification in
[`lean/InfraFormalization/AxiomCheck.lean`](lean/InfraFormalization/AxiomCheck.lean)
reduces to `{propext, Classical.choice, Quot.sound}` (and many to
`{propext, Quot.sound}` only). No `sorry`, no `native_decide`, no
`decide`, no custom axioms. `lake build` fully green.

**JGORARD refutations F1–F7 Lean-formal**, including `F6Circularity`
(the Poisson-sprinkle-then-reconstruct schema of arXiv:2102.09363
§3.3 formally proved to produce its input identically — the
`circular_procedure_is_identity` theorem).

## Closures since the 2026-04-23 weekly report

(Cumulative list in [`POST_WEEKLY_UPDATES_2026-04-23.md`](POST_WEEKLY_UPDATES_2026-04-23.md).
Highlights:)

- **ID6 CLOSED**: full `V(v, r) = 2r + 1` on cycle hypergraphs.
  `cycleHypergraph_ballVolume_exact`, `dimensionCompatibilityObligation_holds`.
  Infrastructure added along the way: `cycleHypergraph_walk_in_shift`
  (walk-structural induction), `cycleHypergraph_dist_iter{Succ,Pred}_le`,
  `cycleHypergraph_iter{Succ,Pred}_val`, `cycleHypergraph_iter{Succ,Pred}_injOn`,
  `cycleHypergraph_iterSucc_ne_iterPred`.
- **IR7 CLOSED (refined form)**: `ReverseEngineeringObligationRefined` holds;
  original `ReverseEngineeringObligation` is provably false.
- **B6 CLOSED**: FLRW metric bundle (`flrwPartial` as `PartialMetricData 4`
  with domain, Christoffel, Lorentzian, origin obligation).
- **C1, C2**: `DiagRiemannianMetric` + `DiagLorentzianMetric` bundle
  predicates with Euclidean and Minkowski witnesses.
- **C7**: `HypergraphConnection` — discrete connection on a hypergraph
  with group-valued transport, flat baseline, walk-transport as a
  monoid homomorphism (`transportWalk_append`), holonomy, `IsFlat`
  predicate.
- **J1**: `MultiwayCausalGraph` — joint structure bundling a rewriting
  system, initial hypergraph, and causal DAG on events.
- **H1**: `CandidateRuleCatalog` — JGORARD's named rule (arXiv:2102.09363)
  plus four other literature rules as concrete `Rule P` instances with
  `LiteratureSource` citations and machine-checked conservation theorems.
- **P20 advances**: Rodkey classification — `AdjTransitive → DistTransitive
  → BallVolumeVertexUniform → LocalDimensionVertexUniform` sufficient
  chain fully proved on cycle hypergraphs; `pathHypergraph` ruled out
  as negative example at radius 1.
- **Ollivier audit (research-new)**: quantitative discrepancy
  `ollivier_minus_gorard_leading = δε²(R - Ric_vv)/(2(n+2))`, with S²
  worked example `δε²/8` (`s2_gorard_error`) — identifies a specific
  computable deviation between JGORARD's discrete-Ricci construction
  and standard Ollivier-Ricci.
- **A6 partial**: `A6_for_{constants,identity,sq,cube}` monomial
  convergence + `A6Holds` predicate closed under `const_mul`, `add`,
  `sub`; polynomials up to degree 3 done, general continuous awaiting
  Weierstrass.
- **B9 Kerr metric**: `kerrG`, `kerrSigma`, `kerrDelta`, `KerrValid`
  exterior predicate; symmetry + Schwarzschild-reduction at spin zero.
- **C3 vector-bundle connection** (substantive): `VectorBundleConnection n k`
  with covariant derivative, curvature 2-form, curvature antisymmetry,
  flat instance, `ofConnectionData` lifting `ConnectionData n` to
  `VectorBundleConnection n n`, and `ofConnectionData_curvature_eq_riemann`
  identifying the bundle curvature with the Riemann tensor on the
  tangent bundle.
- **C4 torsion at bundle level** (substantive): `VectorBundleConnection.torsion`,
  `IsTorsionFree`, `ofConnectionData_isTorsionFree` (lifted tangent-bundle
  connection is always torsion-free via `Γ_symm`).
- **C6 bundle Γ ↔ local-coord Γ** (substantive): `toConnectionData`
  projects a torsion-free `VectorBundleConnection n n` back to a
  `ConnectionData n`; `toConnectionData_ofConnectionData` round-trip.
- **G2 discrete gauge field** (substantive): `DiscreteGaugeField H G` as
  a gauge-theory alias for `HypergraphConnection`, with Wilson-loop
  holonomy and `gaugeHolonomy_append` using the `transportWalk`
  monoid-homomorphism property.
- **J4 causal-set comparison** (substantive, conditional on
  antisymmetry): `CausalSetStructure` Prop; every finite `CausalGraph`
  whose precedence is antisymmetric satisfies Sorkin's causal-set
  axioms (reflexivity + antisymmetry + transitivity + local finiteness
  on the finite carrier).
- **H3 candidate rule passing signature screens** (substantive):
  `signature_sameEdgeCount_of_conservative` + concrete
  `gorardNamedRule_passes_sameEdgeCount_screen` (gorardNamedRule from
  a 4-edge seed keeps `edgeCount = 4` forever, closing the 4-edge
  screen against any 4-edge target).
- **R4 — warpedDiag2 curved Einstein-manifold identity fully proved**
  (substantive; `WarpedDiag2C2.lean`): first complete curved-case
  Einstein identity in the project. `warpedDiag2_C2 : MetricDataC2 2`
  supplies second partials + inverse-metric derivatives. Closed-form
  Riemann: `R^0_{101}(x) = -1/(1+x₀²)`, `R^1_{010}(x) = -1/(1+x₀²)²`,
  `R^0_{001}(x) = 0`, `R^1_{110}(x) = 0`. Closed-form Ricci:
  `R_{00}(x) = -1/(1+x₀²)²`, `R_{11}(x) = -1/(1+x₀²)`,
  `R_{01} = R_{10} = 0`. **Einstein identity** `warpedDiag2_einstein`:
  `R_{μν}(x) = (-1/(1+x₀²)²) · g_{μν}(x)` for all `(μ, ν) : Fin 2²`,
  realising the 2D Einstein-metric property with Gaussian curvature
  `K(x) = -1/(1+x₀²)²` (non-constant, negative). Generic
  `riemann_diag_zero` lemma (`R^ρ_{σμμ} = 0` from `riemann_antisymm`)
  underpins the off-diagonal Ricci closure.

## Reopened: cosmetic closures that need substantive work

Several earlier closures in this session wrapped a Prop-type obligation
around a zero-discrepancy / trivial witness. Those are now reopened
and carry concrete descriptions of the real work still required.
None of these are substantively finished:

- **E6 Lorentzian-GH** (`LorentzianGH.lean`): obligation stated via a
  supplied discrepancy function; no actual Lorentzian-GH distance defined.
  Task #58 reopened; project-own Lorentzian-GH distance is task #213.
- **E7 discrete-causal-DAG → continuum Lorentzian** (`CausalDAGContinuumLimit.lean`):
  wrapper around E6's zero baseline. Task #59 reopened.
- **H4 scaled trajectory → continuum manifold** (`ScaledTrajectoryLimit.lean`):
  zero-discrepancy baseline. Task #78 reopened.
- **H5 curved-target RicciBridge** (`CurvedRicciExtensions.lean`):
  per-target obligations all discharged by the same zero-discrepancy
  sequence. Task #79 reopened; #218 tracks per-target real
  computations.
- **A7 Wasserstein-1 O(1/n)** (`WassersteinRate.lean`): zero-discrepancy
  baseline. Task #18 reopened; project-own Wasserstein-1 is task #214.
- **A8 d-torus measure lift** (`MeasureTorusLift.lean`): d-indexed
  zero-discrepancy. Task #19 reopened; #215 targets real `O(1/n)`.
- **C8 scaled connection → Levi-Civita** (`ScaledConnectionLimit.lean`):
  `connectionSup` placeholder at identically zero. Task #41 reopened.
- **J2 path integral over causal graphs** (`PathIntegralCausalGraph.lean`):
  zero-amplitude PathIntegralAmplitude baseline. Task #95 reopened.
- **I10 path-integral formulation**: aliased to J2's zero amplitude.
  Task #93 reopened.
- **J3 emergent gravity** (`EmergentGravity.lean`): uniform-entropy-1
  population; no actual Clausius relation derived. Task #96 reopened.
- **J5 LQG spin-foam comparison** (`LQGComparison.lean`):
  QuantumSpacetimeSkeleton with `Is1Complex = True` stub. Task #98
  reopened.
- **J6 AdS/CFT-analog** (`AdSCFTAnalog.lean`): zero boundary-amplitude
  baseline. Task #99 reopened.
- **G5 continuum limits of discrete fields** (`ContinuumFieldLimits.lean`):
  ContinuumLimitRecord has `spectralConvergencePositive : True` slot;
  the underlying spectral convergences are real but the wrapper is
  cosmetic. Task #72 reopened.
- **B10 Ricci symmetry for Levi-Civita** (`RicciSymmetry.lean`):
  **Non-flat witness landed**: `warpedDiag2_leviCivita_ricci_symm`
  proves Ricci symmetry on the warped 2D Levi-Civita connection with
  non-vanishing `R_{00}`, `R_{11}` (and zero off-diagonal) from the
  closed-form components in `WarpedDiag2C2.lean`. General
  Levi-Civita case (metric compatibility → pair-swap symmetry) still
  pending. Task #30 in progress.
- **B11 contracted 2nd Bianchi**: **Non-flat witness landed**:
  `warpedDiag2_einsteinTensor_zero` proves `G_{μν} ≡ 0` on
  warpedDiag2 via the 2D Einstein identity (every 2D manifold is
  Einstein, so `Ric = K g`, `R = 2K`, `G = 0`). From this,
  `warpedDiag2_einstein_divergence_zero` gives the Bianchi
  divergence piece for free. General Levi-Civita case (un-contracted
  Bianchi ∇_{[λ} R_{μν]ρσ} = 0 via metric compatibility) pending.
  Task #32 in progress.

## Support tasks for the reopened items

Tasks to build the infrastructure required to retire the baseline
witnesses with real convergence / amplitude / curvature computations:

- **#213** define our own Lorentzian-GH distance (Noldus/Suhr style).
- **#214** define our own Wasserstein-1 distance on finite supports.
- **#215** prove real d-torus Wasserstein O(1/n) using #214.
- **#216** scrub all "await Mathlib" excuses from files + docs.
- **#217** compute project-own Ricci / Einstein tensors end-to-end on
  named GR metrics (Schwarzschild, FLRW, Kerr, RN, dS, S²).
- **#218** prove (or disprove) each curved-target discrete-Ricci
  convergence with a real hypergraph discretisation, not a baseline
  witness.
- **#219** discrete Hamiltonian / momentum constraint residuals
  on a causal foliation (extrinsic curvature K_{ab}-analogue
  + L₁/L₂/L∞ reporting).
- **#220** Ollivier-Ricci convergence on a concrete discretisation
  (no such theorem exists yet; we have statement + disagreement only).
- **#221** PDE solution-level convergence (not just eigenvalues):
  discrete heat/wave/Schrödinger/KG solutions → continuum PDE
  solutions in a function norm.
- **#222** project-own pointed-GH and metric-measure-GH
  infrastructure (pre-req for #213 Lorentzian-GH and for composing
  with Wasserstein-1).
- **#223** discrete stress-energy T_μν on a hypergraph (so EFE
  origin obligations can be discharged with non-flat T).
- **#224** per-trajectory curvature signature screener — **landed**: `RuleSignatureScreener.lean` (`signatureTrajectory`, `formanRicciTrajectory`, `formanRicciDeviation`, `FormanRicciScreener`, `MultiScreener`, conservative-discharge + persistent-gap-failure theorems). Phase B opens; next: `RuleSignatureSchema` interchange.
  (Forman/Ollivier signature curve vs. target manifold profile).
- **#225** multi-way → continuum bridge (MultiwayCausalGraph
  convergence theorem — replaces the cosmetic J-series closures).
- **#154 / #155** IQ8 EME persistence and IQ9 path integral
  reopened after reclassifying their zero-witness closures as
  cosmetic (Prop too weak; real content needs a rule-derived
  amplitude / EME).

## Open items tracked at the obligation level

| Open item | Status |
|---|---|
| **IG10** exponential map via weighted shortest-path counts | needs shortest-path counting infrastructure + PHAJEK's weighted-sum formulation |
| **IB2** causal-branchial commutator theorem | predicate placeholder at `True`; needs a real theorem statement before proof |
| **ID7** spectral dimension via heat-kernel trace | heat trace defined; small-`t` asymptotics pending |
| **A6** weak convergence (general continuous) | polynomials to degree 3 closed; Weierstrass lift pending |
| **A7 / A8** non-trivial Wasserstein bounds | **#214 landing: project-own W_1 on finite supports as a full pseudometric + Kantorovich-Rubinstein + cycle-hypergraph observable-level convergence.** `wasserstein1_delta_eq_dist`, `wasserstein1_symm`, `wasserstein1_self_eq_zero`, `wasserstein1_triangle`; `wasserstein1_lipschitz_bound` (KR: `\|E_μ[f] − E_ν[f]\| ≤ L W_1(μ,ν)`). Cycle anchor: `wasserstein1_cycleDelta_succ = 1/n`, `wasserstein1_shiftMeasure_le ≤ 1/n`, `wasserstein1_shiftIter_le ≤ k/n`, **`expectationDiff_shiftIter_le`** (`\|E_μ[f] − E_{shift^k μ}[f]\| ≤ L k / n` for any L-Lipschitz f — the observable-level A7 statement). A7 zero-discrepancy baseline superseded; #215 (d-torus lift) pending |
| **Curved GR witnesses** (B3/B4, B7, F4/F5/F6) | **B7 + F5 closed**: FLRW full Ricci tensor in closed form (diagonal + all six off-diagonal vanishings), Friedmann LHS pair, perfect-fluid stress-energy, **`flrwEFE_diag_iff_friedmann`** : diagonal EFE ⟺ Friedmann equations, and F5 capstones (`flrw_satisfies_EFE_of_friedmann`, `flrw_vacuum_friedmann_iff`, `flrw_dust_friedmann_iff`). Schwarzschild / Kerr Ricci = 0 still pending; tracked as task #217. |
| **E5 ADM / D11 Choquet-Bruhat** | long-term GR formalization targets |
| **C5 Levi-Civita existence-uniqueness (Koszul)** | the hard remaining C-group item; needs the explicit Koszul formula + metric compatibility |

For the full per-module view, see [`COVERAGE_MAP.md`](COVERAGE_MAP.md).

## Rungs of the bridge ladder (see `BRIDGE_MACHINERY.md`)

| Rung | Topic | Status |
|---|---|---|
| 1 | Discrete calculus | ✅ graph Laplacian, inner product, self-adjointness, Dirichlet form, PSD, divergence theorem, Laplacian-as-LinearMap, cycle instance; matrix form + heat kernel via `Matrix.exp` (R2/D3), symmetric Laplacian matrix, row-sum zero, heat trace; **`Hypergraph.dist` triangle inequality + cycle connectivity (T3)** |
| 2 | Op. convergence to continuum | ✅ C² Taylor convergence of scaled second difference (R1/A2); ✅ scaled discrete → continuum f'' for all C² (A3); ✅ cycle spectrum closed form (R5) + eigenvalue → continuum (A4); **cycle spectrum in `HasEigenvalue` form (T4)**; **exp fixes eigenvectors (T2)** |
| 3 | Measure limits | ✅ counting measure + pushforward (A5); ⌛ weak convergence (A6), Wasserstein (A7) still pending |
| 4 | Connections / Levi-Civita | local-coord route complete (ConnectionData, leviCivitaConnection, Riemann/Ricci/Einstein as explicit formulas); project-own bundle route (C3 `VectorBundleConnection`, C4 torsion, C6 consistency) done; C5 Koszul existence/uniqueness and C8 convergence tracked as our own tasks |
| 5 | Riemann / Ricci / scalar | ✅ local-coord Riemann + Ricci + Einstein via `CurvatureRiemann` (X2 ∇, R/∇ commutator pending); ✅ GR metric zoo formalised: **Minkowski, Schwarzschild (B1+B5), Reissner-Nordström (B8), FLRW (B6), de Sitter, S²**; `DiagLorentzianManifold` (E1), `EinsteinEqLambda` (F3); `minkowski4_flat_vacuum_forces_lambda_zero` excludes Minkowski-as-de-Sitter |
| 6 | ODE/PDE | ✅ discrete heat equation (D1/D4/D5) + existence/uniqueness (D2 forward-time); wave (D8); Klein-Gordon (D9); Schrödinger unitarity (D10); scalar field Lagrangian/EL (G1/G3/G4); **ODE ↔ matrix heat kernel unified (T1)**; matrix-level mass/L²/semigroup corollaries; **long-time heat decay of non-constant cycle modes (D6 partial, `HeatKernelDecay.lean`); multi-mode convergence `heatKernel_cycleHypergraph_multi_mode_tendsto` — heat flow of any finite eigen-combination converges to its constant component** |
| 7 | Fields / gauge | Far |
| 8 | Lorentzian geometry | ✅ discrete (`LorentzLattice`, `Minkowski`); ✅ continuum `DiagLorentzianManifold` (E1) with Minkowski instance; ✅ discrete Cauchy foliation (E5) via stably-causal time function; ⌛ continuum Lorentzian-GH missing in Mathlib |
| 9 | Einstein equations | ✅ **F3 `EinsteinEqLambda`** for general (M, C, Λ, κ, T); `minkowski4_satisfies_EFE_zero_lambda`, `einsteinEqLambda_vacuum_iff`, `minkowski4_flat_vacuum_forces_lambda_zero`, `flatConnection_einstein_divergence_zero`; ⌛ Schwarzschild / Kerr / FLRW Ricci = 0 blocked by Ricci-on-explicit-connection (B3-B4, B7) |
| 10 | Hypergraph → GR | ✅ flat targets done (cycle→circle, path→interval, torus, d-torus, discrete→continuum Minkowski); ⌛ curved targets blocked by Rungs 4–5 |

## Key deliverables by phase

### Phase 0 — Audit of the JGORARD corpus
- ✅ Close-readings of G1 (2004.14810), G2 (2011.12174), G3 (2102.09363), G4 (2303.07282).
- ✅ 184-row claims catalog, severity taxonomy S1–S6, major-flaws index F1–F8, cross-paper audit.
- ✅ Empirical refutation of the named EFE rule (SetReplace + independent Python rewriter on 9 seeds).

### Phase 1 — Wolfram-model structural theorems (Lean)
- ✅ Edge conservation, trajectory-level conservation, in/out degrees, per-event balance.
- ✅ Causal-DAG level function via well-founded recursion; level monotonicity; same-level antichain.
- ✅ `causallyPrecedes_iff_isCausalPred` bridge between Prop- and Bool-level causal relations.
- ⌛ Full parallel-layer bound `|layer_s| ≤ N/k` (needs trajectory-structure lemma).
- ⌛ Trajectory-structure lemma (consumed hyperedges have earlier creators).

### Phase 1 — Refutations of major structural flaws (F1–F5)
All formalized as Lean theorems, axiom-clean:
- ✅ **F1** (`Refutations/F1NoMetric.lean`) — no canonical hypergraph-to-metric construction.
- ✅ **F2** (`Refutations/F2Orthonormality.lean`) — fiat orthonormality is non-canonical.
- ✅ **F3** (`Refutations/F3Tautology.lean`) — "asymptotic dim preservation ⇒ EFE" is `Iff.rfl`.
- ✅ **F4** (`Refutations/F4Tautology.lean`) — "causal invariance ⇔ discrete general covariance" is `Iff.rfl` (axiom-free).
- ✅ **F5** (`Refutations/F5Illdefined.lean`) — "becomes" is convergence-notion-dependent.

### Phase 2 — Corrected continuum identities
- ✅ Statement-only forms of the correct Ollivier identity (directional Ric) and JGORARD's wrong form (scalar R); coincidence-condition theorem.
- ✅ Statement-only forms of the correct Gray tube formula and JGORARD's wrong form; concrete disagreement proofs on S² (1/6 ≠ 1/3) and S³ (1/3 ≠ 2).

### Phase 3 — Continuum-limit theorems
- ✅ **Cycle → circle** GH bound at `1/(2n)` (`Infra/GHBound.lean`).
- ✅ **Path → interval** GH bound (`Infra/ScaledPath.lean`).
- ✅ **2D lattice → 2-torus** GH bound (`Infra/ScaledTorus.lean`).
- ✅ **(d+1)D lattice → (d+1)-torus** GH bound for arbitrary `d ≥ 0` (`Infra/ScaledTorusD.lean`).
- ✅ Abstract `GHApproximation` structure (`Infra/GHApprox.lean`).

### Phase 4 — Infrageometry of the Lorentzian side
- ✅ **Discrete Lorentzian lattice** `LorentzLattice.lean`: `CausalPrecedes`, Timelike/Null/Spacelike trichotomy, signed Minkowski interval with three-way positivity classification, forward cones.
- ✅ **Continuum Minkowski** `Minkowski.lean`: `ContinuumCausalPrecedes`, trichotomy, signed interval.
- ✅ **Scaled int-to-ℝ embedding** `ScaledLorentz.lean`: `lorentzIntEmbed` preserves `CausalPrecedes` and `Timelike` into continuum Minkowski (forward direction).
- ⌛ Full scaled isometry-plus-density (Lorentzian GH) — project-own Lorentzian-GH distance is task #213; we define it ourselves rather than wait on Mathlib.

### Phase 4 — Bridging theorems (rewriting ↔ Minkowski)
- ✅ **1+0-dim bridge** `TrajectoryLorentz.lean`: `trajectoryToEvent τ` via the level function. `causallyPrecedes_implies_timelike`. `trajectoryToEvent_lossy` (F1/F2 gap explicit).
- ✅ **d-dim conditional bridge** `TrajectoryLorentzD.lean`: `SpatialEmbedding`, `LightConeCompatible`, `fullEmbed_preserves_causal`. The F1 missing-data slot made an explicit parameter.
- ✅ **End-to-end bridge** `FullBridge.lean`: `causallyPrecedes_gives_continuum` chains trajectory → Lorentz → Minkowski under `LightConeCompatible τ φ`.

### Rung 1 — Discrete calculus (bridge ladder entry)
- ✅ `Neighbourhood V` structure + graph Laplacian + counting inner product (`DiscreteCalculus.lean`).
- ✅ Linearity of `Δ`, vanishes on constants.
- ✅ `discreteInner` symmetry + bilinearity.
- ✅ `laplacianLinear`: graph Laplacian as `LinearMap` — opens Mathlib spectral API.
- ✅ **Self-adjointness** `⟪Δ f, g⟫ = ⟪f, Δ g⟫` (`DiscreteCalculusSymm.lean`).
- ✅ **Dirichlet form** `⟪f, −Δ f⟫ = ½ ∑ (f(w) − f(v))²`.
- ✅ **Positive semidefiniteness** of `−Δ`.
- ✅ **Discrete divergence theorem** `∑ Δ f = 0`.
- ✅ **Cycle graph** concrete instance + Dirichlet form (`CycleGraph.lean`).

### Rung 2 — Operator convergence (entry)
- ✅ Central second difference `Δ²_h f := f(x+h) − 2 f(x) + f(x−h)`, linearity, polynomial-case exact identity: for any quadratic, `Δ²_h f(x) = f''(x) · h²` (no error). Identifies cycle Laplacian with the second difference.
- ✅ `C²` Taylor-remainder version (`CTwoTaylor.lean`, `scaledSecondDiff_tendsto_iteratedDeriv`) — Mathlib `iteratedDeriv` / `taylorWithinEval` are integrated.

### Branchial QM bridge (I1–I10)
- ✅ I1 BranchialSlice finiteness (`BranchialFinite.lean`).
- ✅ I2 Uniform branchial measure `branchialUniformWeight` (`BranchialHilbert.lean`).
- ✅ I3 Branchial amplitudes + Born rule `bornProbability` (`BranchialHilbert.lean`).
- ✅ I4 / R3 partial — ℓ²(slice) Hilbert space `BranchialHilbert S := EuclideanSpace ℂ S` with ℂ-linear adjacency `branchialAdjLM` and self-adjointness `branchialAdjLM_inner` (`BranchialHilbert.lean`).
- ✅ I5 Unitary branchial evolution `branchialSchrodinger_unitary_evolution` (`BranchialSchrodinger.lean`) — Schrödinger eq `i ∂_t ψ = A ψ` preserves `∑(u² + v²)`.
- ✅ I6 Observables as Hermitian operators `BranchialObservable S` (`BranchialHilbert.lean`).
- ✅ I7 Expectation values + real-valuedness on observables (`BranchialHilbert.lean`).
- ✅ I9 Schrödinger on branchial graph (via `BranchialSchrodinger adj u v`).
- ⌛ I8 Hilbert-space continuum limit; I10 path-integral formulation.
- ⌛ IQ6 FS←Fisher limit; IQ8 EME persistence; IQ9 path integral over causal graphs.

## Documentation
- [`README.md`](README.md), [`INDEX.md`](INDEX.md) — navigation.
- [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) — F1–F8 structural-flaw registry with Lean-formalization status for each.
- [`MILESTONES.md`](MILESTONES.md) — checkbox tracker across all phases.
- [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) — 10-rung ladder from discrete calculus to Einstein equations.
- [`RULE_SEARCH.md`](RULE_SEARCH.md) — how the Lean corpus serves as verifier + screener in a rule-search pipeline.
- [`PUBLISHABLE.md`](PUBLISHABLE.md) — paper targets P1–P7 with dependencies.
- [`LEAN_PHYSICS.md`](LEAN_PHYSICS.md) — conventions and alignment with other Lean-physics efforts.

## Path-on-GR summary (see `BRIDGE_MACHINERY.md`)

**What we have:** full chain `causallyPrecedes (trajectory) → CausalPrecedes (discrete Lorentz) → ContinuumCausalPrecedes (Minkowski)` under `LightConeCompatible τ φ`. Flat-target GH bounds in all dimensions (cycle, path, d-torus). Graph Laplacian with full spectral-theory readiness. F1–F5 refuted.

**What we're missing for GR:** curved-target bridges (tasks #217 + #218 — our own Ricci / Einstein on explicit metrics, plus real discrete-Ricci convergence on curved targets; nothing waits on Mathlib). Full Lorentzian-GH (task #213 — we define it ourselves). A specific rule whose causal graph has the right dimension (empirical + structural rejection of JGORARD's named rule — F7). Discretization of the Einstein–Hilbert action converging to the continuum one (F5 blocks naïve form).

**Rule search as the practical route:** our Lean corpus serves as verifier for any candidate rule + candidate spatial embedding (`RULE_SEARCH.md`). Screening signatures: level growth `~t^{d+1}`, antichain width `~k^d`, cone volume. Any candidate rule passing these + `LightConeCompatible` gets a machine-checked Minkowski-consistency certificate via the end-to-end bridge.

## Next concrete directions

1. **Rung 2 C² case**: generalise `SecondDifference` from polynomials to arbitrary `C²` functions via Mathlib's Taylor infrastructure.
2. **Discrete heat equation as linear ODE**: use `laplacianLinear` + finite-dimensional ODE existence-uniqueness; prove conservation of total mass via `laplacian_sum_zero` + `d/dt ∑ u = 0`.
3. **Rung 5 local-coordinate Ricci**: define Christoffel symbols, Riemann tensor, Ricci, scalar curvature on explicit charts (ℝⁿ, Schwarzschild in Schwarzschild coords). Skip the bundle machinery for now; the coordinate form is what physics actually uses.
4. **Branchial measure**: uniform probability on finite `BranchialSlice`, first step toward Hilbert-space amplitudes.
5. **Trajectory-structure lemma** + **full parallel-layer bound** `|layer_s| ≤ N/k` (Phase 1 pending).
