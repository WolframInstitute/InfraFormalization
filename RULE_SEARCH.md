# Rule search via the Lean machinery

Our infrageometry Lean corpus can be used as a **verifier** and **screener** in a rule-search pipeline aimed at finding Wolfram-model rewriting rules whose causal graph converges to a Lorentzian manifold. It does **not** generate rules — that is a separate combinatorial-search problem. What it does is give formal grounds for accepting or rejecting candidates, and quantitative dimensional signatures that drive the rejection phase.

## What the Lean corpus provides

### Negative screening (fast rejection)

| Mechanism | Lean primitive | What it rules out |
|---|---|---|
| Conservation forces constant state size | `Application.size_result_of_conservative` | Rules where the causal graph can grow in density; places an upper bound on cone dimension. Refutes JGORARD's named rule (F7). |
| Same-level antichain | `same_level_ordered_antichain`, `no_causal_edge_within_level` | Rules whose causal DAG lacks consistent level structure (shouldn't happen for well-formed trajectories, but the formal invariant is available). |
| Linear cone growth empirically | (combinatorial; driven by level and causal-precedence counts) | Rules with cone dimension 1 on any seed — cannot support 3+1-dim Minkowski. |

### Quantitative signatures

These are the per-rule observables that should track dimensional expectations:

1. **Level-growth signature.** For a (d+1)-dim Minkowski target:
   `|{j : j < N ∧ level τ j ≤ t}|  ~  t^{d+1}` (as `t` grows within the trajectory).
   Formal grounds: `level_add_one_le_of_isCausalPred`, `level_eq`.

2. **Antichain-width signature.** For d spatial dimensions:
   `|{j : level τ j = k}|  ~  k^d`.
   Formal grounds: `no_causal_edge_within_level` (antichain structure).

3. **Forward-cone volume.** `|{j : causallyPrecedes τ i j ∧ level τ j ≤ level τ i + t}|  ~  t^{d+1}`.
   Formal grounds: `causallyPrecedes_implies_minkowski`, `causallyPrecedes_implies_timelike`.

4. **Bridging consistency.** Given a candidate spatial embedding `φ : event-index → Fin d → ℤ`, check that every `causallyPrecedes τ i j` pair satisfies `Timelike d (fullEmbed φ i) (fullEmbed φ j)` in the Lorentz lattice. This is decidable and mechanisable. The 1+0-dim version is already proved automatic (`causallyPrecedes_implies_timelike`); higher-dim is a conditional theorem parameterised by the embedding.

### Executable-side screening, Lean-alone (#384)

`RuleSignatureExecMetrics.lean` makes a candidate rule screenable **without leaving Lean and without reconstructing an abstract `Trajectory`**. The engine's states are `ExecHG ℕ` (ℕ-vertex hyperedge lists); the signature metrics are recomputed on the finite carrier `vertexList H`, so every verdict is `decide`/`native_decide`-checkable.

Pipeline per candidate `ExecRule r`, seed `H`, horizon `n`:
1. `d := canonicalDossier r H n` — run the engine (`singleWayEvolve`), recording the trajectory. `canonicalDossier_isConsistent` guarantees `d` is the genuine engine run; #377 guarantees no other consistent trajectory exists.
2. `d.signatureVerdict : SignatureVerdict ⟨edgeCounts, vertexCounts, formanScalars⟩` — the per-state metric triple, computed from the run alone.
3. Accept / reject by decidable predicate:
   - `d.formanScalarConstant` — conservative / flat-target pass.
   - `d.formanScalarReaches tgt` — positive verdict (final state hits the target curvature).
   - `d.formanScalarPersistentGap tgt` — negative discharge (no state ever attains `tgt`; reject for this seed).

The metric primitives are `execAdj`, `execAdjDegree`, `execTriangles`, `execFormanEdge` (= `Hypergraph.formanRicciEdgeTriangle`: `4 − deg u − deg w + 3·#△`), and `execFormanScalar` (= `Hypergraph.formanRicciTriangleDoubled`). Worked example: the edge-append rule from a single edge certifies `⟨[1,2,4,8], [2,3,5,9], [4,4,0,-12]⟩` — the Forman scalar going negative is the tree-like / hyperbolic signature, a decide-checked rejection against any flat or positively-curved target.

**Engine-port spec.** This `SignatureVerdict` triple, computed by exactly these formulas, is the metric set to port into RASSAR's `HypergraphRewritingEngine` (the fast engine). The engine is the at-scale generator+runner; Lean fixes *what* it must compute per state and certifies the screening logic on small instances. Open enumeration (#190) drives candidates through this same screener.

### A complete Lean-alone search loop (#384 + #385)

`RuleSignatureExecSearch.lean` closes the loop: **generate → run → classify → select**, all `decide`/`native_decide`-checkable.

- **Generate.** `enumerateRules2_1 maxRHS` is a bounded rule generator (not a hand-list): single-edge LHS `{0,1}`, RHS any nonempty subset (size ≤ `maxRHS`) of the ordered pairs over `Fin 3` (two bound + one fresh vertex). 21 candidates at `maxRHS = 2`.
- **Classify.** `trendOf r seed n` runs the candidate (`canonicalDossier`) and reduces its Forman-scalar trace to a `CurvatureTrend` (`flat` if constant, else the sign of the final scalar: `positive` / `negative` / `zero`).
- **Select.** `selectByTrend cands seed n tgt` keeps the candidates matching a target trend — the search filter.

Certified result on the single-edge seed at two steps: the 21 candidates partition into **13 flat, 4 zero-non-constant, 2 negatively-curved (tree-like / hyperbolic), 2 positively-curved** (`13 + 4 + 2 + 2 = 21`, classification total). This is a machine-checked demonstration that the screener discriminates curved from flat rules, and the template for at-scale search once the same `CurvatureTrend` logic runs in the fast engine.

This is a finite-horizon, bounded-family search; scaling up the family size, the horizon `n`, and the seed set is mechanical (and the point where the fast engine takes over). The trend is a *coarse* proxy — final-state Forman sign — not yet a convergence-rate verdict; tightening it to a `ConvergenceRateObligation`-style accept criterion is the next refinement.

### Verification scaffolding

Once a candidate rule is found:
- Instantiate `Trajectory sys init` for sample trajectories of the rule.
- Compute `level τ` — it is a formally-valid Minkowski time coordinate (`trajectoryToEvent_preserves_causal`).
- The bridging theorems (`causallyPrecedes_implies_timelike`, `trajectoryToEvent_lossy`) transfer automatically. No re-proof per rule.
- Any chosen spatial embedding can be checked for `Timelike`-consistency per causal pair, giving a formal certificate.

## What the Lean corpus does not provide

- **Rule generation.** No enumeration, no evolutionary search, no physics-priors. A separate generator is required (`../efficient_rewriting_final/`, `SetReplace`, heuristic search).
- **Canonical spatial embedding.** F1 rules this out structurally. The best we can offer is: "given this chosen embedding, Lean certifies Minkowski consistency." The embedding itself is a non-canonical choice.
- **Curvature certification.** Currently at statement level for Ollivier and Gray, plus proven disagreement of JGORARD's forms on S² and S³; the concrete Ricci / Einstein computation on named metrics is task #217.

## Practical pipeline

The natural build-out is a harness:

1. **Generator** — `../efficient_rewriting_final/` emits trajectory data (initial hypergraph + sequence of applications) per candidate rule.
2. **Python screener** — computes level distribution, antichain widths, cone-volume growth from the trajectory data.
3. **Polynomial-growth filter** — rejects rules failing the `t^{d+1}` and `k^d` signatures for targeted `d`.
4. **Spatial-embedding search** — for surviving rules, attempt embeddings (graph-layout algorithms, spectral embedding, heuristic) into `Fin d → ℤ`.
5. **Lean certificate** — export the trajectory into Lean's `Trajectory` type, load the chosen embedding, and the bridging theorems produce a formal certificate of Minkowski-consistency.

Steps 1–4 are engineering; step 5 is the payoff of our current Lean corpus.

## Scope honesty

This pipeline *verifies* that a candidate rule has causal-graph structure consistent with a chosen Lorentzian target. It does not:
- prove the rule's causal graph *converges* to Lorentzian spacetime (needs a scaled-trajectory GH theorem, not yet formalised);
- produce curvature data (task #217 — project-own Ricci on named metrics);
- prove the target is an *Einstein* manifold (needs the action convergence of F5, which is open).

Those are the remaining structural gaps — tracked in `MILESTONES.md` under Phases 4, 5, and 6.

## References

- `lean/InfraFormalization/CausalLevel.lean` — level function + monotonicity + antichain.
- `lean/InfraFormalization/Infra/TrajectoryLorentz.lean` — 1+0-dim bridging.
- `lean/InfraFormalization/Infra/LorentzLattice.lean` — `CausalPrecedes`, `Timelike`, `Null`, `Spacelike`, `minkowskiIntervalSq`.
- `results/phase1_selfaudit/` — empirical cone-dimension rejection of JGORARD's named rule.
- `MAJOR_FLAWS.md` — F1 (no canonical metric), F2 (fiat orthonormality), F5 (ill-defined limit).
