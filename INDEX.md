# Project index

Complete navigation for `infra_formalization`. This file is hand-maintained; every document in the repo appears below with a one-line description. New readers: start at [`README.md`](README.md), then read sections in the order suggested.

## Start here

| Document | Purpose |
|---|---|
| [`README.md`](README.md) | Entry point — project posture, verdict status table, reproduction instructions, layout. |
| [`INFRAGEOMETRY.md`](INFRAGEOMETRY.md) | Research program: long-term roadmap (audit → correction → positive construction); phases 0–6 with honest timescales. |
| [`GLOSSARY.md`](GLOSSARY.md) | Definitions of every technical term used in this project (causal invariance, branchial graph, tetrad, Ollivier–Ricci, infrageometry, etc.). |
| [`FINDINGS.md`](FINDINGS.md) | Canonical one-line summary of every refuted / verified / open claim, grouped by severity. |
| [`NEXT_STEPS.md`](NEXT_STEPS.md) | What's done, what's in flight, what's waiting for a decision. |
| [`MILESTONES.md`](MILESTONES.md) | Checkbox tracker across all 7 phases, with `[x]` / `[ ]` / `[~]` / `[!]`. |
| [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) | F1–F8 structural flaws in the Gorard corpus, separated from arithmetic errors. |
| [`LEAN_PHYSICS.md`](LEAN_PHYSICS.md) | Survey of existing Lean-physics conventions; how we align. |
| [`RULE_SEARCH.md`](RULE_SEARCH.md) | How the Lean corpus serves as a verifier/screener in a rule-search pipeline — signatures, screening tests, certificate scaffolding. |
| [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md) | The 10-rung ladder from discrete calculus to Einstein equations. What Mathlib has, what we have, what each rung needs, priority order. |
| [`publications/`](publications/) | Each subfolder = one paper (I = incremental, M = major). |

## Methodology and synthesis

| Document | Purpose |
|---|---|
| [`notes/plan.md`](notes/plan.md) | 7-phase verification methodology with quadruple-rail rules. |
| [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) | S1–S6 classification of all 16 distinct errors, with a discussion of how the errors recur. |
| [`notes/corpus_audit.md`](notes/corpus_audit.md) | Cross-paper map: which errors originate in which paper and propagate to which others. |
| [`notes/claim_assessment.md`](notes/claim_assessment.md) | Per-claim synthesis (True / Conjectural / Hunch / Tautology / Error) with overall verdict: "the texts claim more than their arguments establish, and contain no fabricated data." |
| [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) | Why Gorard uses single-way evolution, why this is inconsistent, why our refutations still hold, where the null tetrad and GR machinery actually live. |

## Per-paper close-readings

| Document | Paper | Focus |
|---|---|---|
| [`notes/2004.14810_close_reading.md`](notes/2004.14810_close_reading.md) | G1 — *Some Relativistic and Gravitational Properties* | Gap analysis of §2 (Space/Time) and §3 (Geometry/EFE). The original source of the main "derivation." |
| [`notes/2102.09363_close_reading.md`](notes/2102.09363_close_reading.md) | G3 — *Hypergraph Discretization of the Cauchy Problem* | The circularity chain: Poisson-sprinkle the known target manifold, apply Benincasa–Dowker, "recover" the manifold. |
| [`notes/2303.07282_close_reading.md`](notes/2303.07282_close_reading.md) | G4 — *Non-Vacuum Solutions, Gravitational Collapse, Discrete Singularity Theorems* | Title promises discrete Raychaudhuri + singularity theorems; body delivers continuum collapse + mesh validation, no discrete theorem. |
| [`notes/claims_catalog.md`](notes/claims_catalog.md) | G1 | 184-row audit of every equation, align, definition, with per-row status verdict. |
| [`notes/continuum_limit_claims.md`](notes/continuum_limit_claims.md) | G1–G4 | Every claim in the corpus that asserts convergence to a continuum geometric/physical object, with verbatim quote and audit verdict. Load-bearing claims marked 🧨. |

## Topic notes

| Document | Topic |
|---|---|
| [`notes/null_tetrad_resolution.md`](notes/null_tetrad_resolution.md) | The null tetrad is built on the CCZ4 continuum metric, not on the hypergraph. See also [`singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) §5. |
| [`notes/limit_toolkit.md`](notes/limit_toolkit.md) | Inventory of convergence theorems in the mathematical literature (Ollivier, Gray, Benincasa–Dowker, Gromov–Hausdorff, Noldus-Suhr, spectral, graphon) and which are proved vs conjectural. |
| [`notes/empirical_refutation.md`](notes/empirical_refutation.md) | Empirical refutation of the "EFE-satisfying" rule using SetReplace; cone dimension ≈ 1 on all 9 seeds. |

## Results

Every `results/<phase>/*.md` is a verdict file with triple-or-more-rail verification for a single claim.

| Document | Verdict |
|---|---|
| [`results/phase1_selfaudit/README.md`](results/phase1_selfaudit/README.md) | **PASSED.** Python rewriter matches SetReplace on events fired, state size, causal |V|, |E| (7/9 exactly; 2/9 off by ≤ 4 edges in scheduler tiebreakers). |
| [`results/phase1_selfaudit/setreplace_reference.md`](results/phase1_selfaudit/setreplace_reference.md) | Raw SetReplace output that the Python rewriter is audited against. |
| [`results/phase2_continuum/eq342_verdict.md`](results/phase2_continuum/eq342_verdict.md) | **✗ REFUTED.** Tube volume coefficient. Four rails agree: correct value on $S^2$ is 1/6, Gorard says 1/3 (off by 2); on $S^3$ correct is 1/3, Gorard says 2 (off by 6). |
| [`results/phase2_continuum/eq344_verdict.md`](results/phase2_continuum/eq344_verdict.md) | **✗ REFUTED.** Ollivier Wasserstein. Direct contradiction of the Ollivier 2009 theorem that Gorard cites: directional $\mathrm{Ric}(v,v)$ vs scalar $R$. |

## Scripts (reproducibility)

All scripts are runnable and reproducible; each lists its intended invocation at the top.

| Script | Purpose |
|---|---|
| [`scripts/run_seeds_v3.wl`](scripts/run_seeds_v3.wl) | SetReplace evolution of the named rule on 7 seeds (cycles, paths, figure-8). |
| [`scripts/causal_dimension.wl`](scripts/causal_dimension.wl) | Cone-dimension log-log fit for evolved causal graphs. |
| [`scripts/grid3d_test.wl`](scripts/grid3d_test.wl) | Named rule on 3×3×3, 4×4×4, 5×5×5 grid seeds. |
| [`scripts/test_eq342.wl`](scripts/test_eq342.wl) | Eq 342 verification on $S^2$ and $S^3$: exact area, Taylor series, Gorard's formula side-by-side. |
| [`scripts/python/rewriter.py`](scripts/python/rewriter.py) | Independent Python re-implementation of Gorard's named rule (no SetReplace, no Wolfram Language). |
| [`scripts/python/run_all_seeds.py`](scripts/python/run_all_seeds.py) | Runs Python rewriter on all 9 seeds and compares to SetReplace reference. |
| [`scripts/python/test_eq344.py`](scripts/python/test_eq344.py) | Best-effort MC estimation of $W_1$ on $S^2$ (noise-limited; see `eq344_verdict.md` for why structural refutation is preferred). |

## Lean formalization

Every Lean file has a doc comment describing its role. Built on Mathlib via Lake.

| File | Purpose |
|---|---|
| [`lean/lakefile.toml`](lean/lakefile.toml) | Lake project file (Mathlib 4.29.1 dependency). |
| [`lean/InfraFormalization.lean`](lean/InfraFormalization.lean) | Top-level module importing the submodules. |
| [`lean/InfraFormalization/Hypergraph.lean`](lean/InfraFormalization/Hypergraph.lean) | Directed (multi-)hyperedges and hypergraphs. |
| [`lean/InfraFormalization/Rule.lean`](lean/InfraFormalization/Rule.lean) | Rewriting rules with `IsConservative` predicate (`\|LHS\| = \|RHS\|`). |
| [`lean/InfraFormalization/Application.lean`](lean/InfraFormalization/Application.lean) | Rule applications with embedded-LHS invariant. |
| [`lean/InfraFormalization/Conservation.lean`](lean/InfraFormalization/Conservation.lean) | **Theorem A (proved, draft):** conservative rules preserve state size. |
| [`lean/InfraFormalization/GraphMetric.lean`](lean/InfraFormalization/GraphMetric.lean) | Graph distance + `ScaledHypergraph` for continuum-limit framing. |
| [`lean/InfraFormalization/Growth.lean`](lean/InfraFormalization/Growth.lean) | Ball/cone counting + linear-cone theorem (stated, proof pending). |
| [`lean/InfraFormalization/Limit.lean`](lean/InfraFormalization/Limit.lean) | Scaffolding for GH / spectral / measure-space convergence. |
| [`lean/InfraFormalization/Multiway.lean`](lean/InfraFormalization/Multiway.lean) | Abstract rewriting systems, confluence, local confluence. |
| [`lean/InfraFormalization/Causal.lean`](lean/InfraFormalization/Causal.lean) | Trajectories and causal-precedence relation. |
| [`lean/InfraFormalization/Branchial.lean`](lean/InfraFormalization/Branchial.lean) | Branchial relation + iterated reachability (`NStep`, `BranchialSlice`). First QM-bridge infrastructure. |
| [`lean/InfraFormalization/CausalLevel.lean`](lean/InfraFormalization/CausalLevel.lean) | Causal-DAG level function via well-founded recursion; `level_add_one_le_of_isCausalPred`, `no_causal_edge_within_level`, `same_level_ordered_antichain`. |
| [`lean/InfraFormalization/ParallelSchedule.lean`](lean/InfraFormalization/ParallelSchedule.lean) | Parallel-schedule scaffolding; `trajectory_preserves_size`, in/out-degree theorems. |
| [`lean/InfraFormalization/Demo.lean`](lean/InfraFormalization/Demo.lean) | End-to-end `edge_conservation` demo theorem. |
| [`lean/InfraFormalization/AxiomCheck.lean`](lean/InfraFormalization/AxiomCheck.lean) | `#print axioms` certification for every theorem in the repository. |
| [`lean/InfraFormalization/Infra/`](lean/InfraFormalization/Infra/) | Infrageometry theorems (continuum limits + Lorentzian structure). |
| [`lean/InfraFormalization/Infra/ScaledCycle.lean`](lean/InfraFormalization/Infra/ScaledCycle.lean) | Scaled n-cycle with `cycleDist` metric; triangle, symmetry, self-distance. |
| [`lean/InfraFormalization/Infra/LatticeDensity.lean`](lean/InfraFormalization/Infra/LatticeDensity.lean) | `latticeEmbed`, density in `[0, 1)`, `latticeEmbed_isometry`. |
| [`lean/InfraFormalization/Infra/Circle.lean`](lean/InfraFormalization/Infra/Circle.lean) | Circle-metric via fundamental-domain parameterisation. |
| [`lean/InfraFormalization/Infra/GHBound.lean`](lean/InfraFormalization/Infra/GHBound.lean) | `cycle_circle_gh_bound`: cycle GH-converges to circle at rate `1/(2n)`. |
| [`lean/InfraFormalization/Infra/ScaledPath.lean`](lean/InfraFormalization/Infra/ScaledPath.lean) | Path → interval GH bound. |
| [`lean/InfraFormalization/Infra/ScaledTorus.lean`](lean/InfraFormalization/Infra/ScaledTorus.lean) | 2D lattice → 2-torus GH bound. |
| [`lean/InfraFormalization/Infra/ScaledTorusD.lean`](lean/InfraFormalization/Infra/ScaledTorusD.lean) | **Generalised (d+1)D lattice → (d+1)-torus GH bound** for arbitrary `d ≥ 0`. |
| [`lean/InfraFormalization/Infra/GHApprox.lean`](lean/InfraFormalization/Infra/GHApprox.lean) | Abstract `GHApproximation` structure. |
| [`lean/InfraFormalization/Infra/OllivierStatement.lean`](lean/InfraFormalization/Infra/OllivierStatement.lean) | Correct Ollivier identity (statement-only) + Gorard mis-stated form + coincidence theorem. |
| [`lean/InfraFormalization/Infra/GrayTubeStatement.lean`](lean/InfraFormalization/Infra/GrayTubeStatement.lean) | Correct Gray tube formula (statement-only) + `gray_vs_gorard_disagree_on_S2/S3` disagreement proofs. |
| [`lean/InfraFormalization/Infra/LorentzLattice.lean`](lean/InfraFormalization/Infra/LorentzLattice.lean) | **Discrete Lorentzian lattice**: `CausalPrecedes`, trichotomy (timelike/spacelike), forward cones. |
| [`lean/InfraFormalization/Infra/TrajectoryLorentz.lean`](lean/InfraFormalization/Infra/TrajectoryLorentz.lean) | **Bridging theorem**: `trajectoryToEvent` embeds a trajectory's causal DAG into the 1+0-dim Lorentz lattice via the level function. |
| [`lean/InfraFormalization/Infra/TrajectoryLorentzD.lean`](lean/InfraFormalization/Infra/TrajectoryLorentzD.lean) | **d-dim conditional bridging**: `SpatialEmbedding`, `LightConeCompatible`, `fullEmbed_preserves_causal`. The F1 spatial-data slot made an explicit parameter. |
| [`lean/InfraFormalization/Infra/Minkowski.lean`](lean/InfraFormalization/Infra/Minkowski.lean) | Continuum Minkowski `ℝ^{1,d}` with L∞ spatial metric: `ContinuumCausalPrecedes`, Timelike/Null/Spacelike, signed interval, trichotomy. |
| [`lean/InfraFormalization/Infra/ScaledLorentz.lean`](lean/InfraFormalization/Infra/ScaledLorentz.lean) | Int-to-ℝ embedding `lorentzIntEmbed` with **exact** isometry (`continuumSpaceDist_eq_cast`) and **iff** causal/timelike preservation (`_preserves_causal_iff`, `_preserves_timelike_iff`). Scaled embedding `scaledLorentzEmbed n` with `1/(2n)`-density in `ℝ^{d+1}` (`scaledLorentzEmbed_dense`), exact scaling identity (`scaledLorentzEmbed_spaceDist_eq_cast`), and iff causal preservation (`_preserves_causal_iff`). |
| [`lean/InfraFormalization/Infra/FullBridge.lean`](lean/InfraFormalization/Infra/FullBridge.lean) | **End-to-end bridge**: `causallyPrecedes_gives_continuum` chains trajectory → Lorentz lattice → continuum Minkowski under `LightConeCompatible`. |
| [`lean/InfraFormalization/DiscreteCalculus.lean`](lean/InfraFormalization/DiscreteCalculus.lean) | **Rung 1 of the bridge ladder**: graph Laplacian, discrete inner product, linearity. |
| [`lean/InfraFormalization/DiscreteCalculusSymm.lean`](lean/InfraFormalization/DiscreteCalculusSymm.lean) | **Self-adjointness** `⟪Δ f, g⟫ = ⟪f, Δ g⟫` + Dirichlet form `⟪f, -Δ f⟫ = ½ ∑ (f(w) - f(v))²` + positive semidefiniteness of `-Δ` + `laplacian_sum_zero` (discrete divergence theorem). |
| [`lean/InfraFormalization/CycleGraph.lean`](lean/InfraFormalization/CycleGraph.lean) | Concrete cycle Laplacian on `Fin n`: second-difference form, linearity, cycle Dirichlet form. Prototype for Rung-2 convergence to `d²/dx²`. |
| [`lean/InfraFormalization/SecondDifference.lean`](lean/InfraFormalization/SecondDifference.lean) | Central second difference `Δ²_h f(x) := f(x+h) − 2 f(x) + f(x−h)`, exact polynomial identity (for any quadratic, equals `f''(x) · h²`), linearity, identification with the cycle Laplacian. |
| [`lean/InfraFormalization/CurvatureLocalCoord.lean`](lean/InfraFormalization/CurvatureLocalCoord.lean) | **Rung 5 (local-coord route)**: `MetricData n` (g, g⁻¹, ∂g + axioms), Christoffel symbols `Γ^ρ_{μν}` with lower-index symmetry, Minkowski instance with `Γ ≡ 0`. Foundation for Riemann/Ricci in coordinates without bundle machinery. |
| [`lean/InfraFormalization/CurvatureRiemann.lean`](lean/InfraFormalization/CurvatureRiemann.lean) | **Riemann tensor**, Ricci, scalar curvature, Einstein tensor — all as explicit local-coord formulas. `riemann_antisymm`, **`bianchi_first`** (algebraic Bianchi I), flat-connection vanishing theorems. **`minkowski4_satisfies_vacuum_EFE`**: `G_{μν} = 0` on Minkowski (the trivial flat-space sanity check). Everything Gorard wrote `g^{ab}, R, R_{μν}, G_{μν}, G_{μν} = 0` for, formalised. |
| [`lean/InfraFormalization/DiscreteRicci.lean`](lean/InfraFormalization/DiscreteRicci.lean) | **Hypergraph anchor for Rung 5.** Forman-Ricci curvature `Ric_F(v,w) := 4 − deg(v) − deg(w)` on edges, vertex-aggregation, total scalar. `formanRicciEdge_zero_of_two_regular`: 2-regular (e.g., cycle) graphs have zero Forman-Ricci everywhere — matches continuum Ricci of the circle (zero). |
| [`lean/InfraFormalization/RicciBridge.lean`](lean/InfraFormalization/RicciBridge.lean) | **First explicit discrete-Ricci ↔ continuum-Ricci bridge**: `circleMetric : MetricData 1`, `circle_ricci_zero`, `cycleForman_zero`, `forman_ricci_matches_continuum_on_cycle`, `forman_ricci_real_matches_continuum_on_cycle`. The continuum and discrete Ricci agree (both ≡ 0) on the cycle/circle pair — the prototype for the broader hypergraph→manifold curvature correspondence. |
| [`lean/InfraFormalization/LaplacianBridge.lean`](lean/InfraFormalization/LaplacianBridge.lean) | **Scaled discrete Laplacian ↔ continuum second derivative**: `scaledSecondDiff f n x := n² · Δ²_{1/n} f(x)` matches `f''(x)` exactly for any quadratic, at any scale `n ≥ 1` and any point. Independence-of-scale theorem makes the limit-free polynomial bridge explicit. |
| [`lean/InfraFormalization/HypergraphLaplacian.lean`](lean/InfraFormalization/HypergraphLaplacian.lean) | **Laplacian directly on `Hypergraph V`** (the actual Wolfram-model state type): `laplacianHyper H f v := ∑_{e ∈ H.edges} ∑_{w ∈ e.others v} (f(w) − f(v))`. Linearity (`_add`, `_smul`), vanishes on constants. Specialises to standard graph Laplacian for 2-vertex edges. The "Wolfram-model state IS a discrete-calculus domain" anchor. |
| [`lean/InfraFormalization/DiscreteDAlembertian.lean`](lean/InfraFormalization/DiscreteDAlembertian.lean) | **Discrete d'Alembertian on a trajectory's causal DAG (Benincasa–Dowker style)**. The Gorard-attempted-but-failed centerpiece. `openInterval`, `intervalSize`, `layer τ k i`, `discreteDAlembertian4` with BD's 4D coefficients `(1, -9, 16, -8)`. Linearity proved. **`discreteAction`** `S[φ] := ∑ φ · B[φ]` (Gorard's Eq 86 discrete analog) and **`discreteEL`** (the Euler-Lagrange equation). `BenincasaDowkerConjecture` recorded as an open `Prop` — the unproven load-bearing assumption in Gorard F6, now formally flagged. |
| [`lean/InfraFormalization/Rewriting.lean`](lean/InfraFormalization/Rewriting.lean) | Auxiliary rewriting machinery (older scaffold). |
| [`lean/InfraFormalization/Refutations/`](lean/InfraFormalization/Refutations/) | Formal Lean refutations of the major structural flaws. |
| [`lean/InfraFormalization/Refutations/F1NoMetric.lean`](lean/InfraFormalization/Refutations/F1NoMetric.lean) | **F1 refuted**: no canonical metric construction from hypergraph data alone. |
| [`lean/InfraFormalization/Refutations/F2Orthonormality.lean`](lean/InfraFormalization/Refutations/F2Orthonormality.lean) | **F2 refuted**: fiat orthonormality is non-canonical; multiple forms render the same pair orthonormal. |
| [`lean/InfraFormalization/Refutations/F3Tautology.lean`](lean/InfraFormalization/Refutations/F3Tautology.lean) | **F3 refuted**: "asymptotic dim preservation ⇒ Einstein equations" is `Iff.rfl`. |
| [`lean/InfraFormalization/Refutations/F4Tautology.lean`](lean/InfraFormalization/Refutations/F4Tautology.lean) | **F4 refuted**: "causal invariance ⇔ general covariance" is `Iff.rfl` (axiom-free). |
| [`lean/InfraFormalization/Refutations/F5Illdefined.lean`](lean/InfraFormalization/Refutations/F5Illdefined.lean) | **F5 refuted**: "discrete sum becomes integral" is under-determined without a convergence notion. |

## Primary sources (read-only)

The papers themselves are under [`papers/`](papers/) — PDFs plus extracted TeX for each. Not part of our authorship; included for reproducibility of line references.

| Directory | Paper |
|---|---|
| `papers/gorard_2004.14810.pdf` + `papers/tex_2004/` | G1 — Some Relativistic and Gravitational Properties |
| `papers/gorard_2011.12174.pdf` + `papers/tex_2011/` | G2 — Algorithmic Causal Sets and the Wolfram Model |
| `papers/gorard_2102.09363.pdf` + `papers/tex_2102/` | G3 — Hypergraph Discretization of the Cauchy Problem |
| `papers/gorard_2303.07282.pdf` + `papers/tex_2303/` | G4 — Non-Vacuum Solutions, Gravitational Collapse, Discrete Singularity Theorems |

## Suggested reading paths

**"I want the 5-minute verdict."**
1. [`README.md`](README.md) status table.
2. [`FINDINGS.md`](FINDINGS.md) one-line summaries.
3. [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) S1–S6 gallery.

**"I want to check the math myself."**
1. [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) to pick which error you want to scrutinize.
2. The corresponding [`results/phase2_continuum/*.md`](results/phase2_continuum/) or [`results/phase1_selfaudit/*.md`](results/phase1_selfaudit/) verdict file.
3. The corresponding script under [`scripts/`](scripts/). Re-run.

**"I want to see if Gorard's original paper is as bad as claimed."**
1. [`notes/claims_catalog.md`](notes/claims_catalog.md) — per-equation verdict for all of 2004.14810.
2. [`notes/2004.14810_close_reading.md`](notes/2004.14810_close_reading.md) — prose discussion of §3.
3. [`notes/corpus_audit.md`](notes/corpus_audit.md) — cross-paper propagation.

**"I want to contribute a Lean proof."**
1. [`README.md`](README.md) layout section for Lean.
2. [`lean/InfraFormalization.lean`](lean/InfraFormalization.lean) and its submodules.
3. [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) §6 for the six items a honest formalization would require.

**"I want to understand the single-way vs multi-way issue."**
1. [`notes/singleway_vs_multiway.md`](notes/singleway_vs_multiway.md) top to bottom.
2. Appendix about the null tetrad in the same file.

**"I want to know which claims are established."**
1. [`notes/severity_taxonomy.md`](notes/severity_taxonomy.md) — "How the errors recur" section.
2. [`notes/claim_assessment.md`](notes/claim_assessment.md) — "The honest verdict" section.
