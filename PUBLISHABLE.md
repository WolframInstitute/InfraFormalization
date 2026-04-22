# Publishable outputs — target list

Working list of concrete publishable units the infrageometry programme is heading toward. Each is a real paper or technical note with an identifiable audience; each names the sufficient condition on our work for the paper to be ready.

Grouped from most-immediate (parts already done) to most-ambitious.

## P1 — Audit and formal refutation of the Gorard corpus

**One-line pitch.** A machine-checked audit of arXiv:2004.14810, 2011.12174, 2102.09363, 2303.07282 showing that the central claim — that general relativity has been derived from Wolfram-model hypergraph rewriting — has not been established. Each specific error and structural flaw is documented at citation-precision and **formally refuted in Lean**.

**Status.** Ready *now* as a v1 arXiv preprint.

**Sufficient conditions.**
- [x] S1/S2/S6 error taxonomy with TeX line references
- [x] F1–F5 structural flaws **formally refuted in Lean** (`Refutations/F1-F5*.lean`), all axiom-clean
- [x] Corpus-wide cross-paper propagation map
- [x] Continuum-limit claims catalog
- [x] Line-by-line close readings of all four Gorard papers
- [x] Edge conservation proved in Lean (underpins F7 refutation)
- [x] Named rule empirically refuted (SetReplace + independent Python rewriter)
- [ ] A short (≤ 15 page) technical-comment-style PDF
- [ ] External review by Wolfram Institute colleagues

**Audience.** *Complex Systems* (published G1, G2); arXiv math-ph + gr-qc cross-listing.

**Load-bearing Lean theorems:**
- F1: `Refutations.F1NoMetric.hypergraph_does_not_determine_metric`
- F2: `Refutations.F2Orthonormality.orthonormality_depends_on_form`
- F3: `Refutations.F3Tautology.gorard_dim_preservation_is_euler_lagrange` (Iff.rfl)
- F4: `Refutations.F4Tautology.gorard_causal_invariance_is_general_covariance` (axiom-free)
- F5: `Refutations.F5Illdefined.becomes_is_underdetermined`
- F6: `DiscreteDAlembertian.BenincasaDowkerConjecture` (explicit unproven-load-bearing flag)
- F7: `Application.size_result_of_conservative`

## P2 — Corrected continuum identities formalised

**One-line pitch.** The correct versions of the Ollivier–Ricci identity and the Gray tube formula, expressed as Lean definitions, with their disagreement with Gorard's forms machine-verified at concrete test manifolds.

**Status.** Statement-level formalisation complete; proofs of the correct identities pending Mathlib's Riemannian + optimal-transport infrastructure.

**Sufficient conditions.**
- [x] `OllivierStatement.OllivierIdentityLeading` + `GorardMisstatedForm` + coincidence theorem
- [x] `GrayTubeStatement.GrayTubeLeading` + `gray_vs_gorard_disagree_on_S2/S3`
- [ ] Full proofs of the correct identities (Mathlib Ricci/Wasserstein dependency)

**Audience.** arXiv math.DG + math-ph.

## P3 — Infrageometry continuum-limit templates (cycle, path, torus, Lorentz)

**One-line pitch.** A Lean library of discrete-to-continuum Gromov-Hausdorff bounds: cycle → circle, path → interval, (d+1)-lattice → (d+1)-torus, and int-lattice → Minkowski. Unified under a common `GHApproximation` structure.

**Status.** Complete up to flat-space targets; curved-target extensions await Mathlib Ricci.

**Sufficient conditions.**
- [x] `cycle_circle_gh_bound`
- [x] `path_interval_gh_bound`
- [x] `torus_gh_bound` (2D) and `dTorus_gh_bound` (arbitrary d)
- [x] `lorentzIntEmbed_preserves_causal_iff` (exact Minkowski causal correspondence)
- [x] `scaledLorentzEmbed_dense` + `_spaceDist_eq_cast` (scaled isometry + density)
- [x] **Rung-2 spectral core**: `CTwoTaylor.scaledSecondDiff_tendsto_iteratedDeriv` (general C² convergence), `ScaledDiffC2Bridge.scaledSecondDiff_tendsto_iteratedDeriv_C2` + `hypergraph_scaled_laplacian_eq_scaledSecondDiff` (end-to-end hypergraph → f'' for all C²).
- [x] **Cycle spectrum closed form**: `CycleSpectrum.cycleLaplacian_eigen` (eigenvalues `−4 sin²(πk/n)` + eigenvectors `cos(2πkj/n)`, full wrap-around).
- [x] **Eigenvalue convergence**: `CycleEigenLimit.cycleEigenvalue_scaled_tendsto` (n² · λ_k → −(2πk)², continuum circle spectrum).
- [x] **Matrix bridge**: `LaplacianMatrix.laplacianMatrix_mulVec = laplacianHyper` and `heatKernel H t := exp(t · Δ)` (`heatKernel_add` semigroup, `heatTrace`, symmetric matrix).
- [x] **ODE ↔ matrix heat kernel unified** (T1, `HeatKernelODE.lean`): `heatKernel_isHeatSolution` — the matrix kernel satisfies the `HeatSolution H` ODE predicate. Heat existence + forward uniqueness (D2) follows.
- [x] **Matrix-level conservation laws**: `heatKernel_mulVec_const`, `heatKernel_mass_conservation`, `heatKernel_L2_decay`, `heatKernel_mulVec_add`.
- [x] **Matrix exp fixes eigenvectors** (T2): `exp_mulVec_of_eigenvector`. Opens Mathlib `Module.End.HasEigenvalue` form of cycle spectrum (T4).
- [x] **Counting-measure + pushforward** on Hypergraph V (A5, `HypergraphMeasure.lean`): foundation for A6 (weak convergence) and A7 (Wasserstein rate).
- [x] **`Hypergraph.dist` triangle inequality + cycle connectivity** (T3).
- [ ] 25-page paper with the Lean library as appendix

**Audience.** arXiv math.MG + math-ph + formal-methods.

## P4 — Wolfram-model structural theorems library

**One-line pitch.** A Lean library of structural theorems about hypergraph rewriting — edge conservation, degree sums, causal-DAG level monotonicity, same-level antichain, hypergraph calculus — all axiom-clean.

**Status.** Substantially more than earlier. 200+ theorems across the Lean corpus, all axiom-clean.

**Sufficient conditions.**
- [x] Edge conservation, degree sums, balance
- [x] Level monotonicity + same-level antichain (forward)
- [x] **Hypergraph Laplacian** + self-adjointness + Dirichlet form + PSD + divergence theorem
- [x] **Hypergraph Laplacian as matrix** (`laplacianMatrix H`) + matrix symmetry + row-sum zero + heat kernel via `Matrix.exp` (semigroup, `heatTrace`)
- [x] **Forman-Ricci** (simple + hypergraph) + cycle=0 bridge
- [x] **Cycle Laplacian = central second difference** (interior-point identification)
- [x] **Scaled-second-difference = f''** for all C² (`CTwoTaylor.lean` + `ScaledDiffC2Bridge.lean`; beyond polynomials)
- [x] **Cycle spectrum closed form** + scaled eigenvalue → continuum circle spectrum (`CycleSpectrum.lean`, `CycleEigenLimit.lean`)
- [x] **Discrete PDE ladder**: heat equation (mass conservation + L² decay), wave equation (energy conservation), Klein-Gordon, Schrödinger (unitarity), scalar field (Lagrangian + Euler-Lagrange ↔ KG)
- [x] **Discrete exterior calculus**: `HypergraphCalculus.lean` with discrete Stokes (summation by parts), `DeRham.lean` (d² = 0), `FormCochainIntegration.lean`
- [x] **Infrageometry program** (9 groups, 57 tasks): IA full, IG 10/11, IC full, IT 3+3 obligation, ID 5+2 obligation, IB 5/6, IS full, IR 6+1 obligation
- [x] Hypergraph distance + geodesic ball + Wolfram-Hausdorff dimension (`HypergraphDistance.lean`)
- [x] Benincasa-Dowker discrete d'Alembertian + action + EL equation
- [x] State-size invariant under conservative trajectory (`trajectory_size_invariant`)
- [ ] Trajectory-structure lemma (consumed expressions ≤ earlier produced)
- [ ] Full parallel-layer bound `|layer_s| ≤ N/k`
- [ ] 25-page paper

**Audience.** arXiv cs.LO + math.CO + formal-methods.

## P5 — First provable Wolfram-to-GR bridge

**One-line pitch.** A rewriting rule whose evolution is proved to converge in Gromov–Hausdorff sense to a specific Lorentzian manifold; with discrete curvature on the causal graph converging to the continuum Ricci. The first such rigorous result.

**Status.** **Open research problem** (candidate rule). But substantial infrastructure in place.

**Sufficient conditions.**
- [x] `Infra/LorentzLattice.lean` + `Infra/Minkowski.lean` + `Infra/FullBridge.lean` — discrete causal-graph ↔ continuum Minkowski, exact isometry + bridge theorems.
- [x] **`DiscreteDAlembertian`** — Benincasa-Dowker operator on trajectories, `discreteAction`, `discreteEL`. The Gorard-attempted-but-failed operator, now formalised.
- [x] **`BenincasaDowkerConjecture`** explicitly flagged as an open `Prop`-level hypothesis.
- [x] **Forman-Ricci → continuum Ricci** bridge on the cycle/circle (`RicciBridge.lean`) — first discrete-to-continuum curvature match.
- [x] **`leviCivitaConnection : MetricDataC2 → ConnectionData`** — full local-coord curvature derivation.
- [x] **Schwarzschild — all 8 Christoffel components** in the exterior (`Schwarzschild.lean`, B1 complete #20).
- [x] **Cycle spectrum → continuum circle spectrum** (`CycleSpectrum.lean` + `CycleEigenLimit.lean`): first concrete hypergraph-Laplacian → continuum-Laplacian spectral convergence.
- [x] **EPS axioms + Marzke-Wheeler clock** (`EPSAxioms.lean`, `MarzkeWheeler.lean`; IC7/IC8): operational reconstruction of Lorentzian geometry from hypergraph-level light rays and observers.
- [x] **Spatial reconstruction + causal foliation + proper time** (IC4/IC5).
- [x] **Candidate rule database + screening pipeline** (`CandidateRuleDatabase.lean`; IR6).
- [x] **Conservation ⇒ bounded dimension** structural theorem (`RuleDimensionBounds.lean`; IR2).
- [ ] At least one candidate rule identified (or engineered).
- [ ] Convergence theorem for that rule.

**Audience.** arXiv gr-qc + math-ph (*Physical Review D* / *Classical and Quantum Gravity* / *Foundations of Physics*). This would be the headline result.

## P6 — Branchial quantum mechanics audit + formalisation

**One-line pitch.** Gorard's claim that branchial structure recovers quantum mechanics, audited with the same methodology as P1, with corrected and formalised versions in Lean where the claim survives.

**Status.** Partial infrastructure.

**Sufficient conditions.**
- [x] `Branchial.lean` — `BranchialRelated`, `NStep`, `BranchialSlice`. Basic structure.
- [x] `BranchialFinite.lean` (I1 #84) — `branchialSliceFinite_of_successors_finite` (finite-dim groundwork).
- [x] `FisherMetric.lean` (IQ5 #152) — Fisher metric on branchial distributions.
- [x] `SchrodingerEquation.lean` (D10) — discrete Schrödinger on `Hypergraph V` with proven unitarity / probability conservation.
- [x] Formal `∧ False` obligations for IQ6 (Fubini-Study limit), IQ8 (EME persistence), IQ9 (path integral) in `RemainingObligations.lean` — no silent assumptions.
- [ ] Complete S1–S6 audit of Gorard's QM paper (arXiv:2004.14808).
- [x] Branchial measure: uniform probability on finite slices (I2 #85; `BranchialHilbert.lean` — `branchialUniformWeight` summing to 1 when nonempty).
- [x] `ℓ²(slice)` Hilbert space (I4 #87 / R3 #178 partial; `BranchialHilbert.lean` — ℂ-Hilbert alias, ℂ-linear adjacency operator `branchialAdjLM`, self-adjointness for symmetric adjacency).
- [~] Branchial amplitudes + evolution as unitary (I3 ✅, I5/I8 pending). `BranchialHilbert.lean` defines `BranchialAmplitude` + Born rule; unitary evolution `exp(i·t·A)` remains for I5.
- [ ] Fubini-Study limit under branchial refinement (IQ6 #153 in progress; currently obligation).
- [ ] Prove (or disprove) the branchial → QM bridge claim.

**Audience.** arXiv quant-ph + math-ph.

## P7 — Binary-black-hole merger via hypergraph rewriting

**One-line pitch.** Hypergraph-level BBH initial data, evolved under an established Wolfram-to-GR rule (from P5), with proved convergence to the merger spacetime.

**Status.** **Depends on P5.** The scientific prize advertised (but not delivered) in G3.

**Sufficient conditions.**
- [ ] P5 completed
- [ ] Discrete Brill–Lindquist initial data on a hypergraph
- [ ] Evolution under the P5 rule
- [ ] Discrete Ψ₄ extraction matching BBH waveforms
- [ ] Lorentzian-GH convergence to a merger spacetime

**Audience.** Same as P5.

## P8 — Formalised discrete d'Alembertian + Benincasa-Dowker conjecture flag

**One-line pitch.** A Lean formalisation of the Benincasa-Dowker discrete d'Alembertian on a Wolfram-model trajectory's causal DAG, with the continuum-limit `B_ρ → □ − ½R` explicitly recorded as an open `Prop`-level conjecture. This closes the F6 "Gorard's circular EFE derivation" gap on the discrete side: the operator is fully defined, its linearity is proved, and the unproven load-bearing claim is machine-flagged.

**Status.** Core done (`DiscreteDAlembertian.lean`). Ready as a short technical note.

**Sufficient conditions.**
- [x] `openInterval`, `intervalSize`, `layer τ k i`, `discreteDAlembertian4` defined and proved linear.
- [x] `discreteAction` (Gorard Eq 86 analog), `discreteEL` (EL equation).
- [x] `BenincasaDowkerConjecture` structure; `gorardF6_carries_BD_assumption`.
- [x] `layer_disjoint`, `mem_layer_isCausalPred` structural lemmas.
- [ ] General-dimension `discreteDAlembertian_d` (coefficients indexed by `d`).
- [ ] 10-page note with motivations + connection to F6 + BD literature review.

**Audience.** arXiv gr-qc + hep-th (*Classical and Quantum Gravity* as a Letter).

## P9 — Machine-checked refutation of Gorard's EFE derivation chain

**One-line pitch.** A self-contained paper walking through Gorard's prose derivation of the Einstein field equations from Wolfram-model dynamics, showing at each step which move is tautological (F3, F4), ill-defined (F5), circular (F6), or unsupported (F1, F2). Every refutation is a cited Lean theorem.

**Status.** All pieces formalised; drafting ready to begin.

**Sufficient conditions.**
- [x] F1 refuted: `hypergraph_does_not_determine_metric`.
- [x] F2 refuted: `orthonormality_depends_on_form`.
- [x] F3 refuted: `gorard_dim_preservation_is_euler_lagrange` (Iff.rfl).
- [x] F4 refuted: `gorard_causal_invariance_is_general_covariance` (axiom-free).
- [x] F5 refuted: `becomes_is_underdetermined`.
- [x] F6 flagged: `BenincasaDowkerConjecture`.
- [x] Positive construction (hypergraph anchor) exists for each "what Gorard should have formalised" move.
- [ ] 15-page paper draft

**Audience.** arXiv gr-qc + cs.LO. This is the direct counter-paper.

## Dependencies and ordering

```
P1 (audit) ──────────────────┐
P2 (correct identities) ─────┤
P3 (continuum templates) ────┤
P4 (structural library) ─────┤
P8 (discrete d'Alembertian) ─┤
P9 (refutation chain) ───────┘
                             │
                             ▼
                            P5 (Wolfram → GR)
                           /       \
                          ▼         ▼
                         P7 (BBH)   P6 (QM branchial)
```

P1–P4, P8, P9 are independent; most content exists. P5 is the research gate for the physics prize; P7 depends on P5; P6 is orthogonal but necessary for quantum gravity.

## Conventions and process

- Every paper target names at least one Lean theorem it cites. Papers are **proof-assistant-backed**.
- Each paper's draft PDF lives under `reports/`.
- *No paper leaves the lab without passing internal review.*
- The project exists to correct overclaim in Wolfram physics; we do not add to it.
