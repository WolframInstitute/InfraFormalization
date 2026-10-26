# Roadmap: sequencing toward a binary black hole merger from a hypergraph

Target: a Lean theorem that a hypergraph initial condition, evolved under a Wolfram-model rule, converges to a binary black hole merger spacetime, with the extracted waveform converging to the numerical-relativity waveform. The initial hypergraph is not sampled from the target manifold (G3 samples its initial data from the Brill-Lindquist geometry, READ, G3 lines 6148-6152 and 6179).

This document orders the open tasks into phases by dependency. The critical-path tasks of a phase depend on the previous phase. Parallel streams do not gate the critical path.

Status labels follow `STATUS_OF_GORARD_CLAIMS.md`: PROVED, PROVED-WITH-NATIVE-DECIDE, MEASURED, READ, OPEN.

---

## Phase A: convergence statements with content

Phase A consists of convergence statements for a trajectory and a target metric that are false for some target. The library has no such statement.

| # | Task | Deps | Status |
|---|---|---|---|
| 233 | A metric-origin statement for a hypergraph trajectory that is false for some target metric | #234 | OPEN. Lean: none |
| — | A convergence-rate statement for a discrepancy computed from the trajectory, with rate functions 1/n, 1/n² and cⁿ | #233 | OPEN. Lean: none |
| 234 | A discrepancy computed from the counting measure of the n-th state of the subdivision trajectory | — | OPEN. Lean: none |
| — | Define, for a trajectory τ and a target metric g, the discrepancy d_τ,g(n) as the Wasserstein-1 distance between the pushforward of the counting measure of the n-th state and the volume measure of g, and prove d_τ,g(n) ≤ C/n for one flat target and one rule | measure of a trajectory | OPEN |

Phase A gives Phase B screener metrics a target statement to test against.

---

## Phase B: rule-search infrastructure

Lean metric definitions, a trajectory interchange format, and the driver for wolframscript and the C++ engine.

| # | Task | Deps | Status |
|---|---|---|---|
| 224 | Curvature signature screener on abstract trajectories (Forman-Ricci trajectory, deviation from a target, angular and combined screeners) | — | OPEN. Lean: none. `RuleSignature.lean` defines the edge-count, vertex-count and ball-volume signature of a hypergraph with screening lemmas (PROVED) |
| 372, 377 | `RuleSignatureSchema.lean`: dossier format, `canonicalDossier_isConsistent`, `consistent_dossier_eq_canonical` | #224 | PROVED |
| 384-386 | Screening and bounded search on the executable engine (`RuleSignatureExecMetrics.lean`, `RuleSignatureExecSearch.lean`) | #224 | PROVED-WITH-NATIVE-DECIDE |
| 190 | Rule search via wolframscript at scale | #224, schema | OPEN |
| 227 | Per-edge-instance match enumeration in `MultiwayExec` | — | OPEN |
| 228 | Causal edge tracking in `MultiwayExec` | #227 | `CausalEventTrace.lean` relates events through hyperedge values. `CausalHistory.lean` defines the causal graph on hyperedge identities. An engine trace with identities is OPEN |
| 229 | Branchial edge tracking in `MultiwayExec` | #227 | OPEN. The relation of `BranchialEventTrace` is same-step consumed-edge contention, not the Wolfram-model branchial graph |
| 230 | State canonicalisation up to isomorphism | #227 | OPEN |

Engine semantics. `MultiwayExec.singleWayStep` applies a maximal set of edge-disjoint matches, chosen greedily in enumeration order. `MultiwayExec.fireAllStep` applies every match, including matches that share edges, and is not a Wolfram model update when matches overlap. Modules that state results with `fireAllStep` are listed in `STATUS_OF_GORARD_CLAIMS.md` (Execution engine).

Phase B gives a check, for a rule R from a corpus, of whether R's trajectory meets a target statement from Phase A.

---

## Phase C: curved targets

Prove a convergence statement from Phase A for one curved 4D Lorentzian metric and one rule.

| # | Task | Deps |
|---|---|---|
| R4 | Convergence of a scaled discrete Ricci curvature to a nonzero continuum Ricci curvature | #224 |
| 218 | Per-metric proof or disproof of Ricci convergence | R4 |
| 217 | Curvature tensors of the named GR metrics in the project's local-coordinate library | — |
| 220 | Ollivier-Ricci convergence on a concrete discretisation | R4 |
| 225 | Convergence statement for the multiway causal graph | #231, Phase B |
| 235 | Each Lean module tied to `ExecHG`, the multiway system or `Hypergraph V` | #231 |
| 236 | A rule and a proof for one curved-target statement | Phase A, Phase B, R4 |
| 213 | Lorentzian Gromov-Hausdorff distance (Noldus, Suhr) | — |
| E6 | Lorentzian Gromov-Hausdorff on causal graphs | #213 |
| E7 | Convergence of a discrete causal DAG to a continuum Lorentzian manifold | #213, E6 |
| 222 | Pointed and metric-measure Gromov-Hausdorff | — |
| 221 | PDE convergence of solutions, beyond eigenvalues | — |
| 219 | Discrete Hamiltonian and momentum constraint residuals | E5 |
| H4 | Scaled trajectory converges to a continuum manifold | Phase B |
| H5 | Ricci bridges for curved targets | R4, #218 |

Phase C ends with one GR metric that has a rule, a trajectory and a convergence proof.

---

## Phase D: binary black hole merger

| # | Task | Deps |
|---|---|---|
| D11 | Cauchy problem for the Einstein equations (Choquet-Bruhat) | E5, Phase C |
| KN1 | Wave equation solution u(t) = cos(Dt) u₀ + t·sinc(Dt) v₀ | d² = 0 (PROVED) |
| KN2 | Discrete-time wave step and unitary wave propagator | KN1 |
| H6 | Binary black hole initial data as a hypergraph | Phase C, KN1, KN2 |
| H7 | Evolution of that data under the Phase C rule | H6, #236 |
| H8 | Discrete Ψ₄ extraction compared with numerical-relativity waveforms | H7 |
| H9 | Convergence to the merger spacetime | H8, Phase C |

Target statement (OPEN): `∃ rule R, hypergraph_IC : ExecHG ℕ, NRwaveform : ℝ → ℂ, discreteWaveform R IC tendsto NRwaveform`, where `discreteWaveform` is computed from the evolution of `hypergraph_IC` under R.

H6-H9 have no Lean statement. `twoTriangleSeed` (`TwoTriangleSeed.lean`) is a 6-vertex graph of two triangles joined by an edge. It is not binary black hole initial data.

---

## Parallel streams

### Knill theorems (KN)

- KN3: Wu inclusion-exclusion `wuCharacteristic₂_eq_chi_sq_sub_disjoint`. PROVED. Wu cohomology and the fusion inequality are OPEN.
- KN8: Euler-Poincaré f-vector identity `eulerCharacteristic_eq_alt_sum_kSkeleton`. PROVED. The zeta functions are OPEN.
- KN14: McKean-Singer supersymmetry. Needs dimension-graded form spaces. OPEN.
- KN16: Cartan formula L_X = i_X d + d i_X. Needs vector fields and interior products. OPEN.
- KN18: Brouwer-Lefschetz fixed-point theorem. Needs hypergraph endomorphisms and the Lefschetz number. OPEN.
- KN15: Atiyah-Singer and Atiyah-Bott analogues. OPEN.
- KN4, KN5, KN6, KN7, KN9-KN13, KN17, KN19, KN20. OPEN.

### Synthetic geometry (SIG)

- SIG3: Tarski `Between` and `Cong` as definitions on `Hypergraph.dist`, with the axioms T1-T8 as decidable Props on finite hypergraphs. OPEN.
- SIG2: Tarski and Hilbert axioms as Props, decided per class (path, lattice, branching). OPEN.
- SIG1: constructions `Line`, `Ray`, `Segment`, `Perpendicular`, `Parallel`. OPEN.
- SIG4: coordinates from shortest-path counts or a Cayley embedding. OPEN.
- SIG5: stability of branching constructions under refinement. OPEN.

### Engine and abstract rewriting

- #231 extension: an `Application` built from an executable match, and the correspondence between `singleWayStep` and `MultiStep`. OPEN.
- #267: `singleWayStep subdivisionSys H = subdivideAll H (nextFresh H)` for every path-shaped H. The single-edge case `singleWayStep_subdivisionSys_consEdge_of_ne` (any a ≠ b) is PROVED. The closed form `singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)` is PROVED for n ≤ 2 by `decide` and PROVED-WITH-NATIVE-DECIDE for n = 3, 4, 5. The statement for every path-shaped H is OPEN.
- #268: existential preservation of path shape (Route C). OPEN.

### Infrastructure (T)

- T5: closed forms of the path and d-torus Laplacian spectra. The path eigenvalue at k = 0 is PROVED. General k is OPEN.
- #214: Wasserstein-1 distance. Pseudometric axioms and the Lipschitz bound are PROVED. The convergence rate of the scaled counting measure is OPEN.
- #215: Wasserstein-1 rate O(1/n) on the d-torus. OPEN.
- #216: replace every statement deferred to future Mathlib with a project proof or an OPEN statement.

### Knill paclet port (IGE)

- #273: super-trace, pseudo-determinant, super-determinant. `superTrace_diag_one` is PROVED. The determinants are OPEN.
- #274: Betti vector and Lefschetz number from the Hodge blocks. OPEN.
- IGE2: simplicial sets (face and degeneracy maps, delta-complex morphisms). OPEN.
- IGE3: Vietoris-Rips, Čech and persistence on hypergraphs. OPEN.
- IGE4: mesh primitives. OPEN.
- IGE5: formal chain complex. OPEN.

### P-track

P1-P20 in `NEXT_STEPS.md` are open: P3 (Chern-Simons), P4 (ribbon graphs), P5 (sheaves), P6 (Koszul signs), P7 (homotopy colimit), P9 (action principle), P11 (interaction diagrams), P14 (blowup rules and renormalisation), P19 (1-skeleton and clique complex), and others.

### M-track (collaborators)

- M1: IMILEA gauge-intern coordination.
- M3: HKOLCZ Lie-Poisson MBQC.
- M4: JPULLMAN IBL-∞ and BV formalism.
- M6: NMURZIN `Infrageometry` paclet, Lean port parity (see `CONTRIBUTORS.md`).
- M7: SAHMED EME-tracking community post.
- M8: diffusion-geometry bridge, attribution under review (see `CONTRIBUTORS.md`).
- M9: tropical-geometry synthetic infrageometry.
- M10: three-body problem and dimension signatures.

### Named GR metrics (B)

- B2: Schwarzschild Riemann tensor components. OPEN.
- B3: Schwarzschild Ricci tensor equal to 0 on the exterior. OPEN.
- B4: Schwarzschild satisfies the vacuum Einstein equations on the exterior. No theorem exists. OPEN.
- B10: symmetry of the Ricci tensor of the Levi-Civita connection for every `MetricDataC2`. PROVED for `warpedDiag2`. OPEN in general.
- B11: second Bianchi identity ∇_μ G^{μν} = 0 for the Levi-Civita connection. OPEN. The Einstein tensor is 0 for the flat connection (`flatConnection_einstein_zero`) and for `warpedDiag2` (`warpedDiag2_einsteinTensor_zero`), both PROVED.
- C5: existence and uniqueness of the Levi-Civita connection (Koszul). OPEN.
- C8: a scaled discrete connection converges to the Levi-Civita connection. OPEN.
- F4: Schwarzschild as an explicit vacuum solution. OPEN.
- F6: Kerr as a vacuum solution. OPEN.

### Continuum field limits (G)

- G5: continuum limits of discrete fields. OPEN.
- G6: HepLean integration. OPEN.

### Branchial and quantum (I, IQ)

- I8: Hilbert-space continuum limit of branchial slices. OPEN.
- IQ8: EME persistence as a branchial observable. OPEN. Lean: none.
- IQ9: path integral over single-way causal graphs. OPEN. Lean: none.

### Causal and Lorentzian (E)

- E5: foliation existence is PROVED (`stablyCausal_hasFoliation`). The lapse-shift decomposition is OPEN.

### Heat and spectra (D, A, ID)

- D6: convergence of every heat solution on the cycle to its mean. Decay of finitely many nonconstant modes is PROVED (`heatKernel_cycleHypergraph_multi_mode_tendsto`). The eigenbasis decomposition of arbitrary initial data is OPEN.
- A6: weak convergence of the scaled counting measure to Lebesgue measure on [0,1). PROVED for polynomials of degree at most 3 (`A6Holds_poly_deg3`). The continuous case is OPEN.
- A7: Wasserstein-1 rate O(1/n) for the scaled counting measure. OPEN.
- A8: measure convergence on the d-torus. OPEN.
- ID7: spectral dimension from the heat-kernel trace. OPEN.

### Multiway engine

- J2: path integral over causal graphs. OPEN.
- J3: emergent gravity (Jacobson, Verlinde). OPEN.
- J5: comparison with LQG spin foams. OPEN.
- J6: AdS/CFT analogue in the Wolfram model. OPEN.

### Papers (K)

- K1: P1 audit paper.
- K2: P2 corrected identities.
- K3: P3 continuum-limit templates.
- K4: P4 structural library.
- K5: P5 Wolfram-to-GR rule.
- K6: P6 branchial QM audit and formalisation.
- K7: P7 binary black hole paper, after K5.
- K8: P8 discrete d'Alembertian.
- K9: P9 analysis of the G1 derivation.

### Angles and topology (AT, PATH, POLY, CELL, TOP, KNOT)

Definitions in place: `Hypergraph.elementaryAngle`, `cosAngle`, `angle`, `IsOrthoApprox` (AT0, AT1, AT6), `Hypergraph.scalarCurvatureAt` (AT9, scalar curvature from the ball-volume ratio), `spatialB0` and `firstBettiZ` with lower bounds (TOP4, TOP1), `infraSphere` and `infraDisk` (SPHERE1), `perpBisector`, `closerHalf`, `midpoint`, `nearMidpoint` and `voronoiCell` (HYPER2, HYPER3, MIDPT1). PROVED (definitions with lemmas).

Open tasks in this stream (task numbers #285-#342):

- angle definitions AT2-AT27 and AT-W (sheaf angle), and the angular and combined screeners AT7;
- paths PATH1, PATH2;
- polygons POLY1 (polygon with arbitrary intersection sequence), POLY2 (cellular k-chains with sheaf coefficients), POLY3 (spin networks);
- cellular sheaves CELL1;
- contractibility CONTRACT1 (scale-indexed, through the Vietoris-Rips complex);
- path moves DEFORM1, DEFORM2;
- homotopy HOM1 (path homotopy), HOM2 (fundamental groupoid);
- invariants TOP2 (higher Betti numbers), TOP3 (fundamental group), TOP5 (higher homotopy groups), TOP6 (genus);
- knots KNOT1 (linking number), KNOT2 (Massey products), KNOT3 (Yamada and Jones polynomials).

---

## Critical path

```
Phase A (statements that depend on the trajectory and the target)
   ↓
Phase B (#190, #227-#230, screeners)
   ↓
Phase C (R4, #218, #217, #225, #235, #236, Lorentzian GH)
   ↓
Phase D (D11, KN1, KN2, H6, H7, H8, H9)
   ↓
Target theorem; papers K5 and K7.
```

Current state: Phase A has no Lean statement and is OPEN. The bounded search of `RuleSignatureExecSearch.lean` exists (PROVED-WITH-NATIVE-DECIDE for the search counts). The next Phase B task is #190.
