# Infrageometry — research program and Lean coverage map

## 1. What Infrageometry is

**Infrageometry** is the study of the intrinsic geometry of hypergraphs arising in hypergraph rewriting. It is the backbone of the Wolfram Physics Project interpreted as *reconstruction* (the inverse of discretization): a small hypergraph is consistent with many continuum geometries; rewriting progressively refines which one. Smooth structure is expected only in the thermolimit of many updates.

Strategic contrasts:

- In contrast to the "the hypergraph determines the metric" framing (Gorard corpus): infrageometry explicitly *refuses* uniqueness. "Small graphs support multiple geometries." Scale-dependent phenomena are the rule, not the exception.
- Against diffusion geometry: that program is probabilistic, infrageometry is exact computational; complementary, not competing.
- Against causal-set theory: inherits sprinkling language and the BD action but treats the discrete substrate as the fundamental object rather than a sampled image of a Lorentzian manifold.
- Against lattice gauge theory: operates at the *infra*-scale (no labels, just combinatorics); mesoscale labeled graphs are the coarse-graining target for RG flow into LGT.

## 2. Named subprojects of the program

| Program | Scope | Status in colleagues' work | Our Lean coverage |
|---|---|---|---|
| **Synthetic Infrageometry** | Axiomatic construction of lines, circles, subspaces, spheres on hypergraphs (Euclid-style). `InfrageometricScene` handles multi-constructions. Hausdorff distance on branchial graph of construction instances. | Implementation in Wolfram paclet; extremal orthogonal axes; coordinatization via intersection of spheres (dual to intersection of lines). | None yet. Task group S below. |
| **Infracausality** | Axiomatic special relativity from causal graphs. Observer chains, light rays, spatial-reconstruction hypergraph, Cauchy foliations, Ehlers–Pirani–Schild axioms, Marzke–Wheeler clocks. | "Axiomatic Relativity from Causal Graphs" paper in progress; EPS identified as the most discrete-compatible scheme. | Partial — `Causal.lean`, `CausalLevel.lean`, `Infra/LorentzLattice`, `Infra/TrajectoryLorentz`, `Infra/ScaledLorentz`. No EPS axiomatization yet. Task group IC. |
| **InfraGaugeTheory** | Fibered graphs, sections, connections, parallel transport, Wilson loops, holonomy, moduli of connections, quantum corrections. | Paclet `resources/InfraGaugeTheory` is live (Pavel Pokorny). `RandomFiberedGraph`, `ConnectionQ`, `HolonomyMatrix`, `FlatConnectionQ`, `FindHorizontalLeaf`, `GraphTangentBundle`. | None yet. Task group IG below. |
| **Infraanalysis** | Multi-variate calculus on graphs coordinatized by bundles of directed acyclic subgraphs; built-in renormalization via blowups; forms→cochains integration map. | 1D calculus on directed graphs as blowups of ℝ; cotangent bundle + de Rham complex in progress. | Partial — `DiscreteCalculus`, `DiscreteCalculusSymm`, `HypergraphCalculus` (grad/div/SBP), `LaplacianBridge` (scaled 2nd difference → `f''`), `HypergraphCycleBridge` (explicit hypergraph anchor). No DAG-coordinatization yet. Task group IA. |
| **Ruliology / EME tracking** | Catalog rules by their geometric signatures; track eme (vertex) lifetimes across multiway branches as persistence signals. | Community paper in preparation; efficient-rewriting engine (Richard Assard) for GPU-parallel multiway. | None yet. Task group R. |

## 3. Technical primitives — colleague definitions

### Dimension (multiple, compatibility as a geometricity test)

- **Wolfram–Hausdorff dimension.** `d(v) := lim_{r→∞} log V_v(r) / log r` where `V_v(r)` is the number of vertices within graph distance `r` of `v`. Plateau across scales marks the "real" dimension; small r shows local irregularities, large r shows finiteness effects.
- **Homology-based dimension.** Top Betti number that survives persistence across a plateau of scales on the Vietoris–Rips complex.
- **Coordinatization-based dimension.** Number of extremal orthogonal axes that coordinatize a local neighborhood. Distinguishes compact from non-compact directions.
- **Causal-graph dimension.** Derived from longest-antichain / foliation-thickness analysis of the causal graph.
- **Model-rules dimension.** Classify a rule by the dimension it tends to produce.
- **Compatibility principle.** Different notions should agree for "physically admissible" rules; discrepancies flag pathological cases.

### Topology (Vietoris–Rips + persistence)

- **Latschev theorem** (cited): for any closed Riemannian manifold *M*, there exists `ε₀` such that for any `ε < ε₀` there exists `δ` such that for every metric space *X* with `d_GH(X, M) < δ`, the Vietoris–Rips complex `VR_ε(X)` is homotopy equivalent to *M*.
- Application: given a hypergraph, take cliques of hyperedges → 1-skeleton → `VR_ε` at scales `ε = 1, 2, …` → persistence barcode → recover topology of limiting manifold.
- **Scale-dependence phenomenon.** Quantum scale `ε < ε₁`: fully discrete. Mesoscale `ε₁ < ε < ε₂`: homology matches intuition. Coarse scale `ε > ε₂`: collapses. This is an intrinsic feature, not a bug.
- **Hodge Laplacian on VR.** Spectral invariants of the vertex and edge Gram matrices give further geometric signature. Oriented versions support discrete Chern–Simons (IBL-∞) for loop-space information.

### Fibered / gauge constructions

- **Fibered graph** = `(total: Graph, proj: total → base)`. Vertical edges live inside fibers, horizontal edges are transverse.
- **Fiber bundle predicate** `FiberBundleQ`: isomorphic fibers + edge-lifting property + at-most-one-edge-lift + local triviality (trivial holonomy on cycles in each vertex neighborhood).
- **Connection** = subgraph of transverse edges with unique edge-lifting (`AtMostOneEdgeLiftQ`) and completeness.
- **Section** = map base → total with `proj ∘ section = id`. Smooth iff adjacency-respecting.
- **Parallel transport** along a base path = fold horizontal lifts; returns an association on fibers.
- **Holonomy matrix** = permutation matrix around a loop; `HolonomyMatrices` covers basis cycles.
- **Wilson loop** = trace of holonomy.
- **Flat connection** = trivial holonomy on all loops.
- **Tangent bundle** `GraphTangentBundle[g, r]` = fibers are `r`-neighborhoods; horizontal edges are "maximal transverse bipartite matchings."
- **Exponential map** (proposal): `exp_v(e) = ∑_u [(#shortest paths v→u starting with edge e) / (total #shortest paths v→u)] · u`.

### Infracausality primitives

- Minimal model of observer = causal edge.
- Minimal model of spatial closeness = shared immediate common ancestor.
- Foliation = decomposition into successive antichains ≡ Cauchy surfaces.
- Light ray from point *p* = subgraph where causal interval `[p, q]` is degenerate for every `q` in the ray.
- Spatially reconstructed hypergraph = events in same foliation slice connected when they share an immediate common-ancestor event in the previous slice.
- Multi-fibrations arise because shortest-path projections are non-unique: one fiber element lies over multiple base points. Standard fibrations are the wrong model; multi-fibrations are honest.
- Proper time = longest-path foliation (candidate).
- Further goals: event horizon, inertial frames, Lorentz transformation, mass, axiomatic special relativity (EPS scheme), Marzke–Wheeler clocks on transitively-reduced causal graphs.

### Branchial / quantum

- Branchial graph at slice *n*: states sharing an immediate common ancestor.
- Connected components = superposition classes; self-adjoint adjacency → Hilbert space in limit.
- **Elementary blowups**: rules with single-hyperedge LHS. Their commutator is causal-branchial-trivial, so they form a Lie algebra on isomorphism classes of hypergraphs.
- Unary-edge blowups = **insertion Lie algebra** of perturbative QFT. Graded version exists.
- Poisson bracket on formal functions ⟹ Hamiltonian mechanics on ruliad, with canonical functions `#V`, `#E`.
- Moduli space of connections → path-integral weights via causal-branchial-graph time evolution.
- Fisher metric on branchial graph → Fubini–Study in limit (Van Le direction).

### Synthetic / axiomatic

- Synthetic Euclidean analogs: circle = equidistant set from a point; line = shortest-path center; sphere, cylinder, plane.
- Fréchet-eccentricity selection for canonical straight lines.
- Multi-constructions ensemble treated as a branchial object with Hausdorff metric.
- Axiomatic formulation planned.

## 4. Coverage map — what this repo currently has

### Fully Lean-formalized (axiom-clean)
- Hypergraph calculus: `laplacianHyper` + linearity / self-adjointness / Dirichlet-PSD / divergence theorem; `hyperedgeGradient`, `hypergraphDiv`, discrete Stokes.
- PDE ladder on `Hypergraph V`: heat (mass conservation + L² decay + long-time decay to constant), wave (energy), Klein–Gordon (energy + mass), Schrödinger (unitarity), scalar field Lagrangian + Euler–Lagrange.
- Cycle bridge: `cycleHypergraph n` + matrix Laplacian + `exp(t · Δ)` heat kernel + C² Taylor convergence of the scaled second difference to `f''`.
- Flat continuum limits: scaled cycle → S¹, path → interval, 2-torus, d-torus, discrete Lorentz → Minkowski.
- Infracausality: `CausalGraph V` as TR-DAG, `ObserverChain`, `LightRay`, `Foliation` from successive antichains, EPS axioms, Marzke–Wheeler clock construction, `SpatiallyReconstructedHypergraph`, multi-fibration from non-unique shortest paths.
- Fibered-graph machinery: `FiberedGraph`, `Section`, `Connection`, `ParallelTransport`, `HolonomyMatrix`, `WilsonLoop`, `FlatConnection`, `FiberBundle`, `GraphTangentBundle`, `MultiFiberedGraph`.
- Hypergraph connection: `HypergraphConnection H G` with `flat`, `IsSymmetric`, `transportWalk`, `holonomy`, `IsFlat`, and the monoid-hom property `transportWalk_append`.
- Infradimension: Wolfram–Hausdorff (ID1), plateau detection (ID2), homology dimension (ID3), coordinatization (ID4), causal-graph (ID5), compatibility `V(v, r) = 2r + 1` on cycle hypergraphs (ID6 `dimensionCompatibilityObligation_holds`).
- Infratopology: `VietorisRipsComplex`, persistence diagram / barcode (IT4), Hodge Laplacian on VR 0- and 1-forms (IT2) with spectrum (IT3), Latschev obligation for cycles (IT5), scale trichotomy for cycles (IT6).
- Ruliology (IR): `RuleSignature V`, `hypergraphSignature`, conservation theorem (IR2 — |LHS|=|RHS| bounds dimension), planar rules have dim ≤ 2 (IR4), tree-producing rules have log-branching dimension (IR3), product-rule additivity (IR5), candidate-rule database + screens (IR6), refined reverse-engineering obligation (IR7; over-strong form provably FALSE).
- Blowup/Poisson (IB): `ElementaryBlowup`, blowup operations, `BlowupLieAlgebra`, insertion Lie (IB4), Poisson bracket on formal functions (IB5), radial/laminar blowup (IB6).
- Branchial/quantum (IQ): finite `BranchialSlice` (I1), uniform measure (I2), ℂ-amplitudes + Born rule (I3), ℓ²(slice) Hilbert space + self-adjoint ℂ-linear adjacency (I4), unitary Schrödinger evolution (I5), Hermitian observables (I6) + expectation values (I7), Fisher metric on branchial (IQ5), Fubini-Study / Bhattacharyya bound (IQ6), EME persistence baseline (IQ8), path-integral baseline (IQ9).
- Synthetic axiomatic (IS): circle, line, sphere (IS1); `InfrageometricScene` (IS2); axiomatic-synthetic layer (IS3).
- Continuum targets (local-coord): Schwarzschild component functions + all eight Christoffels on the exterior; Schwarzschild as `PartialMetricData 4` (B1, B5); FLRW `flrwPartial a da` (B6); Reissner-Nordström `rnPartial M Q` (B8); de Sitter; 2-sphere; warpedDiag2.
- Bundle-level metric predicates: `DiagRiemannianMetric` + Euclidean witness (C1); `DiagLorentzianMetric` + Minkowski witness (C2).
- Hypergraph-origin obligations: every continuum metric in the GR zoo carries a `HypergraphMetricOriginObligation` Prop with flat-case witness; `LorentzianManifoldOriginObligation`, `ConnectionDataOriginObligation`, `EFEOriginObligation` similarly; `minkowski4_flat_vacuum_EFE_originated_global` is the first complete rule → metric → connection → EFE chain.
- Refutations: F1 (no canonical metric), F2 (fiat orthonormality), F3 (dim-preservation tautology), F4 (causal-invariance ⇔ GC tautology), F5 (ill-defined "becomes"), F6 (G3 circular procedure = identity), F7 (named-rule conservativity blocks 4D cone growth); F8 Raychaudhuri statement level.
- Ollivier–Gorard quantitative discrepancy: `ollivier_minus_gorard_leading` with S² worked example `s2_gorard_error = δε²/8`.

### Partially formalized
- A6 weak-convergence lift: polynomials up to degree 3 done; general continuous via Weierstrass pending.
- D6 long-time convergence of the heat equation: non-constant eigenmodes decay; full result for arbitrary initial data needs eigenbasis-spanning.
- P20 Rodkey classification of graphs with pointwise-constant Wolfram–Hausdorff dimension: sufficient chain `AdjTransitive → DistTransitive → BallVolumeVertexUniform → LocalDimensionVertexUniform` and necessary-regularity direction proved on cycle/path; general classification open.
- IB2 causal-branchial-trivial commutator theorem: predicate-level placeholder; real theorem statement needed.

### Still open
- IG10 exponential map via weighted shortest-path counts.
- ID7 heat-trace small-`t` asymptotics for spectral dimension.
- C3–C8 bundle connection / Levi-Civita existence-uniqueness (Koszul) / scaled-discrete-connection → Levi-Civita convergence.
- Curved-GR witnesses: Schwarzschild/Kerr/FLRW Ricci computations (B2/B3/B4, B7, B9); second Bianchi for Einstein tensor (B11); Ricci symmetry (B10).
- G2 discrete gauge field (uses Rung 4).
- E5 ADM decomposition, E6 Lorentzian-Gromov–Hausdorff, E7 discrete causal → continuum Lorentzian convergence.
- D11 Cauchy problem for Einstein evolution (Choquet-Bruhat 1952).
- A7 Wasserstein-1 convergence rate; A8 d-torus measure lift.
- Branchial quantum continuum: I8 branchial-Hilbert continuum limit, I10 path-integral / unitary-evolution equivalence.
- Full infrageometry obligations bundled in `all_obligations_hold`; the open items above are those left after that bundling.

## 5. Lean task groups — full program coverage

These are added as tasks (see next commit). Each group is ordered so that early tasks unblock later ones.

### Group IA — Infraanalysis (discrete calculus on hypergraphs + DAGs)
- IA1. `dagAsBlowupOfInterval` — `Hypergraph V` where `V = Fin n` with linear orientation as a 1D-coordinate blowup of `[0, 1]`.
- IA2. Calculus on coordinate DAGs: `dagDerivative`, `dagIntegral`, fundamental theorem.
- IA3. De Rham complex on `Hypergraph V`: 1-form, 2-form, `d` operator, `d² = 0`.
- IA4. Integration map forms → cochains on clique complex; `∫_γ ω` is cochain of γ.
- IA5. Blowup / refinement operator as a `Hypergraph V → Hypergraph W` map; commutes with calculus up to `O(1/n)`.
- IA6. Scaled second-difference → `f''` for `C²` functions (closes /).
- IA7. `C^k` uniform convergence on compacts (closes).

### Group IG — InfraGaugeTheory (port from Pavel Pokorny's paclet to Lean)
- IG1. `FiberedGraph V W : Type` with projection `π : V → W` and type classes for fibers.
- IG2. `Section π` := `σ : W → V` with `π ∘ σ = id`.
- IG3. `Connection π` := `Finset (V × V)` with at-most-one-edge-lift.
- IG4. `ParallelTransport` along a base path.
- IG5. `HolonomyMatrix` on a loop.
- IG6. `WilsonLoop := trace HolonomyMatrix`.
- IG7. `FlatConnectionQ` predicate.
- IG8. `FiberBundleQ` predicate.
- IG9. `GraphTangentBundle` as a specific `FiberedGraph`.
- IG10. `ExponentialMap` via weighted shortest-path counts.
- IG11. Multi-fibrations: `MultiFiberedGraph` where `π` is multi-valued.

### Group IC — Infracausality (axiomatic SR from causal graphs)
- IC1. Type `CausalGraph` = transitively-reduced DAG.
- IC2. `ObserverChain` = causal edge / maximal chain.
- IC3. `LightRay` as a degenerate-interval subgraph.
- IC4. `Foliation` = successive antichains; `ProperTime` := longest-path height.
- IC5. `SpatiallyReconstructedHypergraph` from causal graph + foliation.
- IC6. Multi-fibration structure from non-unique shortest-path projection.
- IC7. EPS axiom set (as Props): light-structure, particle-structure, compatibility.
- IC8. `MarzkeWheelerClock` construction + determinism theorem.
- IC9. Lorentz-transformation emergence for scaled causal DAGs converging to Minkowski.
- IC10. Extension to curved targets (open obligation, similar to `SchwarzschildObligationMet`).

### Group IT — Infratopology (Vietoris–Rips, Hodge, persistence)
- IT1. `VietorisRipsComplex (H : Hypergraph V) (ε : ℕ) : AbstractSimplicialComplex V`.
- IT2. `hodgeLaplacian` on 0-forms and 1-forms of VR.
- IT3. Spectrum of Hodge Laplacian — eigenvalues, multiplicities.
- IT4. `persistenceDiagram (H : Hypergraph V) : PersistenceDiagram`.
- IT5. `BettiNumber VR_ε k` computation.
- IT6. Latschev-theorem statement as a `Prop` obligation (+ proof for cycle → S¹).
- IT7. Scale-dependence signature: formal statement of the quantum / meso / coarse trichotomy as a theorem on Betti-number function of ε.

### Group ID — Infradimension (multiple notions + compatibility)
- ID1. `wolframHausdorffDimension (H : Hypergraph V) (v : V) : ℝ`.
- ID2. Plateau detection: `wolframHausdorffDimension` as a function of neighborhood radius range.
- ID3. `homologyDimension` from top surviving Betti number in persistence.
- ID4. `coordinatizationDimension` via extremal orthogonal axes.
- ID5. `causalGraphDimension` from longest-antichain analysis.
- ID6. Compatibility theorem: on regular lattices, all notions agree with the lattice dimension.
- ID7. Incompatibility as a pathology detector: rules where notions disagree are flagged.

### Group IB — Infrablowup / renormalization
- IB1. `ElementaryBlowup (e : Hyperedge V) : Hypergraph V → Hypergraph V`.
- IB2. Commutator `[B₁, B₂]` on isomorphism classes; theorem: causal-branchial component vanishes for LHS-single-hyperedge rules.
- IB3. `BlowupLieAlgebra` structure.
- IB4. Insertion Lie algebra for unary edges ≅ pQFT insertion algebra.
- IB5. Poisson bracket on `ℝ[V_count, E_count]`; Hamiltonian vector fields.
- IB6. Radial and laminar blowup operations, commuting with calculus up to `O(1/n)` (IA5 generalization).
- IB7. Graded version.

### Group IQ — Branchial / quantum
- IQ1. `BranchialGraph` type + `Fintype` instance for finite systems (closes).
- IQ2. Branchial ℓ² Hilbert space (closes).
- IQ3. Unitary evolution on branchial ℓ² (closes).
- IQ4. Amplitudes and observables (closes).
- IQ5. Fisher metric on branchial graph.
- IQ6. Fubini–Study metric as limit of Fisher metric on refined branchial graphs.
- IQ7. Branchial continuum limit → Hilbert space (closes).
- IQ8. EME-tracking: persistence of a vertex across multiway branches as a branchial observable.
- IQ9. Path integral as a sum over singleway causal-graph classes.

### Group IS — Synthetic infrageometry
- IS1. `SyntheticCircle`, `SyntheticLine`, `SyntheticSphere` from equidistant/shortest-path constructions.
- IS2. `InfrageometricScene` type for multi-constructions.
- IS3. Branchial structure on scenes with Hausdorff metric.
- IS4. Axiom set (Euclid-flavored) for synthetic infrageometry.
- IS5. Incidence / collinearity / concurrency theorems.
- IS6. Tropical-geometry translation (algebraization direction).

### Group IR — Ruliology
- IR1. `RuleSignature (R : RewritingSystem P) : DimensionTuple × GrowthTuple × CurvatureTuple × …`.
- IR2. Conservation theorem: `|LHS| = |RHS|` ⇒ bounded Wolfram–Hausdorff dimension (formalizes `empirical_refutation_key_rule`).
- IR3. Tree-producing rules ⇒ dimension = `log(branching)`.
- IR4. Planar rules ⇒ dimension ≤ 2 via Euler-formula.
- IR5. Candidate-rule database and screening pipeline.
- IR6. Product rules `R₁ × R₂` → dimension additivity (under confluence).
- IR7. Computable hypergraph invariants → Lean-verifiable check list.

## 6. How this relates to the Gorard-refutation track

The refutation work in `Refutations/F1–F5` + `MAJOR_FLAWS.md` is **not** subsumed — it becomes one arm of a larger program:

- **Refutation arm:** pin down what the 2004.14810 / 2102.09363 / 2303.07282 corpus actually proves vs. claims. Publishable as P1–P5.
- **Positive arm (this file):** build the genuine infrageometry the corpus gestures at. Publishable as P6–P9.
- **Bridge arm:** the `ContinuumLimitStatement` Props state the *concrete* obligations a future rule must satisfy. Any positive construction lives as a term of one of those Props. Any refutation lives as a `¬ obligation`.

Concretely:
- GR continuum limits (Schwarzschild, Kerr, FLRW) remain open obligations (`SchwarzschildObligationMet`, etc.). Group IC task IC10 extends to curved targets.
- QM via branchial (unitary evolution, Hilbert-space limit) is formalized on the discrete side (Schrödinger unitarity, self-adjoint Laplacian) and obligated to converge via Group IQ.
- The hypergraph Laplacian is already the backbone of both sides. Every continuum object we add must factor through it.

## 7. Ongoing external work to track

| Item | Person | Relevance |
|---|---|---|
| Axiomatic Relativity from Causal Graphs paper | Carlos Zapata, Sara Ahmed | Input for IC7 (EPS axioms) and IC8 (Marzke–Wheeler) |
| InfraGaugeTheory paclet (`resources/`) | Pavel Pokorny | Reference implementation to port — Group IG |
| EME tracking (WWS26) | Ahmed, Pavel Hajek | Input for IQ8 |
| Infragauge intern project (Apr–Jun 2026) | Ioana Milea | Moduli of connections, gauge dynamics on causal graphs |
| Infrageometry paclet (differential forms, fibered graphs) | Pavel Hajek | Reference for IA3–IA4 |
| Austin conference (Apr 17–19, 2026) | many | Publication window for P1, P6 |
| Srní / Madrid / Mathematical Institute talks | Pavel Hajek | Public statements of program; verbatim definitions available in `/tmp/infrageom/srni.txt`, `/tmp/infrageom/madrid.txt` (cached locally for reference) |
| Winter School Srní 2027 | Stephen Wolfram (invited) | Bridge to Czech differential-geometry community |
| Van Le Austin talk | Van Le | Input for IQ5–IQ6 (Fisher → Fubini–Study) |
| Hubert Kolcz MBQC / Lie–Poisson | Hubert Kolcz, Pavel | Input for IB5 (Poisson on ruliad) and IQ9 |
| Jan Pullman IBL-∞ / BV | Jan Pullman | Input for IT2 (Hodge Laplacian on VR, higher-order info) |
| Diffusion Geometry (Srní speaker) | external | Complementary framework; feeds into IT + IR as validation |
| Tropical geometry | Pavel Pokorny | IS6 — algebraization of synthetic |

## 8. Grounding principle (unchanged)

Every continuum object in the Lean library must have an explicit hypergraph origin — either a proved theorem or a `Prop` obligation with explicit `False`. No continuous islands. Schwarzschild, Kerr, FLRW remain open obligations; PDE ladder and flat continuum limits are proved; fibered/gauge/branchial objects must all factor through `Hypergraph V`.

The program is not about faster theorems — it is about *right theorems*. Every claim carries a proof or a precisely stated open.
