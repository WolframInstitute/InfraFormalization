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

### Group KN — Oliver Knill quantum-calculus track (#237–#256, added 2026-04-24)

Formalisation in Lean of Knill's discrete-geometry program as catalogued in
[`resources/Infrageometry/QuantumCalculus.md`](resources/Infrageometry/QuantumCalculus.md).
Each task has an upstream Mathematica counterpart in
[`resources/Infrageometry/Infrageometry/Kernel/QuantumCalculus.wl`](resources/Infrageometry/Infrageometry/Kernel/QuantumCalculus.wl)
(290 lines; functions `WaveEquationSolution`, `WuCharacteristic`,
`IsospectralDeformation`, `DiracZetaFunction`, `IndexExpectationCurvature`, …).

Knill's program is **strict finitism applied to differential geometry**:
every continuum concept gets a purely combinatorial counterpart on finite
abstract simplicial complexes (or delta sets / quivers). Bosonic vs Fermionic
invariants (volumes order-blind vs cohomology orientation-aware) are tracked
separately. The McKean–Singer supersymmetry of `H = D²` between even / odd
forms underwrites both Euler–Poincaré and Brouwer–Lefschetz.

- KN1. Wave equation d'Alembert solution `u(t) = cos(D t) u₀ + t · sinc(D t) v₀` via matrix functions on the Dirac matrix.
- KN2. Discrete-time wave step (leapfrog) + unitary wave propagator `exp(i D t)`.
- KN3. Wu characteristic `ω_m(G) = ∑_{x_1 ∩ ⋯ ∩ x_m ≠ ∅} ω(x_1) ⋯ ω(x_m)` and Wu cohomology with fusion inequality.
- KN4. Isospectral Lax-pair deformation `D' = [d − d*, D]` of the Dirac operator + extracted diagonal mass term.
- KN5. Connes spectral distance `d(x, y) = sup{|f(x) − f(y)| : ‖[D, f]‖ ≤ 1}`; bridge to `Hypergraph.dist`.
- KN6. Dynamical connection matrix `L(T)` and Green function `g(T) = L(T)⁻¹` under graph automorphism; unimodularity `det(L) = ±1` (Fermi); energy theorem `∑ g(x, y) = χ(H)`; hydrogen operator `L − L⁻¹` for 1D.
- KN7. Curvature generalisations — index expectation (`K(x) = E[i_f(x)]`), sectional, form curvature (curvature on k-forms), boundary curvature.
- KN8. Dirac / Connection / Lefschetz zeta functions; bridge to "elementary dyadic Riemann hypothesis" for circular graphs.
- KN9. Analytic torsion `log T(H) = ½ ∑_k (−1)^{k+1} k · log det'(H_k)` + spectral monotonicity under barycentric refinement.
- KN10. Wave-front exterior derivative + spherical-average non-local `d` (Knill 2025–2026 wave-front calculus).
- KN11. Geodesic gas + cellular-automaton geodesic evolution on triangulated 2D lattices (Hopf–Rinow workaround on finite complexes).
- KN12. Delta sets / quivers — face-map exterior derivative + cohomology; Gauss–Bonnet, Brouwer–Lefschetz, supersymmetry on delta sets.
- KN13. Soft barycentric refinement (random subdivision) + Fisk-manifold predicate (every codim-2 face has even number of top-dim faces).
- KN14. McKean–Singer supersymmetry: non-zero spectrum even↔odd forms equal; super-trace deformation derives Euler–Poincaré + Brouwer–Lefschetz from one fact.
- KN15. Atiyah-Singer / Atiyah-Bott analog in finite geometry (Knill 1708.06070): `index(D) = χ(H)`; isolated-fixed-points `L(T) = ∑ ω(x)`.
- KN16. Cartan's magic formula `L_X = i_X d + d i_X` (discrete) — Knill 1811.10125.
- KN17. Bosonic / Fermionic distinction in the type system — separating order-blind from orientation-aware invariants.
- KN18. Brouwer fixed-point for graph endomorphisms via Lefschetz-number computation (Knill 1206.0782).
- KN19. Deformed exterior derivatives `d_h` continuous family for `h ∈ ℝ` (Knill 1306.5597).
- KN20. Level sets + Euler characteristic — discrete Morse-theory bridge (Knill 2401.07435).

**Key Knill papers** (catalogue in `QuantumCalculus.md §5`):

| arXiv | Year | Topic |
|---|---|---|
| [1206.0782](https://arxiv.org/abs/1206.0782) | 2012 | Brouwer fixed-point (KN18) |
| [1205.0306](https://arxiv.org/abs/1205.0306) | 2012 | Index expectation curvature (KN7a) |
| [1301.1408](https://arxiv.org/abs/1301.1408) | 2013 | Discrete supersymmetry / McKean-Singer (KN14) |
| [1306.5597](https://arxiv.org/abs/1306.5597) | 2013 | Deformed exterior derivatives (KN19) |
| [1312.4239](https://arxiv.org/abs/1312.4239) | 2013 | Zeta functions of circular graphs (KN8) |
| [1708.06070](https://arxiv.org/abs/1708.06070) | 2017 | Atiyah-Singer/Atiyah-Bott in finite geometry (KN15) |
| [1801.04639](https://arxiv.org/abs/1801.04639) | 2018 | Elementary dyadic Riemann hypothesis (KN8) |
| [1811.10125](https://arxiv.org/abs/1811.10125) | 2018 | Cartan's magic formula, discrete (KN16) |
| [2205.14097](https://arxiv.org/abs/2205.14097) | 2022 | Graphs, groups and geometry |
| [2401.07435](https://arxiv.org/abs/2401.07435) | 2024 | Level sets and Euler characteristic (KN20) |
| [2501.14611](https://arxiv.org/abs/2501.14611) | 2025 | Wave front density conjectures (KN10) |

### Group IGE — Lean port of upstream `Infrageometry` Mathematica paclet (#257–#261)

The `resources/Infrageometry/Infrageometry/` paclet is the reference Wolfram-Language
implementation of the Knill / quantum-calculus + infrageometry toolkit. The IGE
group ports it **module by module** to Lean so that every Mathematica function
has a Lean counterpart we can prove theorems about (and so KN-tasks have stable
foundations).

- IGE1. Lean port of `Infrageometry.wl` core (351 lines): `complexClosure`, `simplexCardinalities`, `complexEulerCharacteristic`, `complexFermiCharacteristic`, `simplexUnitSphere`, `simplexStar`, `simplexCore`, `complexIncidenceMatrix`, `connectionMatrix L`, `greenFunctionMatrix g = L⁻¹`, `diracHodgeMatrix D = d + d*`, `hodgeMatrix H = D²`, `bettiVector`, `lefschetzNumber`, `lefschetzCurvature`, `simplicialMap`, `complexPolynomial`, `dehnSommervilleQ`, `barycentricRefinement`, `faceGraph`, `superTrace`, `superDeterminant`, `pseudoDeterminant`, `complexJoin`, `complexDual`. Foundation for the whole KN-track.
- IGE2. `SimplicialSet.wl` Lean port (315 lines): face/degeneracy maps + delta-complex morphisms; bridges KN12 + IA1–IA5.
- IGE3. `TDA.wl` Lean port (242 lines): VR / Čech / persistence on infrageometry hypergraphs; aligns with IT1–IT4.
- IGE4. `Mesh.wl` Lean port (248 lines): mesh-generation primitives + chain-of-meshes refinement; geometric realisation of a hypergraph + coordinatisation as a mesh.
- IGE5. `Chains.wl` Lean port (63 lines): formal chain complex (integer-coefficient combinations of simplices, boundary, sum, scaling) underlying cohomology computations.

### Group SIG — Synthetic infrageometry, expanded (#262–#266)

Parallel to IS1–IS6 above, the SIG group adds module-level Lean ports of the
[`resources/SyntheticInfrageometry/`](resources/SyntheticInfrageometry/) paclet
plus the branching-stability research questions from its README.

- SIG1. `Tools.wl` Lean port — primitive constructions (`Line`, `Ray`, `Segment`, `Perpendicular`, `Parallel`) the infra-observer can use, each branching to a multi-set of `InfrageometricScene` (existing IS2). Foundation for SIG2/SIG3.
- SIG2. `Postulates.wl` Lean port — Euclid-style axioms (5 postulates + common notions) as `Prop`s on a hypergraph + scene; enables ruliological study `for each rule r: which postulates hold on every state of singleWayEvolve r seed n?`. Bridges to existing IS3 axiomatic infrageometry. **Empirical question**: does the parallel postulate hold on regular tilings? On Wolfram-rule outputs?
- SIG3. `Predicates.wl` Lean port — geometric predicates (`collinear`, `concyclic`, `perpendicular`, `congruentSegment`, `betweenness`); decidable for finite hypergraphs; used by SIG2 to check axioms.
- SIG4. `Coordinatization.wl` Lean port — analytisation/algebraisation of synthetic infrageometry via shortest-path counts / Cayley-style embedding; bridges ID4 (CoordinatizationDimension) and IGE1 (Cayley-graph structure).
- SIG5. **Branching-construction stability** (per SyntheticInfrageometry README): `SceneDistance s₁ s₂ : ℝ` (Wasserstein-style distance between scenes via #214), and `ConstructionStability c r := tendency of branching scenes from construction c on rule-r outputs to converge under refinement`. First concrete instance: subdivision rule (#234) on path/cycle.

#### Conceptual framing for SIG2/SIG3 (synthetic geometry → graph theory bridge)

The SIG2/SIG3 ports should *not* be a line-by-line transcription of the Mathematica paclet. They should implement the following **research-level framing** that connects axiomatic synthetic geometry to graph-theoretic primitives we already have. Adding this here so the eventual Lean implementation lands the right way the first time.

**1. Tarski reduction to two predicates.** Tarski's axiomatisation of Euclidean geometry uses only two primitive predicates: **betweenness** `B(a, b, c)` and **equidistance** `Cong(ab, cd)`. With `Hypergraph.dist` in hand (which we have, `HypergraphDistance.lean`), both become 1-line graph-theoretic definitions:
```
def Tarski.Between (H : Hypergraph V) (a b c : V) : Prop :=
  H.dist a b + H.dist b c = H.dist a c
def Tarski.Cong (H : Hypergraph V) (a b c d : V) : Prop :=
  H.dist a b = H.dist c d
```
Once these are stated, **Tarski's first 8 axioms (T1–T8 — incidence + congruence + segment construction) are universally quantified Props on `Hypergraph.dist`**, decidable for any finite hypergraph. SIG2 should *implement these directly* rather than chase the 5-postulate / common-notion structure of Euclid's Elements (which is harder to bound and entangles definitions with theorems).

**2. The angle problem — full tower.** Tarski's first 8 axioms cover incidence + congruence + extension. Beyond that — angles, perpendicularity, parallel uniqueness — graph theory **stops being enough**. We've now identified that "angle" is not a single concept but a **multi-flavour, multi-abstraction tower**. The thirteen flavour-columns and their abstraction levels (each tracked as an `AT` task #285–#314):

**Column M — Metric** (needs only `Hypergraph.dist`):
- M0 / **AT0** *Stephen chord-ratio* `d(A,B)/d(O,A)` (equidistant `A,B`). Pure-counts, no √, no arccos. Equals `2 sin(θ/2)` for the geometric angle.
- M1 / **AT1** *Law-of-cosines* `arccos((d²+d²−d²)/2dd)`. Standard radian θ.
- M2 / **AT2** *Forman vertex defect* `2π − Σ_v incident-pair-angles`. Gauss-Bonnet curvature density.
- M3 / **AT3** *Toponogov asymptotic* `lim_{r→∞} d(γ₁(r),γ₂(r))/r`. CAT(κ) angle.
- M4 *Coarse Gromov product* `(d(O,A)+d(O,B)−d(A,B))/2`. Hyperbolic angle.

**Column S — Spectral** (needs Hodge `d, d*`, Dirac `D`):
- S1 / **AT4** *Knill / Connes* `⟨df_v, dg_v⟩ / (‖df_v‖·‖dg_v‖)`. Riemannian cotangent angle.
- S2 / **AT17** *Heat-kernel scale-resolved* `⟨e^{−tH}f, g⟩ / (‖e^{−tH/2}f‖·‖e^{−tH/2}g‖)`. Spectrum t→0 to t→∞.
- S3 *Cycle/cocycle angle* `⟨c₁, c₂⟩_{H¹(G;ℝ)}`. Cohomology angle.

**Column Y — Synthetic** (predicates only):
- Y0 / **AT10** *Tarski strict `Cong`* `H.dist A B = H.dist C D`.
- Y1 / **AT5** *`AngleCong` via SAS* — Schwabhäuser-style triple-equivalence.
- **Y2 / AT18** *Projective cross-ratio (Cayley-Klein)* `½ log [A,B; C,D]`. **Sidesteps Stephen's straight-lines requirement** — needs only `Between` + `dist` ratios, not unique geodesics. **Possibly the right starting point for non-`GeodesicallyUnique` hypergraphs.**

**Column T — Transport** (needs Wasserstein):
- T1 / **AT12** *Ollivier-W₁ angle* `W₁(μ_A, μ_B)` between geodesic-ball measures.
- T2 *OT-map angle* — direction of optimal transport plan (variant of T1).

**Column Q — Branchial / QM** (needs `BranchialHilbert`):
- Q1 / **AT13** *Hilbert / Bures* `cos θ = |⟨ψ|ϕ⟩|` or `(tr √(√ρ σ √ρ))²`. Born / fidelity.
- Q2 / **AT24** *Maslov / symplectic* — Lagrangian index.

**Column L — Causal / Lorentzian** (needs causal-interval data):
- L1 / **AT14** *Rapidity* `arctanh((Δt − Δx)/(Δt + Δx))`. Boost angle in `SO(1,1)`.
- L2 *Causal cone-axis angle* — between two future-cones at a vertex (variant of L1).
- L3 *Lorentzian-GH angle* — analog of M3 in Lorentzian setting (gates #213).

**Column G — Gauge / fibre** (needs `FiberedGraph` + `Connection`):
- G1 / **AT15** *Holonomy angle* `arccos(tr HolonomyMatrix γ / 2)`. Rotation around a loop.
- G2 *Wilson-loop angle* `arg(WilsonLoop γ)` for U(1).
- G3 / **AT22** *Connection 1-form* `ω ∈ Ω¹(M; so(d))` per-edge.
- G4 *Curvature 2-form* `Ω = dω + ω∧ω`. Riemann tensor.

**Column I — Information-geometric** (needs `FisherMetric`):
- I1 / **AT16** *Fisher angle* — cotangent angle on statistical manifold.
- I2 *Bregman / e-connection* — divergence-based.
- I3 *KL-divergence angle* — derivative-based.

**Column H — Higher-dim** (k-tuples, k ≥ 3):
- H1 / **AT19** *Solid angle* — `k`-volume of spherical simplex from `k+1` rays.
- H2 / **AT20** *Regge deficit* `2π − Σ dihedral angles around (n−2)-simplex`. **THE numerical-GR variable for Phase D BBH.**
- H3 *Dihedral angle* — between two `n−1`-simplices sharing an `n−2`-face.

**Column K — Conformal**:
- K1 / **AT23** *Conformal class* `[g] := {λ²·g | λ : V → ℝ_{>0}}`. **Angles ARE the conformal data; lengths are extra structure.**
- K2 *Pure-angle theory* = conformal geometry without length scale.
- K3 *Lorentzian conformal* — conformal class + light-cone field.

**Column F — Higher-form completion**:
- F1 / **AT21** *Discrete metric tensor* `g_{ij}(v)` bilinear. Then `cos θ = g(X,Y)/√(g(X,X)·g(Y,Y))` is angle as a 2-tensor.
- F2 *Riemann tensor* — full curvature 2-form components.
- F3 *Holonomy group* — image of parallel-transport in `SO(d)`.

**Column N — Non-standard**:
- N1 / **AT27** *Tropical / max-plus angle* — cone-vertex angle on polyhedral fan.
- N2 *p-adic / non-archimedean* — tree-distance ratio on `T_∞`.
- N3 *Cayley-graph character angle* — on abelian covers.

**Column C — Scale-spectrum**:
- C1 / **AT25** *Angular profile* `r ↦ angle(r)` for any definition. Function, not number.
- C2 *Multi-scale signature* — parametric family.

**Column U — Multivalued** (when geodesics aren't unique):
- U1 / **AT26** *Multiset chord-ratio* — `{d(A,B)/d(O,A) : geodesic choices}`.
- U2 *Distribution-over-angles* — probability-measure-valued angle.

**Beyond angle**:
- Conformal (K1) = pure-angle data.
- Riemannian (F1+M1) = angles + length.
- Lorentzian (L1+conformal) = rapidities + light cones (this is GR).
- Kähler (Q3) = angles + complex structure.
- Symplectic (Q2 + 2-form) = Lagrangian-relative angles.

**Three structural observations:**
1. **Y2 (projective cross-ratio) is more elementary than M0 (chord-ratio).** Needs only `Between`, no `dist`. Stephen's "no angle without straight lines" objection is dodged by working in projective Cayley-Klein from the start.
2. **K1 (conformal structure) IS pure-angle data.** A pure-infrageometric-angle theory IS conformal geometry; metric-rich theories add a length scale on top.
3. **H2 (Regge deficit) is THE variable used in actual numerical-GR.** Phase D BBH = Regge calculus on a triangulated 4-manifold. Sum of deficit angles around each 2-face = stress-energy. **Gating, not optional.**

SIG3's `perpendicular` predicate should pick from this tower (probably AT4 spectral or AT0 chord-ratio with `≈ √2` tolerance) and document the choice; the other definitions become cross-validation predicates.

**2.5 Stephen's straight-lines caveat + path-vs-walk distinction.**

Stephen's view: you can't really get angle without first identifying *a* unique direction from `O` toward each target — i.e. a *non-overlapping path* (vertex `Nodup`). On a generic hypergraph, geodesics branch (`MultiFibrationProjection`, IC6) so there isn't *a* canonical direction.

**Three responses, all valid:**
1. **The chord-ratio (M0/AT0) is unconditionally definable** — `d(A,B)/d(O,A)` is a number computed from `Hypergraph.dist`, regardless of geodesic uniqueness. The *interpretation* as "the angle at O" requires unique geodesics; the *number* doesn't. So we land the number, then gate the angle-interpretation theorems on `H.GeodesicallyUnique` (AT8).
2. **Multivalued angles** (AT26) — accept that on non-`GeodesicallyUnique` hypergraphs the angle is a `Multiset ℝ` over geodesic choices. The *spread* of values is itself a curvature-branching signature.
3. **Projective Cayley-Klein angle (Y2/AT18)** — works without straight lines at all. Needs only `Between` + a cross-ratio of distances. **This is the route that fully sidesteps Stephen's objection.**

**The path-vs-walk distinction at the substrate level (PATH1 / PATH2):** Stephen's "non-overlapping path" requires `Nodup` vertex sequence — a *simple path*, not a *walk*. We have it partially:
- `SubdivisionPath.IsPathOf H vs := 2 ≤ vs.length ∧ vs.Nodup ∧ H = pathEdges vs` — exact match for Stephen's notion, but tied to `ExecHG ℕ` and subdivision-rule trajectories.
- `SimpleGraph.Walk.IsPath` after `Hypergraph.toSimpleGraph` reflection — works numerically but the clique-expansion *silently* drops self-loops (`loopless`), collapses multi-edges, and loses the structural fact "*one* rewrite step touched *one* hyperedge". 
- `Hypergraph.dist` uses Mathlib's `SimpleGraph.dist` which is `shortest-walk-length` — but the shortest walk is automatically a simple path (excise cycles), so `dist` IS the shortest-simple-path length. Numerically right; type-level primitive missing.

**Native primitive needed (PATH1):** a first-class `Hypergraph.SimplePath u v` carrying both a `Nodup` vertex list AND the actual hyperedge sequence (so multi-arity structure isn't collapsed). Bridge theorem (PATH2): is the hyperedge-aware distance the same as `Hypergraph.dist`? Edge cases that surface: ≥3-arity hyperedges treated as `K_n` by clique-expansion (any pair-step inside a 3-edge is one step); multi-edges in the `Multiset`; self-loops within a hyperedge.

This native type is **prerequisite** for AT3, AT8, AT26, and the angle-interpretation theorems gating on geodesic uniqueness. It also recovers structural information for causal/branchial-graph extraction (#228, #229) that the clique-expansion currently destroys.

**3. Units are emergent, not fundamental.**

Deep observation: in continuum physics, `[length] = L`, `[volume] = L^d`, `[scalar curvature] = L^{-2}`. Dimensional analysis depends on these distinctions. **In a hypergraph, `r` (geodesic distance, step count) and `V(r)` (vertex count) are both `ℕ`-valued counts — same kind of thing.** There is no `L`, no `L^d`, no `L^{-2}`. *Everything is a count of discrete things.*

**Consequences:**

(a) **Units are emergent under continuum rescaling.** Introducing a length scale `a` (per rewrite step) gives:
   - `r_phys = a · r_count`
   - `V_phys = a^d · V_count` (in flat regime, dimension `d`)
   - `R_phys = a^{-2} · R_count` (scalar curvature)
   
   The dimensions of physical quantities are *artifacts of the rescaling map* `a → 0`, not properties of the underlying object. The bare hypergraph theory has *no* dimensions; *every* dimensional physical quantity is `a^k · (count-level quantity)` for an integer `k` determined by the Taylor-expansion order at which the quantity sits in the `r`-expansion of `V(r)`.

(b) **The "−2" exponent on scalar curvature is intrinsic, not arbitrary.** Why does curvature have units `L^{-2}`? Because it's the *second-order Taylor coefficient* of `V(r)/r^d`. In the count picture: the second-order term of `log V` against `log r`. The exponent `−2` and the coefficient `R` are, structurally, *the same fact*: the second-order Taylor coefficient.

(c) **Bishop-Gromov in dimensionless form.** `V(r) = Ω_d r^d [1 − R r²/(6(d+2)) + O(r⁴)]` gives the discrete recipe (AT9):
   `R_disc(v, r) := (6(d+2)/r²) · [V_flat(d, r) − V(v, r)] / V_flat(d, r)`
   where `V_flat(d, r)` is the regular d-lattice baseline. **The Wolfram-Hausdorff dimension `d` for this formula is exactly what we extract from `wolframHausdorffDimension`.** So scalar curvature comes free given Bishop-Gromov + an existing primitive.

(d) **Angles are dimensionless to begin with.** AT0 (chord-ratio) is `count/count`, AT4 (spectral) is normalised inner-product, AT2 (Forman defect) is `2π − sum of dimensionless contributions`. Angle quantities are units-free already, consistent with the no-units philosophy. In a curved space, *deviation* of measured chord-ratio from the flat-baseline `√2` is the curvature; sum/integrate to recover Ricci scalar.

(e) **Background independence — the structural meaning.** No metric, no clock, no ruler are assumed; geometry is *derived* from rewriting structure. Shared with causal-set / LQG approaches, but pushed further: even *dimension* is emergent (from `V(r)/r^d` plateau), not chosen. The information-theoretic content: bare quantities are essentially `log #(states satisfying condition)` — entropies. Curvature is a *second-cumulant of an entropy-density function*. Consistent with Jacobson "Einstein equation from thermodynamics" and Verlinde "entropic gravity".

This is formalised as **AT11 — Dimensionless ↔ dimensional bridge**: a `DimensionAssignment a` record bundling the length scale and the unit-conversion maps; consistency theorem stating every count-level identity (Bishop-Gromov, Gauss-Bonnet, etc.) lifts to dimensional form by uniform substitution.

**4. Postulate V (parallel uniqueness) → branching characterization.** In continuum geometry the parallel postulate says exactly one line through a non-incident point is parallel to a given line. On a hypergraph, "lines" are maximal geodesics, and **branching geodesics give multiple parallels through a point by default** — Postulate V *fails generically*. The interesting research question is: **for which rule trajectories does the limit satisfy Postulate V**? That's exactly the characterisation of "Euclidean / flat" rules. Concrete Lean predicate:
```
def ParallelUniqueAtRule (sys : RewritingSystem P) (s₀ : Hypergraph V) : Prop :=
  Filter.Tendsto (fun n => parallelMultiplicity (singleWayEvolve sys s₀ n)) atTop (𝓝 1)
```
where `parallelMultiplicity H` counts the worst-case number of geodesic-parallels through a non-incident point in `H`. A rule is "asymptotically Euclidean" iff this multiplicity tends to 1.

**6. Postulate II (segment extension) → boundary obstruction.** Postulate II says segments can be extended indefinitely. On a finite hypergraph this *fails* at boundary vertices (geodesics terminate). On the inverse / refinement limit it can hold. Lean predicate: `def SegmentExtensionAtRule (sys, s₀) := ∀ n, ∀ geodesic γ in singleWayEvolve sys s₀ n, ∃ extension γ' in singleWayEvolve sys s₀ (n+k) for some k`. Closed under the subdivision rule (#234) by construction; fails for finite cycle hypergraphs.

**7. Bachmann's group-of-motions framing.** Synthetic geometry can also be axiomatised via a group of "motions" (= isometries, Bachmann 1959). For graphs, motions = `Aut(graph)` acting on vertices. A **synthetic geometry** is a graph plus a designated reflection-generated subgroup of automorphisms (Coxeter-style). This is an alternative SIG implementation path: instead of T1–T11 Props, define a `GroupOfMotions H` predicate. Pairs naturally with **IG (FiberedGraph)** infrastructure since `Aut(graph)` is a discrete gauge group.

**8. Class-of-graphs trichotomy** (the structural research target for SIG2). For each graph class, identify which Tarski/Hilbert axioms hold:
   - **Path-shape hypergraphs** (e.g. `pathHypergraph n`, `subdivisionTrajectory n`): T1–T8 hold; T11 (parallel uniqueness) trivially holds because there's only one geodesic between any two points; T9 (Pasch) holds; segment-extension (T2-style) fails at endpoints, recovers in the refinement limit.
   - **Cycle / lattice hypergraphs** (`cycleHypergraph n`, d-torus): T1–T10 hold; T11 holds for n large enough; uniformly Euclidean in the limit.
   - **Branching / random hypergraphs** (Wolfram-rule outputs generally): T1–T8 hold; T11 fails (multiple parallels); convergence to Euclidean is a *non-trivial* convergence property of the rule.

The trichotomy itself is the research deliverable: identifying *which structural property of the rule* corresponds to *which Tarski axiom holding in the limit* would give a Wolfram-side classification of "geometricity" rules.

**9. Connection to existing infrastructure.** SIG2/SIG3 should consume:
   - `Hypergraph.dist` (`HypergraphDistance.lean`) for `Between` / `Cong`.
   - `Hodge laplacian` (`KnillCore.lean`) for spectral-angle perpendicularity.
   - `geodesicBall` (existing) for circles.
   - `IsPathOf` (`SubdivisionPath.lean`) for segments.
   - `InfrageometricScene` (IS2) + `MultiwayCausalGraph` (J1) for branching scenes.

The **research handle** for the SIG track:
> Synthetic geometry is what survives in the asymptotic regime where graph distance approximates a Riemannian metric and angles emerge from spectral data. Knill's "infrageometry" = the regime where this approximation is happening.

## 5b. Topology before metric — the layered combinatorial-topology toolkit

Stephen's structural insight: **topological information should be available BEFORE metric / volume / region structure**. The hypergraph has a natural layered topology hierarchy that doesn't need `Hypergraph.dist` or `geodesicBallVolume`:

**Layer −1 — Connectedness ("is every point reachable from every other") — Stephen's actual most-elementary primitive, the partition that EVERY OTHER topological invariant sits inside.**

Four distinct flavours on a hypergraph (none subsumes the others):
- **Spatial** — `∀ u v, ∃ Hypergraph.SimplePath u v` — symmetric, single-state-level. Standard `H.toSimpleGraph.Connected`.
- **Causal** — directed, event-level — "is v in the causal future of u" within one trajectory.
- **Branchial** — symmetric, equivalence-class-level — "share an ancestor in the multiway".
- **Rewriting-reachable** — directed, state-level — "rewrite from A to B in finitely many `MultiStep`s".

`b_0` is then *four distinct invariants*, one per graph-flavour. Spatial-connected does NOT imply causally-connected (spacelike-separated events). Branchially-connected does NOT imply rewriting-reachable (sibling branches). Refinement-stability adds a scale-indexed variant. Tracked as TOP4 (#326).

**Layer 0 — Cells and incidence (requires only the hypergraph structure, takes connectedness as base):**
- Vertices, hyperedges, simplicial / Δ-complex / CW extension
- Per-component analysis of all higher invariants (everything below is computed per connected component)

**Layer 1 — Paths and cycles (requires PATH1 native simple-path type):**
- `Hypergraph.SimplePath u v` carrying `Nodup` vertices + hyperedge sequence — PATH1 (#300)
- Hyperedge-aware vs clique-expansion equivalence — PATH2 (#301)
- Standard graph-theoretic simple-paths via `Mathlib.SimpleGraph.Walk.IsPath`

**Layer 2 — Polygons (closed cycles of simple paths, with Stephen-style extended intersections):**
- `Hypergraph.Polygon` — cyclic sequence of segments with arbitrary `Finset V` intersection loci between consecutive segments — POLY1 (#316)
- Generalised polygon shape invariants `(|I_1|, ..., |I_n|)` — Euclidean is the special case `|I_i| = 1`
- Cellular k-chains in Δ-complex with sheaf coefficients (the full categorical generalisation) — POLY2 (#317)
- Spin networks / spin foams (LQG primitive, knot-invariant home via Witten/Reshetikhin-Turaev) — POLY3 (#318)

**Layer 3 — Cellular sheaves and cycles-with-common-points:**
- Cellular sheaf F on Hypergraph V, restriction maps `F(σ) → F(τ)` for `τ ⊂ σ` — CELL1 (#315)
- Cycles-sharing-common-points = equalizer condition at the shared stalk
- Sheaf-cohomology IS the topology with non-trivial gluing data
- **Pavel's framing**: this IS string theory on the graph — closed strings = 1-cycles, interaction vertices = common-point equalizers, worldsheets = cellular k-chains
- Sheaf-angle (Column W of the angle tower) — AT-W (#319) — `cos θ = ⟨r₁, r₂⟩_{F(common)} / (‖r₁‖·‖r₂‖)` for the restriction maps; generalises Knill/Connes spectral angle

**Layer 4 — Contractibility (binary, scale-indexed predicate on cycles):**
- `Hypergraph.IsContractible γ : Prop` — γ deformable to trivial loop — CONTRACT1 (#329)
- Two natural variants: cellular/static (γ bounds a 2-cell) and multiway/dynamic (rewriting produces the 2-cell)
- Scale-indexed via VR-complex: `IsContractibleAtScale γ r` — death-time in IT4 persistence barcode
- For BBH (Phase D): black-hole horizon = non-contractible cycle; merger = moment cycle becomes contractible

**Layer 5 — Elementary path moves (the generating set for path-equivalence):**
- **Deformations** (DEFORM1 #330) — homotopy-generating: backtrack insertion/removal, 2-cell-boundary substitution, hyperedge-transit substitution
- **Extensions** (DEFORM2 #331) — path-category-generating: forward/backward edge or hyperedge-transit append/prepend
- Together: **deformations + extensions = fundamental category** (Quillen / ∞-groupoid construction)
- `SubdivisionPath/SubdivisionTrajectory` IS already a concrete elementary-extension scheme in the codebase
- **Tietze / Whitehead / Reidemeister style**: the moves are the data; topology is the consequence

**Layer 6 — Homotopy-theoretic invariants (consequence of layer 5):**
- `b_1` first Betti / cycle rank `E − V + C` — TOP1 (#323)
- `b_k` higher Betti via Hodge decomposition — TOP2 (#324)
- `π_1` fundamental group (non-abelian, strictly richer than `b_1`) — TOP3 (#325)
- `π_k` higher homotopy — TOP5 (#327)
- Genus / crossing number — TOP6 (#328)

**Layer 7 — Linking and knot invariants (cellular-cohomology with twisted coefficients):**
- Linking number for disjoint cycles, Borromean detection — KNOT1 (#320)
- Massey products for higher / Brunnian linking — KNOT2 (#321)
- Yamada / Jones polynomial via colored spin-network evaluation (Witten/RT) — KNOT3 (#322)
- For BBH: horizon-merger IS a knot-cobordism (linked cycles → unlinked); for AdS/CFT: bulk-Wilson-line link invariants ARE the holographic dictionary

**Then comes the metric layer (`Hypergraph.dist`):**
- Geodesic balls, ball volumes, the angle tower (M, S, Y, T, Q, L, G, I, H, K, F, N, C, U columns)
- Wolfram-Hausdorff dimension (ID1)
- Bishop-Gromov scalar curvature from log V(r) — AT9 (#294)
- Forman-Ricci, Ollivier-Ricci, full Riemannian/Lorentzian geometry

**The structural point**: every layer above is built from the previous layers WITHOUT requiring metric / measure / region structure. The metric layer (and everything geometric) sits on top. **This is what "infrageometry" is supposed to mean structurally**: the pre-metric topological substrate from which metric geometry emerges in the continuum limit.

## 5c. The full angle tower in one place (cross-reference to §2)

See §2 above for the complete table of angle definitions across 14 flavour-columns × abstraction levels. Tasks AT0–AT27 (#285–#314) plus AT-W (#319) cover the full tower. Three structural anchors recap:
1. **AT18 (projective Cayley-Klein cross-ratio) needs only `Between` + `dist` ratios** — sidesteps Stephen's geodesic-uniqueness requirement; possibly the right starting point on non-`GeodesicallyUnique` hypergraphs.
2. **AT23 (conformal class) IS pure-angle data** — angles alone define conformal geometry; lengths are extra structure.
3. **AT20 (Regge deficit) IS the actual numerical-GR variable** — gates Phase D BBH simulation.

## 5d. Cellular sheaves and Pavel's "string theory on the graph"

The cellular-sheaf framework (CELL1) is the natural categorical home for cycles-with-common-points (Stephen) and string-theory-on-the-graph (Pavel). Translation table:

| String-theory object | Hypergraph object |
|---|---|
| Closed string | 1-cycle in the cellular complex |
| Open string | path with endpoints |
| Worldsheet | cellular k-chain (k≥2) with sheaf data |
| String-vertex interaction | common-stalk equalizer (multiple cycles meeting) |
| Pants diagram | three cycles meeting at a common boundary loop |
| Loop-level amplitude | higher-genus cellular cover |
| String field theory | cellular sheaf with associative-multiplication-on-stalks |
| D-brane | distinguished 0/1-cell anchor for open-string endpoints |
| Vertex operator algebra | algebra structure on stalks at interaction points |

**The hypergraph IS the combinatorial skeleton of the worldsheet.** The cellular sheaf assigns target-space data to each cell. String amplitudes = sheaf-cohomology computations. Phase D BBH = closed-string black-hole physics on a coarse-grained Regge-skeleton 4-manifold.

## 5e. The structural sequence of primitives (Stephen's order)

Stephen's framing identifies the right *order of primitives* — each layer needs only the previous:

0. **TOP4 (b_0, connectedness)** → "is every point reachable from every other" — partition that EVERY OTHER invariant sits inside; four flavours (spatial, causal, branchial, rewriting-reachable).
1. **PATH1** → simple paths (the substrate; Stephen's "non-overlapping paths").
2. **POLY1** → cycles (closed simple paths) — and Stephen's polygon generalisation with arbitrary intersection sequences.
3. **CONTRACT1** → contractibility predicate (binary, scale-indexed via VR-complex).
4. **DEFORM1 / DEFORM2** → elementary moves (the *witnesses* of contractibility / extension; Tietze/Whitehead/Reidemeister style).
5. **HOM1 / HOM2** → path-homotopy `EqvGen DEFORM1`, fundamental groupoid Π_1(H).
6. **TOP3 (π_1)** → homotopy classes of loops under DEFORM1 — first non-abelian invariant.
7. **TOP1 (b_1)** → abelianization of π_1 — first cellular invariant.
8. **TOP2 (b_k), TOP5 (π_k), TOP6 (genus)** → higher cellular and homotopy invariants.
9. **KNOT1/2/3** → linking, Massey products, Yamada/Jones (cellular cohomology with twisted coefficients).

**Layer 8 — Hyperplane / polytope / inside-outside / set-theoretic primitives** (Pavel + Stephen, the bridge between metric and synthetic geometry):

- **TOP4 connectedness reuse** (the most basic primitive — already at Layer −1).
- **MEMBER1 (#346)** — decidable membership `v ∈ R` for `Finset V` and predicate-defined regions. Foundational, comes free.
- **HYPER1 (#338)** — vertex-separator (Pavel's pre-metric "hyperplane"); Menger's theorem framework.
- **HYPER2 (#339)** — perpendicular bisector `{M | dist A M = dist B M}` — the metric hyperplane.
- **HYPER3 (#340)** — Voronoi decomposition / closest-point partition.
- **HYPER4 (#341)** — equidistant-set vs separator equivalence (three increasing strengths: `perpBisector` ⊃ `IsGeodesicHyperplane` ⊃ `IsTopologicalHyperplane`); finite-vs-infinite hyperplane distinction recovers in continuum limit.
- **MIDPT1 (#342)** — midpoint of two points (multivalued, possibly empty).
- **POLYTOPE1 (#343)** — polytope as cell of hyperplane arrangement; foundation for AT19 / AT20 / BBH triangulation.
- **INOUT1 (#344)** — inside-outside / Jordan separator on cycles — *not automatic*; depends on contractibility AND separator status. Four "which side is inside" criteria: contractibility, volume, orientation (ribbon-graph), causal-future. **For BBH: causal-future-of-singularity defines inside.**
- **BOUND1 (#345)** — bounded / diameter (four flavours: spatial, causal, branchial, rewriting), trivial on `Fintype V` but structural at limits.
- **COMPACT1 (#347)** — compactness, only meaningful at the limit (GH / multiway / causal-set).
- **SPHERE1–4 (#334–#337)** — infra-sphere / infra-disk types with topology and surface-area Bishop-Gromov extraction.

**Layer 8b — Surfaces and manifold-detection (Stephen's "what is a surface", Knill / Fisk recursive predicate):**

- **SURFACE1 (#348)** — Hyperspherical shell `H.shell O r := H.infraSphere O r` viewed as induced sub-hypergraph. **Knill/Fisk recursive manifold-predicate**: `IsFiskManifold n H` iff every vertex's unit sphere is `IsFiskManifold (n-1)` AND every unit ball is contractible. **Diagnostic test**: a tree's shell at any positive radius is *disconnected* (one component per branch direction) — fails Knill at any positive dim; tree is NOT a 2-manifold-like hypergraph. Cycle's shell = `S^0` (two disconnected points) — passes 1-manifold criterion. Z²-lattice shell at large r ≈ cycle ≈ `S^1` — passes 2-manifold criterion asymptotically. **Empirical rule-screener for "produces manifold-like hypergraph"**: track shell-connectivity / shell-topology along trajectory states. Subsumes / sharpens KN13 (#249) "Soft barycentric refinement + Fisk-manifold predicate".

**Layer 8c — Open sets / neighbourhoods / local topology (Stephen + Pavel pivot to formal topology):**

- **OPEN1 (#349)** — Multiple natural topologies on a hypergraph: discrete, Alexandrov (closed under one-step neighbour-expansion), metric (via `Hypergraph.dist`, on discrete reduces to discrete), cellular / star (open = star of a simplex in Δ-complex), VR-scale-indexed, causal (Alexandrov from `causallyPrecedes`). Each yields different compactness/continuity theorems.
- **NBHD1 (#350)** — Neighbourhood basis at each vertex `{H.geodesicBall v r}_{r ∈ ℕ}` or `{VR(v, r)}` etc. **Stephen's "locally has neighbourhoods" intuition for surfaces** = neighbourhood basis stabilises to disk-shapes. Tree fails this; manifold-like hypergraphs pass.

**Layer 9 — Bachmann motions / reflection group → isometry / Lie structure** (the bridge to Lie theory):

- Reflections through perpendicular bisectors (HYPER2) generate the *isometry group*.
- Translation = composition of two parallel reflections.
- Rotation = composition of two intersecting reflections.
- Glide reflection = translation + perpendicular reflection.
- Closed under reflection → Coxeter group / root system / Weyl group → Lie algebra (#150 IB5).
- **The constructive route from elementary moves to the full Lie-theoretic isometry structure of differential geometry.**

**Then comes the metric layer**: `Hypergraph.dist` → balls → angles (the 14-column tower) → curvature.

**The whole pre-metric topology hierarchy lives below the metric layer.** This is what "topology before metric" buys you structurally — and it's exactly the Tietze / Whitehead / Reidemeister style: **the moves are the data; topology is the consequence.**

## 5f. The constructive route to differential geometry — Stephen's program statement

Stephen: "we're going to get all the way to differential geometry". The full bottom-up route from hypergraph primitives to differential geometry, with no metric / measure / region structure assumed at the bottom and full Riemannian / Lorentzian / gauge structure emerging at the top:

| Step | Adds | Yields |
|---|---|---|
| 1 | Hypergraph + connectedness | Discrete topological structure (b_0) |
| 2 | Native paths (PATH1) | Path category, geodesic substrate |
| 3 | Cycles (POLY1) + cellular sheaves (CELL1) | Topology objects, Pavel's "string theory on the graph" |
| 4 | Contractibility (CONTRACT1) + elementary moves (DEFORM1/2) | Path-equivalence, Tietze/Whitehead generators |
| 5 | Path-homotopy (HOM1) + groupoid (HOM2) | Fundamental groupoid Π_1 |
| 6 | π_1 (TOP3), π_k (TOP5), Betti numbers (TOP1/2) | Algebraic topology |
| 7 | Knots / linking / Massey (KNOT1–3) | Higher cohomology with twisted coefficients |
| 8 | Hyperplanes (HYPER1–4), midpoints (MIDPT1), polytopes (POLYTOPE1) | Synthetic-geometric primitives |
| 9 | Inside-outside (INOUT1), bounded/compact (BOUND1, COMPACT1) | Region structure |
| 10 | Reflections through hyperplanes | Isometry group (Bachmann motions) |
| 11 | Closed reflection set | Coxeter / Weyl group → root system |
| 12 | Linearisation at identity | Lie algebra (IB5 #150) |
| 12.5 | Surface / manifold predicate (SURFACE1) + neighbourhood basis (NBHD1) + open sets (OPEN1) | Local-Euclidean detection; tree-vs-manifold diagnostic |
| 13 | Add metric `Hypergraph.dist` | Spheres (SPHERE1), Voronoi cells (HYPER3), distances |
| 14 | Angles (AT0–AT27, AT-W) | The full 14-column angle tower |
| 15 | Bishop-Gromov + log V(r) (AT9) | Scalar curvature |
| 16 | Cellular metric tensor (AT21) | Bilinear-form-at-point structure |
| 17 | Connection 1-form (AT22) | Christoffel / parallel transport |
| 18 | Curvature 2-form (AT22) | Riemann tensor |
| 19 | Solid angle (AT19), Regge deficit (AT20) | Higher-dim curvature |
| 20 | Tangent bundle (IG9) + connection (IG3) + holonomy (IG5) | Full Riemannian / Lorentzian / gauge structure |
| 21 | Fisher metric (IQ5) + Bures angle (AT13) | Quantum / information-geometric structure |
| 22 | Continuum limit + units (AT11) | Smooth differential geometry |
| 23 | Specific GR metrics (#25–#29) + EFE (#62) | General relativity |
| 24 | Spin networks (POLY3) + LQG bridge (#98) | Quantum gravity |
| 25 | BBH from hypergraph (#80–#83) | THE ENDGAME — actual binary-black-hole merger from a discrete combinatorial substrate |

Each step is one short Lean definition or one bridge theorem on top of the previous. Nothing is hand-waved; every layer has a corresponding task. **This IS the constructive route Stephen is calling out: "all the way to differential geometry".** And on past it to GR, QM, and the BBH merger that motivates the program.

## 5g. Cross-reference with Murzin "Geometry on Combinatorial Objects" (2026-04-26)

Nikolay Murzin's 11-page paper *"Geometry on Combinatorial Objects: From Angle Defect to Cellular Sheaves"* (Wolfram Cloud, dated today, almost certainly the in-progress write-up of the Stephen-Pavel-Nik meeting we tracked) provides an external classification we should align against.

**Coverage alignment (~60-70% of the document maps to existing tasks):**

| Murzin section | Our coverage |
|---|---|
| §2.1 Descartes / Gauss-Bonnet defect; Regge action | AT2 (#287); AT20 (#307); KnillCore Euler-char ✓ |
| §2.2 Knill recursive `K(v) = Σ(−1)^k V_{k-1}(v)/(k+1)` | KN13 (#249), SURFACE1 (#348) ✓ |
| §3.1 Forman-Ricci `F(e) = 4 − deg(u) − deg(v) + 3·#triangles` | `DiscreteRicci.formanRicciHypergraph` ✓ |
| §3.2 Ollivier-Ricci | #220 ✓, AT12 (#297) ✓ |
| §3.4 Bishop-Gromov ball-growth | AT9 (#294), SPHERE4 (#337) ✓ |
| §4 DEC (cochains, coboundary, δ² = 0, Hodge decomp) | KnillCore d, d*, D, H = D²; #277 ✓ |
| §4 Lim's Hodge Laplacians on graphs | IT3, HodgeLaplacianBounds, HodgeVR ✓ |
| §6 Cellular sheaves | CELL1 (#315) ✓ logged |
| §6.3 Lattice gauge sheaf example | IG3-IG7, DiscreteGaugeField ✓ (but not in sheaf framing — see SHEAF-CHOICE6 #356) |

**Gaps logged as new tasks (#351–#368):**

- **§7 — Choosing-restriction-maps classification** (the document's structural payoff): SHEAF-CHOICE1–7 (#351–#357) for constant / Hodge / `S_k`-equivariant / diffusion / order / gauge / tensor-contraction sheaves; SHEAF-CLASSIFICATION (#358) for the meta-table mapping structural commitments to canonical sheaf-types.
- **§3.3 Effective-resistance curvature** (Devriendt-Lambiotte 2022) — EFFRES1 (#359) — third independent curvature notion between Forman and Ollivier on the trade-off curve.
- **§4 explicit Hodge star ⋆** between primal/dual cochains — DEC1 (#360).
- **§4 explicit wedge product ∧** on cochains — DEC2 (#361) — required for AT22 Cartan structure equations.
- **§5 Closure problem** (downward / clique / nerve as explicit choices) — CLOSURE1 (#362).
- **§6 Hansen-Ghrist sheaf-Cheeger inequalities** — CHEEGER1 (#363).
- **§2.1 Christiansen 2024 distributional → smooth scalar curvature** in Regge — REGGE-CONV1 (#364).
- **§2.2 CDT** (Causal Dynamical Triangulations) — CDT1 (#365).
- **§2.2 Stone's discrete Myers** — MYERS1 (#366).
- **§2.2 Higuchi planar-graph curvature** — HIGUCHI1 (#367).
- **§3.2 Ollivier-Ricci hypergraph multi-marginal** (Eidi-Jost 2020) — OLLIVIER-HG (#368).

**The document's central thesis** — *"every geometric construction on a combinatorial object corresponds to a specific structural commitment, and cellular sheaves make this commitment explicit"* — IS exactly the synthesis Stephen and Pavel converged on in the meeting we tracked. The §6.3 lattice-gauge-sheaf example IS Pavel's "string theory on the graph"; the §7 restriction-map classification IS the categorical-organisation layer that makes all our angle / curvature / topology choices explicit. **Our task list now subsumes the document's full coverage** — every concept it identifies has either a corresponding existing infrastructure or a logged task.

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
