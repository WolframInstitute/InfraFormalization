# Infrageometry: research programme and Lean coverage

Status labels in this file: PROVED, PROVED-WITH-NATIVE-DECIDE, VACUOUS, READ, OPEN, as in [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md), and DEFINED for a Lean definition with no theorem attached. Per-theorem axiom lists are in [`THEOREM_STATUS.md`](THEOREM_STATUS.md).

## 1. What infrageometry is

Infrageometry is the study of the intrinsic geometry of hypergraphs arising in hypergraph rewriting. It treats the Wolfram Physics Project as reconstruction, the inverse of discretisation: a small hypergraph is consistent with many continuum geometries, and rewriting narrows the set. Smooth structure is expected only in the limit of many updates.

Relation to other programmes:

- G1 treats the metric as determined by the hypergraph. Infrageometry allows a small graph to support several geometries and treats scale-dependent behaviour as expected.
- Diffusion geometry is probabilistic. Infrageometry uses exact combinatorial constructions. The two are complementary.
- Causal-set theory treats the discrete set as a sample of a Lorentzian manifold. Infrageometry uses the sprinkling language and the Benincasa-Dowker action but treats the discrete structure as fundamental.
- Lattice gauge theory works with labelled lattices. Infrageometry works at the unlabelled combinatorial scale and treats labelled mesoscale graphs as the target of coarse-graining.

## 2. Named subprojects

| Programme | Scope | Work by colleagues | Lean coverage |
|---|---|---|---|
| Synthetic infrageometry | Axiomatic construction of lines, circles, subspaces and spheres on hypergraphs; `InfrageometricScene` for multiple constructions; Hausdorff distance on the branchial graph of construction instances | `SyntheticInfrageometry` paclet (PHAJEK): extremal orthogonal axes, coordinatization via intersections of spheres | `SyntheticGeometry.lean`, `SyntheticAxiomatic.lean`, `InfrageometricScene.lean` (DEFINED). Group IS. |
| Infracausality | Axiomatic special relativity from causal graphs: observer chains, light rays, spatial reconstruction, Cauchy foliations, Ehlers-Pirani-Schild axioms, Marzke-Wheeler clocks | "Axiomatic Relativity from Causal Graphs" paper in progress (CZAPATA, SAHMED); EPS identified as the scheme closest to the discrete setting | `CausalGraphType.lean`, `CausalFoliation.lean`, `EPSAxioms.lean`, `MarzkeWheeler.lean`, `SpatialReconstruction.lean`, `Infra/LorentzLattice.lean`, `Infra/ScaledLorentz.lean`. Group IC. |
| InfraGaugeTheory | Fibred graphs, sections, connections, parallel transport, Wilson loops, holonomy, moduli of connections | `InfraGaugeTheory` paclet (`PacletInfo` `Creator`: Pavel Pokorny; git committer: PHAJEK): `RandomFiberedGraph`, `ConnectionQ`, `HolonomyMatrix`, `FlatConnectionQ`, `FindHorizontalLeaf`, `GraphTangentBundle` | `FiberedGraph.lean`, `Holonomy.lean`, `FiberBundle.lean` (DEFINED). Group IG. |
| Infraanalysis | Multivariate calculus on graphs coordinatized by bundles of directed acyclic subgraphs; renormalisation via blowups; integration map from forms to cochains | `InfraAnalysis` paclet (PHAJEK): 1D calculus on directed graphs as blowups of ℝ; cotangent bundle and de Rham complex in progress | `DiscreteCalculus`, `DiscreteCalculusSymm`, `HypergraphCalculus`, `LaplacianBridge`, `HypergraphCycleBridge`, `DagBlowup`, `DagCalculus`, `DeRham`, `FormCochainIntegration`. Group IA. |
| Ruliology and EME tracking | Catalogue rules by geometric signature; track vertex lifetimes across multiway branches | Community paper in preparation; `HypergraphRewritingEngine` (RASSAR) for multiway evolution | `RuleSignature.lean`, `StructuralRuleBounds.lean`, `EMETracker.lean`. Group IR. |

## 3. Technical primitives from colleagues' work

### Dimension

- Wolfram-Hausdorff dimension: `d(v) := lim_{r→∞} log V_v(r) / log r`, where `V_v(r)` is the number of vertices within graph distance `r` of `v`. A plateau across a range of scales gives the dimension. Small `r` shows local irregularity and large `r` shows finite size.
- Homology dimension: the top Betti number that persists across a plateau of scales of the Vietoris-Rips complex.
- Coordinatization dimension: the number of extremal orthogonal axes that coordinatize a neighbourhood. It distinguishes compact from non-compact directions.
- Causal-graph dimension: from longest-antichain and foliation-thickness analysis of the causal graph.
- Rule dimension: the dimension a rule tends to produce.
- Compatibility: the notions are expected to agree for admissible rules, and disagreement marks pathological cases.

### Topology

- Latschev's theorem (cited): for a closed Riemannian manifold M there is ε₀ such that for every ε < ε₀ there is δ such that every metric space X with d_GH(X, M) < δ has a Vietoris-Rips complex VR_ε(X) homotopy equivalent to M.
- Application: from a hypergraph, take the clique complex, compute VR_ε at ε = 1, 2, ..., and read the topology of a limiting manifold from the persistence barcode.
- Scale dependence: below a scale ε₁ the complex is discrete; between ε₁ and ε₂ its homology matches the expected topology; above ε₂ it collapses.
- Hodge Laplacian on VR: spectral invariants of the vertex and edge Gram matrices. Oriented versions support a discrete Chern-Simons theory (IBL-∞).

### Fibred and gauge constructions

- Fibred graph: a total graph with a projection to a base graph. Vertical edges lie in fibres and horizontal edges are transverse.
- Fibre-bundle predicate `FiberBundleQ`: isomorphic fibres, edge-lifting property, at most one edge lift, and trivial holonomy on cycles in each vertex neighbourhood.
- Connection: a subgraph of transverse edges with unique edge lifting (`AtMostOneEdgeLiftQ`) and completeness.
- Section: a map from base to total with `proj ∘ section = id`. Smooth when it respects adjacency.
- Parallel transport along a base path: the fold of horizontal lifts.
- Holonomy matrix: the permutation matrix around a loop. `HolonomyMatrices` covers a cycle basis.
- Wilson loop: the trace of the holonomy.
- Flat connection: trivial holonomy on every loop.
- Tangent bundle `GraphTangentBundle[g, r]`: fibres are `r`-neighbourhoods, horizontal edges are maximal transverse bipartite matchings.
- Exponential map (proposal): `exp_v(e) = Σ_u [(#shortest paths v→u starting with e) / (#shortest paths v→u)] · u`.

### Infracausality

- An observer is modelled by a causal edge.
- Spatial closeness is modelled by a shared immediate common ancestor.
- A foliation is a decomposition into successive antichains, the analogue of Cauchy surfaces.
- A light ray from p is a subgraph in which the causal interval [p, q] is degenerate for every q on the ray.
- The spatially reconstructed hypergraph joins events of one foliation slice that share an immediate common ancestor in the previous slice.
- Shortest-path projections are not unique, so one fibre element can lie over several base points. The resulting structures are multi-fibrations.
- Candidate proper time: the longest-path foliation.
- Further targets: event horizons, inertial frames, Lorentz transformations, mass, the EPS scheme, Marzke-Wheeler clocks on transitively reduced causal graphs.

### Branchial and quantum

- Branchial graph at step n: states with an immediate common ancestor.
- Connected components are superposition classes. A self-adjoint adjacency operator gives a Hilbert space in the limit.
- Elementary blowups are rules with a single-hyperedge LHS. Their commutator has no causal-branchial component, so they form a Lie algebra on isomorphism classes of hypergraphs.
- Blowups of unary edges form the insertion Lie algebra of perturbative QFT. A graded version exists.
- A Poisson bracket on formal functions gives Hamiltonian mechanics on the ruliad, with canonical functions #V and #E.
- Moduli of connections give path-integral weights through causal-branchial time evolution.
- The Fisher metric on the branchial graph is expected to give the Fubini-Study metric in the limit (HVLE).

### Synthetic

- Synthetic Euclidean analogues: a circle is the set of points equidistant from a centre, a line is a set of shortest-path centres, and spheres, cylinders and planes are built similarly.
- Fréchet eccentricity selects canonical straight lines.
- An ensemble of constructions is treated as a branchial object with the Hausdorff metric.
- An axiomatic formulation is planned.

## 4. Lean coverage

### PROVED results

- Hypergraph calculus: linearity, self-adjointness and the Dirichlet inequality for `laplacianHyper`; Σ Δf = 0; `hyperedgeGradient`, `hypergraphDiv` and `summation_by_parts`; discrete Stokes `stokes_zero_to_one` (`DeRham.lean`).
- PDEs on `Hypergraph V`: heat equation (existence and forward uniqueness, mass conservation, L² decay, decay of non-constant cycle modes), wave equation (energy conservation), Klein-Gordon (energy conservation), Schrödinger (probability conservation), scalar-field Euler-Lagrange equation (`KG_EulerLagrange_iff_KleinGordonSolution`).
- Cycle family: matrix Laplacian, heat kernel `exp(t·Δ)`, eigenvalue equation and the limit n²·λ_k(n) → −(2πk)² (`cycleEigenvalue_scaled_tendsto`); C² convergence of the scaled second difference to f'' (`scaledSecondDiff_tendsto_iteratedDeriv_C2`).
- Fixed-family approximation bounds: an isometric embedding with 1/(2n)-dense image for the scaled cycle in ℝ/ℤ (`Infra.cycle_circle_gh_bound`), the path in [0, 1] (`Infra.path_interval_gh_bound`), the n×n lattice in the 2-torus (`Infra.torus_gh_bound`) and the (Fin n)^(d+1) lattice in the (d+1)-torus (`Infra.dTorus_gh_bound`); preservation of causal order by the embedding of the integer Lorentz lattice in Minkowski space (`Infra.lorentzIntEmbed_preserves_causal_iff`, `Infra.scaledLorentzEmbed_preserves_causal_iff`).
- Infracausality: `stablyCausal_hasFoliation`, `mwClock_implies_causallyPrecedes`, `eps_worldline_not_light`. `CausalGraph V` (transitively reduced DAG), `IsFoliation`, `spatialReconstructionAdj`, `EPSAxioms` and `MWClock` are DEFINED.
- Causal histories (`CausalHistory.lean`): an identity is consumed by at most one event; the out-degree of an event is at most the number of identities it creates; for |LHS| = |RHS| = k with N initial hyperedges, k·|A| ≤ N for every antichain A; for the rule of G3 line 6202, 4·|A| ≤ N (`CausalHistory.gorardNamedRule_antichain_card_le`) and at most 5^t events within directed distance t of an event (`CausalHistory.gorardNamedRule_ball_card_le`). These hold for every update order.
- Hypergraph connection: `transportWalk_append` for `HypergraphConnection H G`.
- Dimension: `dimensionCompatibilityObligation_holds`, V(v, r) = 2r + 1 on `cycleHypergraph n` for 2r + 1 ≤ n (ID6). Rodkey chain on cycles: `cycleHypergraph_rodkey_chain` (`RodkeyClassification.lean`), with `AdjTransitive → DistTransitive → BallVolumeVertexUniform → LocalDimensionVertexUniform`, and `pathHypergraph_not_ballVolumeVertexUniform`.
- Topology: `latschevObligation_holds` states that distances on `cycleHypergraph n` are less than n + 1; it does not state Latschev's theorem. `scaleTrichotomyObligation_holds` covers the scales ε = 0 and ε = n on cycles. `vrHodge0_has_zero_eigenvalue`, `vrHodge0_symm` for the VR Hodge Laplacian on 0-forms.
- Ruliology: edge-count invariance for conservative rules (`RuleSignature.edgeCount_invariant_of_conservative`, `trajectory_size_invariant`). `not_reverseEngineeringObligation` proves that the unrestricted reverse-engineering statement is false. `reverseEngineeringObligationRefined_holds` holds with the zero-step trajectory of the empty rule list starting at the target hypergraph.
- Branchial and quantum: self-adjointness of the slice adjacency (`branchialAdjLM_inner`), probability conservation (`branchialSchrodinger_unitary_evolution`), expectation values (`expectationValue_re_of_symm`), `branchial_qm_is_rewriting_grounded`. `fubiniStudyBhattacharyya_bound` is the inequality |⟨ψ, φ⟩| ≤ Σ_s |ψ_s|·|φ_s|. `EMEPersistenceObligation` and `PathIntegralObligation` are PROVED with the zero vector and the zero amplitude.
- Continuum targets in local coordinates: Schwarzschild Christoffel symbols on the exterior, FLRW Christoffel symbols and Ricci components (`FLRWRicci.lean`), Reissner-Nordström lapse identities, `warpedDiag2_einstein`, `minkowski4_satisfies_vacuum_EFE`.
- Bundle-level metric predicates: `euclidean_diagRiemannian`, `minkowski4_diagLorentzian`.
- Coefficient comparisons with the literature: `Infra.ollivier_minus_gorard_leading`, `Infra.ollivier_gorard_agree_iff`, and the S² case `Infra.s2_gorard_error` (difference δε²/8); `Infra.gray_vs_gorard_disagree_on_S2`, `Infra.gray_vs_gorard_disagree_on_S3`.

### DEFINED

- Fibred graphs: `FiberedGraph`, `IsSection`, `FiberedGraph.Connection`, `ParallelTransportList`, `Holonomy`, `wilsonLoop`, `IsFlatConnection`, `IsFiberBundle`, `GraphTangentBundle`, `MultiFiberedGraph`.
- Dimension: `IsPlateau` (ID2), `HasNontrivialHomology` (ID3), `HasCoordinatizationDim` (ID4), `HasChainToDepth` (ID5).
- Topology: `VietorisRipsEdge`, `VietorisRipsSimplex`, `vietorisRipsGraph`, `PersistenceBarcode`, `firstBettiZ`, `spatialB0`, `IsSpatiallyConnected`.
- Ruliology: `RuleSignature V`, `hypergraphSignature`, `RewritingSystem.ProducesTrees`, `RewritingSystem.ProducesPlanar` (via the necessary condition |E| ≤ 3|V| − 6), `IsDirectConcatSystem`, `IsProductSystem`. No dimension bound for tree-producing, planar or product rules is proved.
- Blowups: `ElementaryBlowup`, `BlowupLieAlgebraStructure`, `PoissonBracket`, radial and laminar blowups. `ElementaryBlowup.CommutatorVanishesCausalBranchial` is a predicate; the commutator theorem (IB2) is OPEN.
- Synthetic: `SyntheticCircle`, `SyntheticLineSegment`, `SyntheticSphere`, `InfrageometricScene`, `Between` and the axioms of `SyntheticAxiomatic.lean`.
- Angles and metric primitives (`HypergraphDistance.lean`): `Hypergraph.elementaryAngle` (AT0), `cosAngle` (AT1), `IsOrthoApprox` (AT6), `GeodesicallyUnique` (AT8), `infraSphere`, `infraDisk`, `perpBisector`, `voronoiCell`, `midpoint`, `nearMidpoint`, `HasTopologicalHyperplane`. `Hypergraph.scalarCurvatureAt` (AT9, `DiscreteRicci.lean`). `AngularScreener`, `CombinedScreener` (AT7, `RuleSignatureScreener.lean`).

### VACUOUS

- Origin obligations. `HypergraphMetricOriginObligation`, `HypergraphMetricOriginObligationStrong`, the partial-metric forms, `ConnectionDataOriginObligation`, `LorentzianManifoldOriginObligation`, `HypergraphQuantumOriginObligationStrong` and `HypergraphBBHOriginObligationStrong` do not depend on their target and hold for every target (`Curvature.any_metric_has_strong_obligation_witness` and the corresponding theorems). `EFEOriginObligation` is equivalent to `EinsteinEqLambda` (`Curvature.EFEOriginObligation_iff_EinsteinEqLambda`), so `minkowski4_flat_vacuum_EFE_originated_global` is the flat-vacuum Einstein equation with VACUOUS origin clauses. The Milestone Props are satisfied by the zero discrepancy; `Milestone.GR_emerges_from_hypergraph_holds` proves `GR_emerges_from_hypergraph target` for every target. Details: [`BRIDGE_MACHINERY.md`](BRIDGE_MACHINERY.md).
- `all_obligations_hold` (`RemainingObligations.lean`) bundles ID6 (PROVED with content), the scale endpoints of IT6, the inequality of IQ6, the zero witnesses of IQ8 and IQ9, and the trivial witness of refined IR7.

### Lean files on G1-G4

- F3 and F4: PROVED by `Iff.rfl` about the project's encodings (`asymptoticDimPreservation_iff_eulerLagrange`, `causalInvariance_iff_discreteGeneralCovariance`).
- F1, F2, F5, F6: VACUOUS with respect to the papers. They state facts about function types, `Bool`, the sequence 1/(n+1) and a restated hypothesis.
- F7: PROVED edge-count conservation for the rule of G3 line 6202; the causal-graph bounds are in `CausalHistory.lean` (above).
- The findings about the papers are READ findings with line numbers; see [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md).

### Partial

- A6: lattice Riemann sums converge to the integral for polynomials of degree at most 3 (`A6Holds_poly_deg3`, PROVED). OPEN for every continuous function.
- D6: decay to the constant mode on cycles is PROVED for finite eigen-combinations. OPEN for arbitrary initial data.

### OPEN

- IG10: exponential map via weighted shortest-path counts.
- ID7: small-t heat-trace asymptotics for spectral dimension.
- C3-C8: covariant derivative on smooth sections, Levi-Civita existence and uniqueness (Koszul formula), convergence of scaled discrete connections to Levi-Civita.
- Curved GR: Schwarzschild and Kerr Ricci tensors and vacuum Einstein equations; FLRW Einstein equations with perfect fluid; second Bianchi identity; Ricci symmetry for a general Levi-Civita connection.
- G2: discrete gauge field.
- E5-E7: ADM decomposition, Lorentzian Gromov-Hausdorff distance, convergence of discrete causal graphs to a Lorentzian manifold.
- D11: Cauchy problem for the Einstein equations (Choquet-Bruhat 1952).
- A7, A8: W₁ convergence rate, d-torus measure lift.
- I8, I10: continuum limit of branchial Hilbert spaces, path-integral formulation.
- Linear cone growth for the rule of G3 line 6202, stated as `CausalHistory.GorardNamedRuleConeGrowthLinear`.

## 5. Lean task groups

Each group lists its items in dependency order.

### Group IA. Infraanalysis

- IA1. `dagAsBlowupOfInterval`: `Fin n` with the linear orientation as a 1D-coordinate blowup of [0, 1]. DEFINED.
- IA2. Calculus on coordinate DAGs: `dagDerivative`, `dagPrefixSum`, fundamental theorem.
- IA3. De Rham complex on `Hypergraph V`: 1-forms, 2-forms, `d`, `d² = 0`.
- IA4. Integration map from forms to cochains on the clique complex.
- IA5. Blowup operator `Hypergraph V → Hypergraph W` commuting with calculus up to O(1/n).
- IA6. Scaled second difference → f'' for C² functions. PROVED (`scaledSecondDiff_tendsto_iteratedDeriv_C2`).
- IA7. Uniform convergence on C^k compacts. OPEN.

### Group IG. InfraGaugeTheory (port of the `InfraGaugeTheory` paclet)

- IG1. `FiberedGraph V W` with projection `π : V → W`.
- IG2. Sections: `σ : W → V` with `π ∘ σ = id`.
- IG3. Connections with at most one edge lift.
- IG4. Parallel transport along a base path.
- IG5. Holonomy on a loop.
- IG6. Wilson loop as the trace of the holonomy.
- IG7. Flat-connection predicate.
- IG8. Fibre-bundle predicate.
- IG9. `GraphTangentBundle` as a fibred graph.
- IG10. Exponential map via weighted shortest-path counts.
- IG11. Multi-fibrations: `MultiFiberedGraph` with multi-valued `π`.

### Group IC. Infracausality

- IC1. `CausalGraph` as a transitively reduced DAG.
- IC2. Observer chains.
- IC3. Light rays as degenerate-interval subgraphs.
- IC4. Foliations by successive antichains; proper time as longest-path height.
- IC5. Spatially reconstructed hypergraph from a causal graph and a foliation.
- IC6. Multi-fibration from non-unique shortest-path projection.
- IC7. EPS axioms as Props: light structure, particle structure, compatibility.
- IC8. Marzke-Wheeler clock and a determinism theorem.
- IC9. Lorentz transformations for scaled causal DAGs converging to Minkowski space.
- IC10. Curved targets, with `SchwarzschildObligationMet` as the model statement.

### Group IT. Infratopology

- IT1. `VietorisRipsComplex (H : Hypergraph V) (ε : ℕ)`.
- IT2. Hodge Laplacian on 0-forms and 1-forms of VR.
- IT3. Spectrum of the Hodge Laplacian.
- IT4. Persistence diagram.
- IT5. Betti numbers of VR_ε.
- IT6. Latschev's theorem as a Prop, with a proof for cycle → S¹. The current `LatschevObligation` is a distance bound and does not state Latschev's theorem.
- IT7. The scale trichotomy as a theorem about the Betti-number function of ε.

### Group ID. Infradimension

- ID1. Wolfram-Hausdorff dimension at a vertex.
- ID2. Plateau detection over a range of radii.
- ID3. Homology dimension from the top persistent Betti number.
- ID4. Coordinatization dimension via extremal orthogonal axes.
- ID5. Causal-graph dimension from longest-antichain analysis.
- ID6. Compatibility on regular lattices. PROVED for cycles (`dimensionCompatibilityObligation_holds`).
- ID7. Rules on which the notions disagree.

### Group IB. Blowups and renormalisation

- IB1. `ElementaryBlowup`.
- IB2. The commutator of two blowups on isomorphism classes, with vanishing causal-branchial component for single-hyperedge LHS. OPEN.
- IB3. `BlowupLieAlgebraStructure`.
- IB4. Insertion Lie algebra for unary edges and its isomorphism with the pQFT insertion algebra.
- IB5. Poisson bracket on ℝ[#V, #E]; Hamiltonian vector fields.
- IB6. Radial and laminar blowups commuting with calculus up to O(1/n).
- IB7. Graded version.

### Group IQ. Branchial and quantum

- IQ1. Finite branchial slices.
- IQ2. Branchial ℓ² Hilbert space.
- IQ3. Unitary evolution.
- IQ4. Amplitudes and observables.
- IQ5. Fisher metric on the branchial graph.
- IQ6. Fubini-Study metric as the limit of the Fisher metric on refined branchial graphs. OPEN; the current `FubiniStudyLimitObligation` is a triangle inequality.
- IQ7. Branchial continuum limit to a Hilbert space. OPEN.
- IQ8. EME tracking: persistence of a vertex across multiway branches as an observable.
- IQ9. Path integral as a sum over single-way causal-graph classes.

### Group IS. Synthetic infrageometry

- IS1. `SyntheticCircle`, `SyntheticLineSegment`, `SyntheticSphere`.
- IS2. `InfrageometricScene`.
- IS3. Branchial structure on scenes with the Hausdorff metric.
- IS4. Euclid-style axioms.
- IS5. Incidence, collinearity and concurrency theorems.
- IS6. Tropical-geometry translation.

### Group IR. Ruliology

- IR1. `RuleSignature`: dimension, growth and curvature data of a rule.
- IR2. Edge count is constant for |LHS| = |RHS|. PROVED (`trajectory_size_invariant`). A dimension bound for such rules is OPEN.
- IR3. Tree-producing rules have dimension log(branching). OPEN.
- IR4. Planar rules have dimension at most 2. OPEN.
- IR5. Candidate-rule database and screening.
- IR6. Dimension additivity for product rules under confluence. OPEN.
- IR7. Computable hypergraph invariants as a Lean-checkable list.

### Group KN. Knill quantum calculus (#237-#256)

Lean formalisation of Knill's discrete-geometry programme as catalogued in [`resources/Infrageometry/QuantumCalculus.md`](resources/Infrageometry/QuantumCalculus.md). Each task has a Mathematica counterpart in [`resources/Infrageometry/Infrageometry/Kernel/QuantumCalculus.wl`](resources/Infrageometry/Infrageometry/Kernel/QuantumCalculus.wl) (290 lines; functions `WaveEquationSolution`, `WuCharacteristic`, `IsospectralDeformation`, `DiracZetaFunction`, `IndexExpectationCurvature` and others).

Knill's programme gives each continuum concept a combinatorial counterpart on finite abstract simplicial complexes, delta sets or quivers. Order-blind (bosonic) and orientation-aware (fermionic) invariants are tracked separately. The McKean-Singer symmetry of H = D² between even and odd forms gives both Euler-Poincaré and Brouwer-Lefschetz.

- KN1. d'Alembert solution `u(t) = cos(D t) u₀ + t · sinc(D t) v₀` via matrix functions of the Dirac matrix.
- KN2. Discrete-time wave step (leapfrog) and the unitary propagator `exp(i D t)`.
- KN3. Wu characteristic `ω_m(G) = Σ_{x_1 ∩ ⋯ ∩ x_m ≠ ∅} ω(x_1) ⋯ ω(x_m)` and Wu cohomology. PROVED: `wuCharacteristic₂_eq_chi_sq_sub_disjoint`.
- KN4. Isospectral Lax deformation `D' = [d − d*, D]` with the extracted diagonal mass term.
- KN5. Connes spectral distance `d(x, y) = sup{|f(x) − f(y)| : ‖[D, f]‖ ≤ 1}` and its relation to `Hypergraph.dist`.
- KN6. Connection matrix `L(T)` and Green function `g(T) = L(T)⁻¹`; unimodularity `det(L) = ±1`; energy theorem `Σ g(x, y) = χ(H)`; hydrogen operator `L − L⁻¹` in 1D.
- KN7. Index-expectation, sectional, form and boundary curvature.
- KN8. Dirac, connection and Lefschetz zeta functions; the dyadic Riemann hypothesis for circular graphs.
- KN9. Analytic torsion `log T(H) = ½ Σ_k (−1)^{k+1} k · log det'(H_k)` and its behaviour under barycentric refinement.
- KN10. Wave-front exterior derivative and spherical-average non-local `d`.
- KN11. Geodesic gas and cellular-automaton geodesic evolution on triangulated 2D lattices.
- KN12. Delta sets and quivers: face-map exterior derivative, cohomology, Gauss-Bonnet, Brouwer-Lefschetz.
- KN13. Soft barycentric refinement and the Fisk-manifold predicate.
- KN14. McKean-Singer symmetry. PROVED ingredients: `KnillCore.dSquared_eq_zero`, `hodgeOnG_psd`.
- KN15. Atiyah-Singer and Atiyah-Bott analogues (Knill 1708.06070).
- KN16. Discrete Cartan formula `L_X = i_X d + d i_X` (Knill 1811.10125).
- KN17. Bosonic and fermionic invariants as separate types.
- KN18. Brouwer fixed-point theorem for graph endomorphisms via the Lefschetz number (Knill 1206.0782).
- KN19. Deformed exterior derivatives `d_h`, h ∈ ℝ (Knill 1306.5597).
- KN20. Level sets and Euler characteristic (Knill 2401.07435). PROVED ingredient: `eulerCharacteristic_eq_alt_sum_kSkeleton`.

Knill papers (catalogue in `QuantumCalculus.md` §5):

| arXiv | Year | Topic |
|---|---|---|
| [1206.0782](https://arxiv.org/abs/1206.0782) | 2012 | Brouwer fixed point (KN18) |
| [1205.0306](https://arxiv.org/abs/1205.0306) | 2012 | Index expectation curvature (KN7) |
| [1301.1408](https://arxiv.org/abs/1301.1408) | 2013 | Discrete supersymmetry, McKean-Singer (KN14) |
| [1306.5597](https://arxiv.org/abs/1306.5597) | 2013 | Deformed exterior derivatives (KN19) |
| [1312.4239](https://arxiv.org/abs/1312.4239) | 2013 | Zeta functions of circular graphs (KN8) |
| [1708.06070](https://arxiv.org/abs/1708.06070) | 2017 | Atiyah-Singer and Atiyah-Bott in finite geometry (KN15) |
| [1801.04639](https://arxiv.org/abs/1801.04639) | 2018 | Elementary dyadic Riemann hypothesis (KN8) |
| [1811.10125](https://arxiv.org/abs/1811.10125) | 2018 | Discrete Cartan formula (KN16) |
| [2205.14097](https://arxiv.org/abs/2205.14097) | 2022 | Graphs, groups and geometry |
| [2401.07435](https://arxiv.org/abs/2401.07435) | 2024 | Level sets and Euler characteristic (KN20) |
| [2501.14611](https://arxiv.org/abs/2501.14611) | 2025 | Wave front density conjectures (KN10) |

### Group IGE. Lean port of the `Infrageometry` paclet (#257-#261)

The paclet `resources/Infrageometry/Infrageometry/` is the Wolfram Language implementation of the Knill and infrageometry toolkit (Creator: NMURZIN). The IGE group ports it module by module.

- IGE1. `Infrageometry.wl` core (351 lines): `complexClosure`, `simplexCardinalities`, `complexEulerCharacteristic`, `complexFermiCharacteristic`, `simplexUnitSphere`, `simplexStar`, `simplexCore`, `complexIncidenceMatrix`, connection matrix `L`, Green function `g = L⁻¹`, Dirac matrix `D = d + d*`, Hodge matrix `H = D²`, `bettiVector`, `lefschetzNumber`, `lefschetzCurvature`, `simplicialMap`, `complexPolynomial`, `dehnSommervilleQ`, `barycentricRefinement`, `faceGraph`, `superTrace`, `superDeterminant`, `pseudoDeterminant`, `complexJoin`, `complexDual`.
- IGE2. `SimplicialSet.wl` (315 lines, PHAJEK): face and degeneracy maps, delta-complex morphisms.
- IGE3. `TDA.wl` (242 lines): Vietoris-Rips, Čech, persistence.
- IGE4. `Mesh.wl` (248 lines): mesh generation and refinement; geometric realisation of a hypergraph.
- IGE5. `Chains.wl` (63 lines): integer chain complex of simplices.

### Group SIG. Synthetic infrageometry, expanded (#262-#266)

Module-level ports of the [`resources/SyntheticInfrageometry/`](resources/SyntheticInfrageometry/) paclet (PHAJEK), with the branching-stability questions from its README.

- SIG1. `Tools.wl`: constructions `Line`, `Ray`, `Segment`, `Perpendicular`, `Parallel`, each producing a multiset of `InfrageometricScene`s.
- SIG2. `Postulates.wl`: Euclid-style axioms as Props on a hypergraph and scene. Question: for which rules r do the postulates hold on every state of `singleWayEvolve r seed n`?
- SIG3. `Predicates.wl`: `collinear`, `concyclic`, `perpendicular`, `congruentSegment`, `betweenness`, decidable on finite hypergraphs.
- SIG4. `Coordinatization.wl`: analytisation of synthetic infrageometry via shortest-path counts and Cayley-style embeddings; relates ID4 and IGE1.
- SIG5. Stability of branching constructions: a distance between scenes and a predicate stating that branching scenes of a construction on the outputs of a rule converge under refinement. First instance: the subdivision rule on paths and cycles.

#### Design notes for SIG2 and SIG3

1. Tarski's axiomatisation of Euclidean geometry uses two primitive predicates, betweenness `B(a, b, c)` and equidistance `Cong(ab, cd)`. With `Hypergraph.dist` they are one-line definitions: `B a b c := dist a b + dist b c = dist a c` and `Cong a b c d := dist a b = dist c d`. `Hypergraph.Between` (`SyntheticAxiomatic.lean`) is DEFINED in this form, and `segment_is_between` (PROVED) identifies it with membership in `SyntheticLineSegment`. Tarski's axioms T1-T8 (incidence, congruence, segment construction) are then decidable Props on any finite hypergraph. SIG2 implements these in place of Euclid's five postulates.

2. Angles. Graph distance gives Tarski's first eight axioms. Angles, perpendicularity and parallel uniqueness need more structure. The angle tasks AT0-AT27 (#285-#314) and AT-W (#319) are organised by the structure each definition needs:

| Column | Structure needed | Definitions (task) |
|---|---|---|
| M, metric | `Hypergraph.dist` | chord ratio d(A,B)/d(O,A) for equidistant A, B, equal to 2 sin(θ/2) in the plane (AT0, SWOLF); law of cosines (AT1); Forman vertex defect 2π − Σ angles (AT2); Toponogov angle lim d(γ₁(r), γ₂(r))/r (AT3); Gromov product |
| S, spectral | Hodge `d, d*`, Dirac `D` | Knill-Connes angle ⟨df, dg⟩/(‖df‖·‖dg‖) (AT4); heat-kernel angle at scale t (AT17); cohomology angle |
| Y, synthetic | predicates | Tarski `Cong` (AT10); `AngleCong` via SAS (AT5); projective cross-ratio ½ log[A,B;C,D] (AT18) |
| T, transport | Wasserstein | Ollivier W₁ angle (AT12); optimal-transport direction |
| Q, quantum | `BranchialHilbert` | Hilbert and Bures angle (AT13); Maslov index (AT24) |
| L, Lorentzian | causal intervals | rapidity arctanh((Δt − Δx)/(Δt + Δx)) (AT14); cone-axis angle; Lorentzian GH angle |
| G, gauge | `FiberedGraph`, connection | holonomy angle arccos(tr Hol/2) (AT15); Wilson-loop phase; connection 1-form (AT22); curvature 2-form |
| I, information | `FisherMetric` | Fisher angle (AT16); Bregman; Kullback-Leibler |
| H, higher | k-tuples | solid angle (AT19); Regge deficit 2π − Σ dihedral angles (AT20); dihedral angle |
| K, conformal | conformal class | conformal class [g] (AT23); length-free angle theory; Lorentzian conformal structure |
| F, tensor | bilinear form | discrete metric tensor g_{ij}(v) (AT21); Riemann tensor; holonomy group |
| N, other | | tropical angle (AT27); p-adic; Cayley-graph character angle |
| C, scale | | angle as a function of radius (AT25); multi-scale signature |
| U, multivalued | non-unique geodesics | multiset of chord ratios (AT26); distribution over angles |
| W, sheaf | cellular sheaf | ⟨r₁, r₂⟩/(‖r₁‖·‖r₂‖) for restriction maps (AT-W) |

The projective cross-ratio (AT18) needs only `Between` and distance ratios and does not need unique geodesics. A conformal class (AT23) consists of angle data; a metric adds a length scale. Regge calculus uses deficit angles (AT20) as its curvature variable. SIG3's `perpendicular` predicate uses one definition from this table (AT4 or AT0 with tolerance √2) and the others serve as cross-checks.

3. Straight lines (SWOLF). SWOLF's position is that an angle at O needs a unique direction from O to each target, that is, a simple path. On a general hypergraph geodesics branch (IC6). Three responses: the chord ratio (AT0) is a number defined from `Hypergraph.dist` whether or not geodesics are unique, and its reading as an angle is gated on `Hypergraph.GeodesicallyUnique` (AT8); on hypergraphs without unique geodesics the angle is a multiset over geodesic choices (AT26); the projective cross-ratio (AT18) does not use straight lines.

4. Paths and walks (PATH1, PATH2). `SubdivisionPath.IsPathOf H vs` (a nodup vertex list with `H = pathEdges vs`) matches the simple-path notion but is tied to `ExecHG ℕ`. `SimpleGraph.Walk.IsPath` after `Hypergraph.toSimpleGraph` drops self-loops, merges multi-edges and loses which hyperedge a step used. `Hypergraph.dist` is Mathlib's `SimpleGraph.dist`, the length of a shortest walk, which equals the length of a shortest simple path. PATH1: a type `Hypergraph.SimplePath u v` carrying a nodup vertex list and the hyperedge sequence. PATH2: whether the hyperedge-aware distance equals `Hypergraph.dist`, given that clique expansion treats a hyperedge of arity at least 3 as a complete graph. PATH1 is a prerequisite for AT3, AT8, AT26 and the extraction of causal and branchial graphs (#228, #229).

5. Units. In a hypergraph, distance r and ball volume V(r) are both counts. A length scale a per step gives r_phys = a·r, V_phys = a^d·V in a flat regime of dimension d, and R_phys = a^(−2)·R. The exponent −2 of scalar curvature corresponds to the order of the curvature term in the expansion V(r) = Ω_d r^d [1 − R r²/(6(d+2)) + O(r⁴)]. This expansion gives the discrete estimator `Hypergraph.scalarCurvatureAt v d r := (6(d+2)/r²)·(1 − V/V_flat)` (AT9), with d from the Wolfram-Hausdorff dimension. Chord ratios (AT0) and normalised inner products (AT4) are dimensionless. AT11 is a record of the length scale and the unit-conversion maps, with the theorem that each count-level identity lifts to dimensional form by substitution. OPEN.

6. Postulate V. On a hypergraph, lines are maximal geodesics and branching geodesics give several parallels through a point. The question is for which rules the limit satisfies Postulate V. Proposed predicate: `ParallelUniqueAtRule sys s₀ := Tendsto (fun n => parallelMultiplicity (singleWayEvolve sys s₀ n)) atTop (𝓝 1)`, where `parallelMultiplicity H` is the largest number of geodesic parallels through a point not on a line. Not formalised.

7. Postulate II. Segments end at boundary vertices of a finite hypergraph, so segment extension fails there. Proposed predicate: every geodesic in state n extends to a geodesic in some later state. Expected to hold for the subdivision rule and to fail for fixed finite cycles. Not formalised.

8. Bachmann's groups of motions. Synthetic geometry can be axiomatised through a group of motions generated by reflections (Bachmann 1959). For graphs the motions are automorphisms. An alternative SIG implementation defines a predicate `GroupOfMotions H` in place of Tarski's axioms. It relates to group IG because `Aut(graph)` acts as a discrete gauge group.

9. Graph classes (OPEN for each class). Conjectures: on path-shaped hypergraphs (`pathHypergraph n`, subdivision trajectories) T1-T8, Pasch (T9) and parallel uniqueness (T11) hold, and segment extension fails at endpoints. On cycles and lattices T1-T10 hold, and T11 holds for large n. On hypergraphs produced by general rules T1-T8 hold and T11 fails. The research question is which property of a rule corresponds to which axiom holding in the limit.

10. Inputs for SIG2 and SIG3: `Hypergraph.dist` (`HypergraphDistance.lean`), the Hodge Laplacian (`KnillCore.lean`), `geodesicBall`, `IsPathOf` (`SubdivisionPath.lean`), `InfrageometricScene` and `MultiwayCausalGraph`.

## 5b. Topology before metric

SWOLF proposes that topological structure be built before metric, volume or region structure. The layers below use no `Hypergraph.dist` and no `geodesicBallVolume`.

Layer −1, connectedness (TOP4, #326). Four notions:

- Spatial: `H.toSimpleGraph.Connected`, on one state. `IsSpatiallyConnected` and `spatialB0` are DEFINED.
- Causal: directed, on events of one trajectory.
- Branchial: symmetric, on states sharing an ancestor in the multiway graph.
- Rewriting reachability: directed, on states connected by finitely many steps.

None implies another: spacelike-separated events are spatially but not causally connected, and sibling branches are branchially related but not mutually reachable.

Layer 0, cells and incidence: vertices, hyperedges, simplicial, Δ-complex and CW structures, computed per connected component.

Layer 1, paths: `Hypergraph.SimplePath u v` (PATH1, #300); hyperedge-aware against clique-expansion paths (PATH2, #301).

Layer 2, polygons: `Hypergraph.Polygon`, a cyclic sequence of segments with arbitrary `Finset V` intersections between consecutive segments (POLY1, #316); Euclidean polygons are the case where every intersection has one point. Cellular k-chains with sheaf coefficients (POLY2, #317). Spin networks and spin foams (POLY3, #318).

Layer 3, cellular sheaves (CELL1, #315): a cellular sheaf F on `Hypergraph V` with restriction maps F(σ) → F(τ) for τ ⊂ σ. Cycles sharing points correspond to equalizer conditions at the shared stalk. PHAJEK proposes reading closed strings as 1-cycles, interaction vertices as equalizers at common points, and worldsheets as cellular k-chains (§5d). The sheaf angle is column W of the angle table (AT-W, #319).

Layer 4, contractibility (CONTRACT1, #329): `Hypergraph.IsContractible γ`, in a static form (γ bounds a 2-cell) and a dynamic form (rewriting produces the 2-cell), and a scale-indexed form `IsContractibleAtScale γ r` given by the death time in the IT4 barcode.

Layer 5, elementary path moves: deformations (DEFORM1, #330: insertion and removal of backtracks, substitution across a 2-cell boundary or a hyperedge) and extensions (DEFORM2, #331: appending or prepending an edge). Together they generate a fundamental category. `SubdivisionPath` is a concrete extension scheme.

Layer 6, homotopy invariants: first Betti number b₁ = E − V + C (TOP1, #323; `firstBettiZ` DEFINED); higher Betti numbers via Hodge decomposition (TOP2, #324); π₁ (TOP3, #325); π_k (TOP5, #327); genus and crossing number (TOP6, #328).

Layer 7, linking: linking numbers and Borromean detection (KNOT1, #320); Massey products (KNOT2, #321); Yamada and Jones polynomials via coloured spin networks (KNOT3, #322).

Layer 8, hyperplanes and regions (PHAJEK, SWOLF):

- MEMBER1 (#346): decidable membership in `Finset V` and predicate-defined regions.
- HYPER1 (#338): vertex separators as pre-metric hyperplanes; Menger's theorem.
- HYPER2 (#339): perpendicular bisector {M | dist A M = dist B M}. `perpBisector` DEFINED.
- HYPER3 (#340): Voronoi decomposition. `voronoiCell` DEFINED.
- HYPER4 (#341): `perpBisector` ⊃ `IsGeodesicHyperplane` ⊃ `IsTopologicalHyperplane`.
- MIDPT1 (#342): midpoints, possibly several or none. `midpoint`, `nearMidpoint` DEFINED.
- POLYTOPE1 (#343): polytopes as cells of a hyperplane arrangement.
- INOUT1 (#344): inside and outside of a cycle, by contractibility, volume, orientation or causal future.
- BOUND1 (#345): boundedness and diameter in the four connectedness notions.
- COMPACT1 (#347): compactness of limits.
- SPHERE1-4 (#334-#337): infra-spheres and infra-disks. `infraSphere`, `infraDisk` DEFINED.

Layer 8b, surfaces (SURFACE1, #348): the shell `H.infraSphere O r` as an induced subhypergraph, and the Knill-Fisk recursive predicate: `IsFiskManifold n H` when every unit sphere is `IsFiskManifold (n−1)` and every unit ball is contractible. A tree's shell at positive radius is disconnected; a cycle's shell is two points (S⁰); the shell of the Z² lattice at large radius is a cycle. Tracking shell topology along a trajectory screens for rules that produce manifold-like hypergraphs. Relates to KN13 (#249).

Layer 8c, topologies (OPEN1, #349; NBHD1, #350): discrete, Alexandrov, metric, star, Vietoris-Rips-indexed and causal Alexandrov topologies; neighbourhood bases `{H.geodesicBall v r}`. A manifold-like hypergraph has neighbourhood bases that stabilise to disks; a tree does not.

Layer 9, reflection groups: reflections in perpendicular bisectors (HYPER2) generate an isometry group; translations and rotations are products of two reflections; a reflection-closed set gives a Coxeter group, a root system and a Lie algebra (IB5, #150).

The metric layer follows: `Hypergraph.dist`, balls, the angle table, curvature.

## 5c. Angle table

The angle table is in §5, design note 2. The tasks are AT0-AT27 (#285-#314) and AT-W (#319).

## 5d. Cellular sheaves and PHAJEK's string correspondence

The cellular-sheaf framework (CELL1) treats cycles with common points (SWOLF) and PHAJEK's proposed correspondence with string theory. Proposed correspondence:

| String-theory object | Hypergraph object |
|---|---|
| Closed string | 1-cycle in the cellular complex |
| Open string | Path with endpoints |
| Worldsheet | Cellular k-chain (k ≥ 2) with sheaf data |
| Interaction vertex | Equalizer at a common stalk |
| Pants diagram | Three cycles meeting at a common boundary loop |
| Loop amplitude | Higher-genus cellular cover |
| String field theory | Cellular sheaf with associative multiplication on stalks |
| D-brane | Distinguished 0- or 1-cell for open-string endpoints |
| Vertex operator algebra | Algebra structure on stalks at interaction points |

None of these correspondences is formalised.

## 5e. Order of primitives (SWOLF)

0. TOP4: connectedness in four forms.
1. PATH1: simple paths.
2. POLY1: cycles and generalised polygons.
3. CONTRACT1: contractibility, scale-indexed via VR.
4. DEFORM1, DEFORM2: elementary moves.
5. HOM1, HOM2: path homotopy as the equivalence closure of DEFORM1; fundamental groupoid.
6. TOP3: π₁.
7. TOP1: b₁ as the abelianisation of π₁.
8. TOP2, TOP5, TOP6: higher Betti numbers, π_k, genus.
9. KNOT1-3: linking, Massey products, knot polynomials.

## 5f. Planned route from hypergraphs to differential geometry (SWOLF)

SWOLF states the aim of reaching differential geometry from hypergraph primitives. Planned steps:

| Step | Adds | Yields |
|---|---|---|
| 1 | Hypergraph and connectedness | b₀ |
| 2 | Simple paths (PATH1) | Path category |
| 3 | Cycles (POLY1), cellular sheaves (CELL1) | Cycles with gluing data |
| 4 | Contractibility (CONTRACT1), moves (DEFORM1/2) | Path equivalence |
| 5 | Path homotopy (HOM1), groupoid (HOM2) | Fundamental groupoid |
| 6 | π₁ (TOP3), π_k (TOP5), Betti numbers (TOP1/2) | Algebraic topology |
| 7 | Linking, Massey products (KNOT1-3) | Twisted cohomology |
| 8 | Hyperplanes (HYPER1-4), midpoints (MIDPT1), polytopes (POLYTOPE1) | Synthetic primitives |
| 9 | Inside and outside (INOUT1), bounded and compact (BOUND1, COMPACT1) | Regions |
| 10 | Reflections in hyperplanes | Isometry group |
| 11 | Reflection-closed sets | Coxeter and Weyl groups |
| 12 | Linearisation at the identity | Lie algebra (IB5, #150) |
| 12.5 | Surface predicate (SURFACE1), neighbourhood bases (NBHD1), open sets (OPEN1) | Local Euclidean detection |
| 13 | `Hypergraph.dist` | Spheres (SPHERE1), Voronoi cells (HYPER3) |
| 14 | Angles (AT0-AT27, AT-W) | Angle table |
| 15 | Ball growth (AT9) | Scalar curvature estimator |
| 16 | Discrete metric tensor (AT21) | Bilinear form at a point |
| 17 | Connection 1-form (AT22) | Christoffel symbols, parallel transport |
| 18 | Curvature 2-form (AT22) | Riemann tensor |
| 19 | Solid angle (AT19), Regge deficit (AT20) | Higher-dimensional curvature |
| 20 | Tangent bundle (IG9), connection (IG3), holonomy (IG5) | Riemannian, Lorentzian and gauge structure |
| 21 | Fisher metric (IQ5), Bures angle (AT13) | Information geometry |
| 22 | Continuum limit and units (AT11) | Smooth differential geometry |
| 23 | GR metrics (#25-#29), Einstein equations (#62) | General relativity |
| 24 | Spin networks (POLY3), LQG comparison (#98) | Quantum gravity |
| 25 | Binary black holes from hypergraphs (#80-#83) | Binary black hole evolution |

Steps 13 to 15 have DEFINED primitives (`infraSphere`, `voronoiCell`, `elementaryAngle`, `cosAngle`, `scalarCurvatureAt`). Steps 22 to 25 have no PROVED result for any rewriting evolution.

## 5g. Cross-reference with NMURZIN, "Geometry on Combinatorial Objects" (2026-04-26)

NMURZIN's 11-page document "Geometry on Combinatorial Objects: From Angle Defect to Cellular Sheaves" (Wolfram Cloud, 2026-04-26) classifies geometric constructions on combinatorial objects. Its central statement is that each geometric construction on a combinatorial object corresponds to a structural commitment, and that cellular sheaves make the commitment explicit.

| Section of the document | Item in this repository |
|---|---|
| §2.1 Descartes and Gauss-Bonnet defect; Regge action | AT2 (#287); AT20 (#307); `KnillCore` Euler characteristic (PROVED results) |
| §2.2 Knill recursive curvature K(v) = Σ(−1)^k V_{k−1}(v)/(k+1) | KN13 (#249), SURFACE1 (#348) |
| §3.1 Forman-Ricci F(e) = 4 − deg(u) − deg(v) + 3·#triangles | `DiscreteRicci.formanRicciHypergraph` (DEFINED) |
| §3.2 Ollivier-Ricci | #220; AT12 (#297) |
| §3.4 Ball growth (Bishop-Gromov) | AT9 (#294); SPHERE4 (#337) |
| §4 Discrete exterior calculus (cochains, coboundary, δ² = 0, Hodge decomposition) | `KnillCore` d, d*, D, H = D²; `KnillCore.dSquared_eq_zero` (PROVED) |
| §4 Hodge Laplacians on graphs (Lim) | IT3; `HodgeLaplacianBounds.lean`; `HodgeVR.lean` |
| §6 Cellular sheaves | CELL1 (#315) |
| §6.3 Lattice gauge sheaf | IG3-IG7; `DiscreteGaugeField.lean` (not in sheaf form; SHEAF-CHOICE6, #356) |

Items in the document with no earlier task, added as #351-#368:

- §7 choice of restriction maps: SHEAF-CHOICE1-7 (#351-#357) for constant, Hodge, S_k-equivariant, diffusion, order, gauge and tensor-contraction sheaves; SHEAF-CLASSIFICATION (#358).
- §3.3 effective-resistance curvature (Devriendt-Lambiotte 2022): EFFRES1 (#359).
- §4 Hodge star between primal and dual cochains: DEC1 (#360).
- §4 wedge product on cochains: DEC2 (#361), needed for the Cartan structure equations of AT22.
- §5 closure (downward, clique, nerve): CLOSURE1 (#362).
- §6 Hansen-Ghrist sheaf Cheeger inequalities: CHEEGER1 (#363).
- §2.1 Christiansen 2024, distributional to smooth scalar curvature in Regge calculus: REGGE-CONV1 (#364).
- §2.2 causal dynamical triangulations: CDT1 (#365).
- §2.2 Stone's discrete Myers theorem: MYERS1 (#366).
- §2.2 Higuchi planar-graph curvature: HIGUCHI1 (#367).
- §3.2 multi-marginal Ollivier-Ricci for hypergraphs (Eidi-Jost 2020): OLLIVIER-HG (#368).

## 6. Relation to the audit of G1-G4

The audit and the infrageometry programme share the library.

- Audit: what G1-G4 state and what holds, recorded in [`FINDINGS.md`](FINDINGS.md), [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) and [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md).
- Infrageometry: discrete constructions on hypergraphs and their relation to continuum geometry (this file).
- Continuum statements: `ContinuumLimitStatement.lean` states the limits to be proved. `SchwarzschildObligationMet`, `KerrObligationMet` and `FLRWObligationMet` are OPEN. The origin obligations of `HypergraphMetricBridges.lean` and related files hold for every target and are not among these statements.

The discrete side of the quantum track (probability conservation on finite branchial slices, self-adjoint Laplacians) is PROVED; its continuum limit (group IQ) is OPEN.

## 7. External work

| Item | Person | Relevance |
|---|---|---|
| Axiomatic Relativity from Causal Graphs (paper) | CZAPATA, SAHMED | Input for IC7 (EPS axioms) and IC8 (Marzke-Wheeler) |
| `InfraGaugeTheory` paclet (`resources/`) | `PacletInfo` `Creator`: Pavel Pokorny; git committer: PHAJEK | Reference implementation for group IG |
| EME tracking (WWS26) | SAHMED, PHAJEK | Input for IQ8 |
| InfraGaugeTheory internship (April to June 2026) | IMILEA | Moduli of connections, gauge dynamics on causal graphs |
| Paclet work on differential forms and fibred graphs | PHAJEK | Reference for IA3-IA4 |
| Srní, Madrid and Mathematical Institute talks | PHAJEK | Definitions of the programme (transcripts not in the repository) |
| Winter School Srní 2027 | SWOLF (invited) | Contact with the Czech differential-geometry community |
| Austin talk | HVLE | Input for IQ5-IQ6 (Fisher and Fubini-Study metrics) |
| MBQC and Lie-Poisson structures | HKOLCZ, PHAJEK | Input for IB5 and IQ9 |
| IBL-∞ and BV structures | JPULLMAN | Input for IT2 |
| Diffusion geometry (Srní speaker) | external | Comparison framework for IT and IR |
| Tropical geometry | none recorded | IS6 |

## 8. Grounding principle

Each continuum object in the library is to be related to hypergraph data by a PROVED theorem. The current ties are recorded in [`GROUNDING_AUDIT.md`](GROUNDING_AUDIT.md). PROVED ties exist for objects defined on hypergraphs (PDEs, calculus, causal graphs, branchial slices) and for flat limits of fixed graph families (cycles, paths, tori, lattices). The origin obligations attached to curved metrics, connections, Lorentzian manifolds and the Einstein equations do not depend on their target and hold for every target, so they establish no tie. Schwarzschild, Kerr and FLRW limits are OPEN.
