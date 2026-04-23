# Pavel Hájek planning items — coverage map

Tracks every item from Pavel's weekly update (2026-04-??) and the Discord "core dump" (entries dated 2025-10-06 to 2026-04-14) against the current Lean library + existing task list, and earmarks uncovered items for future work.

Status codes:
- **covered** — already formalised in the Lean library.
- **partial** — related scaffolding exists; the specific extension Pavel proposes is open.
- **tracked** — task created; formalisation pending.
- **external** — activity outside the scope of this formalisation project (talk, meeting, discussion).

## Weekly-update items (recent)

| Item | Status | Coverage in this project |
|---|---|---|
| Infrageometric paclet migration; new persistence paclet | partial | Mathematical content of persistence covered: `VietorisRips.lean` (IT1), `HodgeVR.lean` (IT2), `HodgeLaplacianSpectrum.lean` + `HodgeLaplacianBounds.lean` (IT3), persistence barcode (IT4), `ID3` homology dimension, Latschev obligation proved for cycles (IT5), scale-trichotomy endpoints proved (IT6). Paclet migration itself is M6 (pending). |
| Austin talk | external | — |
| Scott Aaronson group meeting | external | — |
| Mukund Rangamani holography talk | external | Relates to J6 AdS/CFT-analog (pending); P18 (tracked). |
| Unruh effect / Fisher information / holographic-dualities discussions | partial | Fisher side covered: `FisherMetric.lean` (IQ5), `FisherMetricExtended.lean`, M2 Van Le Fisher → Fubini-Study bridge, IQ6 `fubiniStudyBhattacharyya_bound` proved. Unruh effect + holographic dualities: P18 (tracked). |
| Classification of graphs with pointwise constant Wolfram-Hausdorff dimension (with Dugan, inspired by Sam Rodkey) | partial | `ID1` Wolfram-Hausdorff dimension function on hypergraphs, `ID2` plateau detection; `ID6` compatibility theorem in progress (aim: all dimension notions agree on regular lattices) — directly the target locus. |
| Combinatorial Levi-Civita connection in InfraGaugeTheory | partial | IG1 FiberedGraph, IG2 Section, IG3 Connection, IG4 ParallelTransport, IG5 HolonomyMatrix, IG6 WilsonLoop, IG7 FlatConnection, IG8 FiberBundle, IG9 GraphTangentBundle, IG11 MultiFibrationProjection all covered. Combinatorial Levi-Civita specifically: C5 (Koszul Levi-Civita) and C7 (discrete connection on a hypergraph) pending; `FiberedGraphConnectionBridge.lean` attaches the obligation Prop. |
| Ribbon graphs + Whitehead moves + hypergraph = (1-skeleton, clique-complex cochain) with Kolpakov | tracked | New tasks P4 (ribbon structure + Whitehead moves) and P19 (1-skeleton + clique-cochain decomposition). |
| Carlos InfraCausality paper | covered | IC1 CausalGraphType, IC2 ObserverChain, IC3 LightRay, IC4 Foliation + ProperTime, IC5 SpatialReconstruction, IC6 MultiFibrationProjection, IC7 EPSAxioms, IC8 MarzkeWheeler; M5 Zapata + Ahmed paper completed. |
| Knutt's paper | external | Reference not held here. |
| Ioana coordinatization pipeline in InfraGaugeTheory | partial | ID4 CoordinatizationDimension via extremal orthogonal axes completed; M1 Ioana Milea IG-intern coordination pending. |

## Core-dump items — coverage map

| Item (with date) | Status | Coverage / task |
|---|---|---|
| Delta complexes, simplicial sets from oriented hypergraphs; face maps, degeneracy maps, barycentric subdivision (2025-10-06, 2025-10-18, 2025-10-22) | tracked | **P1** (#193). |
| Cup product; comparison of two definitions of forms (2025-10-06) | tracked | **P2** (#194). Extends existing `DeRham.lean` (IA3) + `FormCochainIntegration.lean` (IA4). |
| Hodge propagator on graphs; 1-loop Chern-Simons amplitude from ribbon graphs; IBL-∞ twist via Maurer-Cartan (2025-10-06, 2025-11-09) | tracked | **P3** (#195), overlaps with **M4** Jan Pullman IBL-∞/BV. Existing scaffolding: `HodgeVR.lean`, `HodgeLaplacianSpectrum.lean`, `HodgeLaplacianBounds.lean`. |
| Homotopy transfer and formality (2025-10-06) | tracked | **P17** (#209) homotopy-algebra / homological-algebra scaffold. |
| Quantum topology (2025-10-06) | tracked | Subsumed under P17 (#209). |
| Finer fibre bundles (2025-10-06) | partial | FiberBundle (IG8), MultiFibrationProjection (IG11), GraphTangentBundle (IG9) covered; further refinements can be added under the IG namespace. |
| Infra complex and symplectic geometry (2025-10-06) | partial | `BlowupLieAlgebra.lean` (IB3), `BlowupPoissonConcrete.lean`, `RadialLaminarBlowup.lean` (IB6) cover part of the symplectic / Poisson side; complex structure is open. |
| Homological algebra paclet (2025-10-06) | tracked | **P17** (#209). |
| Simplicial trie visualisation (2025-10-06) | tracked | Covered under **P15** (#207) observability tools. |
| Coordinate-squashing delta-complexes with degenerate hyperedges (2025-10-06) | tracked | **P1** (#193) — coordinate-squashing is a specific construction in that task. |
| Community post: complexes in infrageometry (2025-10-06) | tracked | Output of P1 / P2 / P17. |
| Community post: Chern-Simons for graphs (2025-10-06) | tracked | Output of P3. |
| Community post: graded Lie bracket, Koszul convention (2025-10-06) | tracked | **P6** (#198). |
| Community post: torsion of simplicial complexes (2025-10-06) | tracked | Output of P1 / P17. |
| Community post: Turing machine on disk → Wolfram (2025-10-06) | covered | Pavel marks this done (2025-10-18) in GeneralizedShift / MultiwayGeneralizedShift. External. |
| Paclet: quantum topology / homological algebra / homotopy algebras (2025-10-06) | tracked | P17 + P3. |
| Observability tools for hypergraph rewriting (flame graph, waterfall) (2025-10-06) | tracked | **P15** (#207). |
| Minimal square covering problem (2025-10-06) | external | Off-topic for the formalisation project. |
| Git as hypergraph rewriting (2025-10-06) | external | Off-topic. |
| Vim distance (2025-10-12) | external | Off-topic / esoteric. |
| Homotopy colimit of rewriting system; extend Knill invariants to simplicial sets (2025-10-18) | tracked | **P7** (#199). |
| Discrete quantum field theory — path integral = Feynman graphs as bundles of walks; ribbon structure meaning for walks; loop values (2025-10-18) | partial | IQ9 path-integral obligation baseline proved; full Feynman-walks interpretation + ribbon meaning tracked under **P3** (#195) and **P4** (#196). |
| Volume and connectivity of clouds of points with same observer-chain coordinates (2025-10-18) | partial | ID4 CoordinatizationDimension covers the underlying coordinatisation; the vertices-per-coordinate ratio and constancy question is not yet formalised. Tracked under ID6 (#144 in progress). |
| Koszul sign for ribbon graphs / hypergraph rewriting (2025-10-18, 2025-11-12) | tracked | **P6** (#198). |
| Sheaves on hypergraphs; sheaf cohomology; orientation sheaf (2025-10-18) | tracked | **P5** (#197). |
| Filtrations of multiway system; vertical, layered, others; completion (2025-10-21) | tracked | **P8** (#200). |
| Simplicial set from face graph of oriented hypergraph; simplicial identities; barycentric subdivision (2025-10-22) | tracked | **P1** (#193). |
| Ribbon (hyper)graph + amplitudohedron / associohedron alternative representations (2025-11-06) | tracked | **P4** (#196). |
| Lie brackets via surgery on hypergraphs; represent known infinite-dimensional Lie algebras (2025-11-09) | partial | Insertion Lie algebra IB4 covered; higher-order / n-Lie extensions tracked under **P10** (#202). |
| Discrete Chern-Simons theory via Hodge + Feynman integrals + IBL-∞ + loop space (2025-11-09) | tracked | **P3** (#195). |
| Knill / Latschev relation to Riemannian via geodesics (2025-11-09) | tracked | **P16** (#208). |
| Why should computation relate to geometry (motivation) (2025-11-09) | covered | Project motivation section in README and weekly report. |
| Koszul sign via confluent rewriting; natural basis of functions on moduli of isomorphism classes (2025-11-12) | tracked | **P6** (#198). |
| 3-body problem as Turing machine (2025-11-19, 2026-01-27) | tracked | **M10** (pending) 3BP / dynamical-systems dimension signature. |
| Blow-up rules as scale-changing → renormalisation group connection (2025-11-23) | tracked | **P14** (#206). |
| Action principle for rewriting (2025-12-10) | tracked | **P9** (#201), coordinated with Carlos. |
| Interaction diagrams from causal graphs; light rays; elementary particles as volume-bounded subgraphs (2025-12-20) | tracked | **P11** (#203). |
| Exponential map at a vertex via shortest-path counts (2025-12-20) | covered (as task) | **IG10** already in the task list (pending). |
| Tropical geometry (2026-01-18) | covered (as task) | **M9** already in the task list (pending). |
| Chaos in hypergraph rewriting; vertical + horizontal (2026-02-02) | tracked | **P12** (#204). |
| Variational principles on hypergraph-space paths; action functional (2026-02-21) | tracked | **P9** (#201). |
| n-Lie / Filippov extension of insertion bracket via signed confluence (2026-02-22) | tracked | **P10** (#202). |
| Dual point of view on infrageometry: ring of functions + Utkarsh twisted-difference operators → reconstruction theorem (2026-04-14) | tracked | **P13** (#205). |

## Task catalog (new, prefix P)

| # | Task |
|---|---|
| 193 | P1: Delta / simplicial machinery on hypergraphs |
| 194 | P2: Cup product + comparison of two form definitions |
| 195 | P3: Discrete Chern-Simons amplitude on graphs |
| 196 | P4: Ribbon (hyper)graph structure + Whitehead moves |
| 197 | P5: Sheaves on hypergraphs |
| 198 | P6: Koszul signs / graded Lie bracket on (hyper)graph rewriting |
| 199 | P7: Homotopy colimit of rewriting system |
| 200 | P8: Filtrations of multiway systems |
| 201 | P9: Action principle for hypergraph rewriting |
| 202 | P10: n-Lie / Filippov extension of insertion bracket |
| 203 | P11: Interaction diagrams from causal graphs |
| 204 | P12: Chaos theory in hypergraph rewriting |
| 205 | P13: Utkarsh Bajaj twisted-difference operators + ring-of-functions duality |
| 206 | P14: Blow-up rules as renormalization group |
| 207 | P15: Observability tools for hypergraph rewriting |
| 208 | P16: Knill geodesics approximating Riemannian geodesics |
| 209 | P17: Homotopy algebra / homological-algebra scaffold |
| 210 | P18: Holography / Unruh effect discussions |
| 211 | P19: Hypergraph as (1-skeleton, clique-complex cochain) decomposition |
