# Citations and related work

This file lists the literature the library builds on and the literature related to the Knill-value computations of this repository. For each computation it records the Lean modules, the status, and the related papers found in the literature search.

Status labels as in [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md): PROVED, PROVED-WITH-NATIVE-DECIDE, MEASURED, READ, OPEN.

---

## A. Foundations

### A1. Knill discrete Gauss-Bonnet

- Knill, O. *A discrete Gauss-Bonnet type theorem.* arXiv:[1009.2292](https://arxiv.org/abs/1009.2292) (2010).
- Knill, O. *A graph theoretical Gauss-Bonnet-Chern theorem.* arXiv:[1111.5395](https://arxiv.org/abs/1111.5395) (2011).
- Knill, O. *Coloring graphs using topology.* arXiv:[1412.6985](https://arxiv.org/abs/1412.6985).
- Used in `KnillDiscreteGaussBonnet.lean`: `knillEulerScaled` equals 12 = 6·χ(S²) on the tetrahedron, octahedron and icosahedron (`tetrahedron_knillEuler`, `octahedron_knillEuler`, `icosahedron_knillEuler`, PROVED-WITH-NATIVE-DECIDE).

### A2. Wolfram-model hypergraph rewriting

- Gorard, J. *Some Relativistic and Gravitational Properties of the Wolfram Model.* arXiv:[2004.14810](https://arxiv.org/abs/2004.14810) (2020). (G1)
- Gorard, J. *Some Quantum Mechanical Properties of the Wolfram Model.* Complex Systems 29(2) (2020) 537-598, doi:10.25088/ComplexSystems.29.2.537. (G5)
- Gorard, J. *Algorithmic Causal Sets and the Wolfram Model.* arXiv:[2011.12174](https://arxiv.org/abs/2011.12174) (2020). (G2)
- Gorard, J. *Hypergraph Discretization of the Cauchy Problem in General Relativity via Wolfram Model Evolution.* arXiv:[2102.09363](https://arxiv.org/abs/2102.09363) (2021). (G3)
- Gorard, J. *Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems in Wolfram Model Systems.* arXiv:[2303.07282](https://arxiv.org/abs/2303.07282) (2023). (G4)
- Gorard, J. *Computational General Relativity in the Wolfram Language using Gravitas I: Symbolic and Analytic Computation.* arXiv:[2308.07508](https://arxiv.org/abs/2308.07508) (2023). (GI)
- Gorard, J. *Computational General Relativity in the Wolfram Language using Gravitas II: ADM Formalism and Numerical Relativity.* arXiv:[2401.14209](https://arxiv.org/abs/2401.14209) (2024). (GII)
- Gorard, J. *General Relativistic Hydrodynamics in Discrete Spacetime: Perfect Fluid Accretion onto Static and Spinning Black Holes.* arXiv:[2402.02331](https://arxiv.org/abs/2402.02331) (2024). (GH)
- Gorard, J. *Gravitas*, Wolfram Language source code, [github.com/JonathanGorard/Gravitas](https://github.com/JonathanGorard/Gravitas), commit 9b02562 (2023-08-28). (GC)
- Local copies of G1-G9, GI, GII and GH are kept in `papers/` as `gorard_<arXiv id>.pdf`, the text extracted with `pdftotext -layout` as `gorard_<arXiv id>.txt`, and the TeX source as `tex_<first four digits of the arXiv id>/`. G5 (Complex Systems 29(2) 537-598, not on arXiv) is kept as `gorard_complexsystems_29_2.pdf` and `.txt`, with no TeX source. The two papers of 2301 keep their TeX sources in `tex_2301_04690/` and `tex_2301_12455/`. The directory is not tracked. Line numbers in the documentation refer to these files.
- The audit of G1-G4 is in [`FINDINGS.md`](FINDINGS.md), [`MAJOR_FLAWS.md`](MAJOR_FLAWS.md) and [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md).

### A3. ZX-calculus and categorical Wolfram model

- Gorard, J.; Namuduri, M.; Arsiwalla, X. *ZX-Calculus and Extended Hypergraph Rewriting Systems I.* arXiv:[2010.02752](https://arxiv.org/abs/2010.02752) (2020).
- Gorard, J. et al. *ZX-Calculus and Extended Wolfram Model Systems II: Fast Diagrammatic Reasoning.* arXiv:[2103.15820](https://arxiv.org/abs/2103.15820) (2021).
- These papers give a categorical (double-pushout) formalisation of hypergraph rewriting. They contain no Knill-value computations.

### A4. Causal-set theory

- Benincasa, D.M.T.; Dowker, F. *Scalar curvature of a causal set.* arXiv:[1001.2725](https://arxiv.org/abs/1001.2725) (2010).
- Aslanbeigi, S.; Saravani, M.; Sorkin, R.D. *A closed form expression for the causal set d'Alembertian.* arXiv:[1311.1701](https://arxiv.org/abs/1311.1701) (2013).
- Carlip, S.; Surya, S. *The causal set approach to quantum gravity.* arXiv:[1903.11544](https://arxiv.org/abs/1903.11544) (2019).
- Combinatorial interpretation of the d'Alembertian coefficients. arXiv:[2412.14036](https://arxiv.org/abs/2412.14036) (2024).
- Causal-set scalar curvature uses the Benincasa-Dowker d'Alembertian. The quantity R of this repository is a scaled Knill Euler characteristic of a DAG built from a rewriting trace. The two definitions differ.

### A5. Discrete Ricci curvature

- Forman, R. *Bochner's method for cell complexes and combinatorial Ricci curvature.* (2003).
- Ollivier, Y. *Ricci curvature of Markov chains on metric spaces.* (2009).
- Devriendt, K.; Lambiotte, R. *Effective-resistance curvature.* (2022).
- *A Cosine Rule-Based Discrete Sectional Curvature for Graphs.* arXiv:[2212.04406](https://arxiv.org/abs/2212.04406) (2022).
- Used as screening metrics in the `RuleSignatureExecMetrics` modules.

### A6. Hausdorff dimension of the Sierpiński triangle

- Sierpiński, W. (1915). The Sierpiński triangle has Hausdorff dimension log₂ 3 ≈ 1.585.

---

## B. Related work

### B1. Pregeometric and homotopy-type Wolfram model

- Gorard, J. et al. *Pregeometric Spaces from Wolfram Model Rewriting Systems as Homotopy Types.* arXiv:[2111.03460](https://arxiv.org/abs/2111.03460) (2021).
- Gorard, J. *A Functorial Perspective on (Multi)computational Irreducibility.* arXiv:[2301.04690](https://arxiv.org/abs/2301.04690) (2023).
- These papers work at a different level of abstraction and contain no Knill-value computations.

### B2. Multiway entanglement entropy

- Gorard, J.; Adhitya, R. *Axiomatic Quantum Field Theory in Discrete Spacetime via Multiway Causal Structure: The Case of Entanglement Entropies.* arXiv:[2301.12455](https://arxiv.org/abs/2301.12455) (2023).
- QFT observables on multiway graphs. No Knill Euler characteristic.

### B3. Hyperedge-replacement systems and fractal limit spaces

- Bezuglyi, S.; Mioduszewski, M.; Ramsey, B. *Eventually Self-Similar Groups acting on Fractals.* arXiv:[2412.04138](https://arxiv.org/abs/2412.04138) (2024).
- Hyperedge replacement with limit spaces, including Sierpiński-type fractals.

### B4. Causal dynamical triangulations

- Loll, R. *Causal Dynamical Triangulations: Gateway to Nonperturbative Quantum Gravity.* arXiv:[2401.09399](https://arxiv.org/abs/2401.09399) (2024).
- Lattice-regularised quantum gravity on triangulations. CDT measures spectral and Hausdorff dimension from the heat kernel.

### B5. Lean formalisation of physics

- *Formalizing Chemical Physics using the Lean Theorem Prover.* arXiv:[2210.12150](https://arxiv.org/abs/2210.12150).
- *A Formalization of the Generalized Quantum Stein's Lemma in Lean.* arXiv:[2510.08672](https://arxiv.org/abs/2510.08672).
- The literature search found no earlier proof-assistant formalisation of Wolfram-model rewriting.

---

## C. Knill-value computations in this repository

"B" is the scaled Knill Euler characteristic of `branchialDAGOfFireAll`, which joins two events of the same step that consume a common edge value. This relation differs from the Wolfram-model branchial graph. "R" is the scaled Knill Euler characteristic of `causalDAGOfFireAll`. Both graphs are built from `MultiwayExec.fireAllStep` (through `tracedFireAllEvolve`). `fireAllStep` applies every match of every rule found in the input state, including matches that share edges. It is not a Wolfram model update when matches overlap, so values computed with it do not describe Wolfram model evolutions. `MultiwayExec.singleWayStep` applies a maximal set of edge-disjoint matches.

### C1. B(d) for two rule pairs

- OPEN: for `edgeReversal_tripleMerger_Sys` and `fork_doubleCycle_Sys` on the seed `seedEdge12`, B(d) = 3^(d+1) − 3 for every d ≥ 2. Lean: none. The library defines no theorem about `branchialDAGOfFireAll`.
- The growth factor 3 per depth gives the exponent log₂ 3 if depth d is identified with −log₂ h for a lattice spacing h. No theorem in the library defines h or relates B to the Sierpiński triangle.
- Literature search: no earlier Wolfram-model computation of this quantity was found.

### C2. R(d) for the same pair

- PROVED-WITH-NATIVE-DECIDE: R(3) = −36 for `edgeReversal_tripleMerger_Sys` and R(3) = 0 for `fork_doubleCycle_Sys` (`edgeReversal_tripleMerger_knill_neg36`, `fork_doubleCycle_knill_zero`, `MultiRuleDiscovered.lean`).
- OPEN: R(d) + B(d) = 12d + 6·(d mod 2) for `edgeReversal_tripleMerger_Sys` and every d ≥ 2. Lean: none.

### C3. Distinct edges of the two rule pairs

- PROVED-WITH-NATIVE-DECIDE: both systems of C1 have 3^d distinct edges at d = 0, ..., 4 (`DistinctEdgeIdentity.lean`, `H9StructuralProgress.lean`).
- PROVED: `H9_conditional_on_bridge` (`H9Closure.lean`) derives the count 3^d for every d from the proposition `engineMatchesTriad`.
- OPEN: `distinct_tripling_conjecture`, the count 3^d for both systems at every depth d.
- OPEN: the equality of B for the two systems at every depth. Lean: none.

### C4. Per-edge additivity

- PROVED-WITH-NATIVE-DECIDE: `per_edge_additivity_instances` (`UniversalAdditivity.lean`) is a conjunction of five equalities for `doubleCycleSys_5` at depth 4 under `singleWayStep`: the Knill value on each of the seeds `seedEdge12`, `seedPath123`, `seedTwoDisjoint`, `seedTriangle`, `twoTriangleSeed` equals the number of seed edges times the value on `seedEdge12`. Further conjunctions in the same module cover `edgeReversalSys` at depth 5 and `bidirectedEdgeSys` at depth 4 under `singleWayStep`, and `edgeReversal_identity_Sys` at depth 3 under `fireAllStep` (`additivity_multi_rule_instances`).
- OPEN: the identity for every seed, rule and depth.

### C5. Linear combination R + α·B

- OPEN: S(rule, seed, d, α) = |seed|·(R + α·B) and the values of α at which S = 0 for specific rule pairs on `twoTriangleSeed`. Lean: none.
- No theorem relates S to the Einstein-Hilbert action or α to a physical constant.

### C6. Lean formalisation of Wolfram-model rewriting

- The library formalises hypergraphs, rule applications, trajectories, an executable step operator, and causal histories with hyperedge identities (`CausalHistory.lean`). The results about the causal graph of the rule of G3 line 6202 (edge-count conservation, antichain bound, cone bound 5^t) are PROVED for every update order. See [`STATUS_OF_GORARD_CLAIMS.md`](STATUS_OF_GORARD_CLAIMS.md), Claim 1.
- The literature search found no earlier proof-assistant formalisation of Wolfram-model rewriting.

---

## D. Open items

- D1. B(d) = 3^(d+1) − 3 for `edgeReversal_tripleMerger_Sys` and every d (C1), and the corresponding statement for R (C2).
- D2. The same computations with `MultiwayExec.singleWayStep` in place of `fireAllStep`, so that the values describe Wolfram model evolutions.
- D3. Whether rule pairs other than the two in C1 have closed forms for B and R.

---

## E. Recording new results

Each new result added to §C records:

- the Lean module and theorem, with its status label;
- the step operator used (`singleWayStep` or `fireAllStep`);
- a literature pointer, or the search queries used when no prior statement was found.

A paper found to contain an earlier statement of a §C result is moved to §A or §B and cited in the result's entry.
