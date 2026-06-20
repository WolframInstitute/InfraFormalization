# Citations & Novelty Audit

Curated literature pointers for the closed-form findings (#485, #487, #490) and the dual-side discrete-QG framework (#460, #469). For each result we ship, we track:

- **Prior art** — papers our work *cites and builds on*
- **Adjacent work** — papers in the same neighbourhood that do *not* anticipate our result
- **Frontier** — what our work *adds* beyond the cited literature

This document is the audit trail for novelty claims when we eventually write up.

---

## A. Foundations we build on (must cite)

### A1. Knill discrete Gauss-Bonnet

- **Knill, O.** *A discrete Gauss-Bonnet type theorem.* arXiv:[1009.2292](https://arxiv.org/abs/1009.2292) (2010).
- **Knill, O.** *A graph theoretical Gauss-Bonnet-Chern theorem.* arXiv:[1111.5395](https://arxiv.org/abs/1111.5395) (2011).
- **Knill, O.** *Coloring graphs using topology.* arXiv:[1412.6985](https://arxiv.org/abs/1412.6985).
- Used directly in `InfraFormalization.KnillDiscreteGaussBonnet` — `knillEulerScaled = 6·χ`.

### A2. Wolfram-model hypergraph rewriting (Wolfram & Gorard)

- **Gorard, J.** *Some Relativistic and Gravitational Properties of the Wolfram Model.* arXiv:[2004.14810](https://arxiv.org/abs/2004.14810) (2020).
- **Gorard, J.** *Some Quantum Mechanical Properties of the Wolfram Model.* (Wolfram tech report, 2020).
- **Gorard, J.** *Hypergraph Discretization of the Cauchy Problem in General Relativity via Wolfram Model Evolution.* arXiv:[2102.09363](https://arxiv.org/abs/2102.09363) (2021).
- **Gorard, J.** *Non-Vacuum Solutions, Gravitational Collapse and Discrete Singularity Theorems in Wolfram Model Systems.* arXiv:[2303.07282](https://arxiv.org/abs/2303.07282) (2023).
- **Gorard, J.** *Algorithmic Causal Sets and the Wolfram Model.* arXiv:[2011.12174](https://arxiv.org/abs/2011.12174) (2020).
- **Gorard, J.** *Computational General Relativity in the Wolfram Language using Gravitas II: ADM Formalism and Numerical Relativity.* arXiv:[2401.14209](https://arxiv.org/abs/2401.14209) (2024).
- Our work is partially a **technical refutation/audit** of these (see project skeptical-of-Gorard stance in `MEMORY.md`).

### A3. ZX-Calculus + categorical Wolfram model

- **Gorard, J.; Namuduri, M.; Arsiwalla, X.** *ZX-Calculus and Extended Hypergraph Rewriting Systems I.* arXiv:[2010.02752](https://arxiv.org/abs/2010.02752) (2020).
- **Gorard, J. et al.** *ZX-Calculus and Extended Wolfram Model Systems II: Fast Diagrammatic Reasoning.* arXiv:[2103.15820](https://arxiv.org/abs/2103.15820) (2021).
- Categorical/DPO formalization; complementary to our Lean / proof-assistant formalization but does not duplicate the closed-form curvature results.

### A4. Causal-set theory (closest discrete-physics analog)

- **Benincasa, D.M.T.; Dowker, F.** *Scalar curvature of a causal set.* arXiv:[1001.2725](https://arxiv.org/abs/1001.2725) (2010).
- **Aslanbeigi, S.; Saravani, M.; Sorkin, R.D.** *A closed form expression for the causal set d'Alembertian.* arXiv:[1311.1701](https://arxiv.org/abs/1311.1701) (2013).
- **Carlip, S.; Surya, S.** *The causal set approach to quantum gravity.* arXiv:[1903.11544](https://arxiv.org/abs/1903.11544) (2019).
- Recent: combinatorial interpretation of d'Alembertian coefficients. arXiv:[2412.14036](https://arxiv.org/abs/2412.14036) (2024).
- **Adjacent, not overlapping.** Causal-set R uses Benincasa-Dowker d'Alembertian; our R uses Knill Euler-scaled on the causal-DAG topology of Wolfram-model rule evolution. Different definitions.

### A5. Discrete Ricci / Forman / Ollivier

- **Forman, R.** *Bochner's method for cell complexes and combinatorial Ricci curvature.* (2003).
- **Ollivier, Y.** *Ricci curvature of Markov chains on metric spaces.* (2009).
- **Devriendt, K.; Lambiotte, R.** *Effective-resistance curvature.* (2022).
- Recent Wolfram-side: *A Cosine Rule-Based Discrete Sectional Curvature for Graphs.* arXiv:[2212.04406](https://arxiv.org/abs/2212.04406) (2022).
- Used as alternative-curvature screeners in `RuleSignatureExecMetrics` family. Not what our closed forms are about.

### A6. Sierpiński fractal Hausdorff dimension log₂(3)

- **Sierpiński, W.** (1915), Hausdorff dim of Sierpiński triangle = log₂(3) ≈ 1.585.
- Classical. Our scaling exponent **matches** this value — see §C frontier note.

---

## B. Adjacent work (in the neighbourhood, does NOT anticipate our results)

### B1. Pregeometric / homotopy-type Wolfram-model

- **Gorard, J. et al.** *Pregeometric Spaces from Wolfram Model Rewriting Systems as Homotopy Types.* arXiv:[2111.03460](https://arxiv.org/abs/2111.03460) (2021).
- **Gorard, J.** *A Functorial Perspective on (Multi)computational Irreducibility.* arXiv:[2301.04690](https://arxiv.org/abs/2301.04690) (2023).
- Different abstraction layer; doesn't compute branchial Knill or closed forms.

### B2. Multiway/branchial entanglement entropy

- **Gorard, J.; Adhitya, R.** *Axiomatic Quantum Field Theory in Discrete Spacetime via Multiway Causal Structure: The Case of Entanglement Entropies.* arXiv:[2301.12455](https://arxiv.org/abs/2301.12455) (2023).
- QFT-style observables on multiway graphs; doesn't address Knill Euler characteristic or closed-form branchial recurrences.

### B3. Hyperedge-replacement systems and fractal limit spaces

- **Bezuglyi, S.; Mioduszewski, M.; Ramsey, B.** *Eventually Self-Similar Groups acting on Fractals.* arXiv:[2412.04138](https://arxiv.org/abs/2412.04138) (2024).
- Different formalism: hyperedge replacement → limit space, with Sierpiński-like fractals as examples.
- Our Wolfram-model rules ARE hyperedge-replacement rules in a sense, but our log₂(3) result is about the *branchial* graph dynamics, not the spatial limit space.

### B4. Causal Dynamical Triangulations

- **Loll, R.** *Causal Dynamical Triangulations: Gateway to Nonperturbative Quantum Gravity.* arXiv:[2401.09399](https://arxiv.org/abs/2401.09399) (2024).
- Lattice-regularized quantum gravity, different combinatorial substrate. CDT measures spectral / Hausdorff dim from heat kernel; we measure from Knill Euler.

### B5. Lean formalization of physics

- *Formalizing Chemical Physics using the Lean Theorem Prover.* arXiv:[2210.12150](https://arxiv.org/abs/2210.12150).
- *A Formalization of the Generalized Quantum Stein's Lemma in Lean.* arXiv:[2510.08672](https://arxiv.org/abs/2510.08672).
- Different physics domains. No prior Lean formalization of Wolfram-model rewriting + curvature surfaced.

---

## C. Frontier — what we add beyond the literature

The following appear to be **novel territory** based on the search:

### C1. Closed-form B(d) = 3^(d+1) − 3 for branchial Knill

- **Result**: For the persistent equivalence class {`edgeReversal + tripleMerger`, `fork + doubleCycle_5`} on `edge12` seed, the branchial Knill follows the geometric closed form `B(d) = 3·(3^d − 1)`, verified at d = 2..6 by `native_decide` (#485, #487).
- **No prior** Wolfram-model closed-form branchial-Knill recurrence found in literature.
- **Connection to Sierpiński**: the log₂(3) scaling exponent is the *Sierpiński triangle Hausdorff dimension*, indicating self-similar fractal branchial growth. This connection is new — Sierpiński's value appears in Wolfram-model dynamics, **not** as a target metric but as an *emergent* scaling exponent of the discrete physics.

### C2. Closed-form R(d) for the same equivalence class

- **Result**: `R(d) = 3 − 3^(d+1) + 12d + 6·(d mod 2)`. R+B = 12d + 6·(d mod 2) — linear with parity oscillation (#490).
- **No prior** closed-form combining causal R and branchial B with this kind of parity-arithmetic identity found.

### C3. Persistent equivalence between distinct multi-rule combos

- **Result**: `eR + tripleMerger` and `fork + dCyc` have **identical B trajectories** at d=2..6 despite **different R trajectories**, a B-equivalence class with at least 2 members (#481, #484).
- **Explanation** (#491): both systems have *identical distinct-edge counts* = 3^d at every depth. Since branchial structure depends only on distinct edges, the equivalence is structural.
- **No prior** rule-equivalence classification at the curvature-observable level found in the Wolfram-model literature.

### C4. Universal per-edge additivity across rule classes

- **Result**: For both causal and branchial Knill, `K(rule, seed, depth) = |seed| · K(rule, edge12, depth)` — topology-independent (#454, #462).
- Holds across Tree, Merger, Bidirected, and multi-rule classes.
- **No prior** statement of this form in the Wolfram-model literature.

### C5. Discrete unified Einstein-Hilbert action

- **Result**: `S(rule, seed, d, α) = |seed| · (R + α·B)` with rational balance α* values {4/5, 7/11, 6/13} certified for specific combos (#465, #470).
- α* interpreted as a "discrete Planck-constant analog" for the classical/quantum-amplitude balance.
- **No prior** discrete-physics framework defining a unified action coupling causal-DAG and branchial-DAG curvature with a rational coupling constant found.

### C6. Lean 4 formalization of Wolfram-model curvature observables

- **Result**: ~50 Lean modules certifying the entire dual-side framework: rule classifier, universal additivity, closed forms, BBH endgame substrate, R/B independence, vacuum regime.
- **No prior** Lean (or other proof-assistant) formalization of Wolfram-model rewriting + curvature found.

---

## D. Open questions where we sit at the literature frontier

### D1. Symbolic proof of B(d) = 3^(d+1) − 3 for all d ≥ 2

- Currently verified by `native_decide` at d = 2..6 (~5-depth verification).
- The structural-induction proof (#492) — `distinctEdgeCount(singleWayStep sys H) = 3·distinctEdgeCount H` — is the missing piece for full H9 closure.
- **No prior** symbolic proof in this direction found.

### D2. Continuum-limit scaling theorem

- Conjectured: in the continuum limit (lattice spacing h → 0 with depth d ~ -log₂ h), `B(h) ~ 3 · h^{-log₂ 3} ≈ 3 · h^{-1.585}` (#486).
- **Closest** prior continuum-limit work: Benincasa-Dowker causal-set d'Alembertian convergence (1001.2725) — different framework.
- **No prior** Wolfram-model continuum-limit scaling-exponent theorem.

### D3. Whether other rule combos beyond the persistent equivalence class admit closed forms

- We found one persistent equivalence pair. Are there more?
- We have honest **negative findings** (#458): multi-rule R doesn't combine simply from single-rule R values.
- Open: a systematic classification of all maxRHS≤3 multi-rule combos by their (R, B) closed-form structure.

---

## E. Citation tracking discipline

Every novel claim shipped going forward must update §C with:
- Pointer to the relevant Lean module/theorem
- A best-effort literature pointer (or explicit "no prior art found" with the search queries used)
- A 1-line frontier note saying what *this* result adds

If a search surfaces a paper that anticipates our result, **move it from §C to §A** and update the project's novelty framing immediately. Honest scoping is more valuable than overclaiming.
