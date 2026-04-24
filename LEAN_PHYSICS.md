# Lean physics formalisation conventions

Survey of existing Lean-based physics formalisation projects, their conventions, and how we align. The goal is to be *part of the ecosystem*, not to invent another one.

## Existing projects

### Mathlib itself
The base layer. We pull in:
- `Mathlib.Topology.MetricSpace.*` — `MetricSpace`, `PseudoMetricSpace`, `HausdorffDist`, partial `GromovHausdorff` API.
- `Mathlib.Geometry.Manifold.*` — charted spaces, `IsManifold`, tangent bundles.
- `Mathlib.MeasureTheory.*` — measure spaces, integrals.
- `Mathlib.Data.Multiset.*`, `Mathlib.Data.Finset.*` — the combinatorial base we use for hypergraphs.

What Mathlib does *not* yet have that we need:
- Ricci / Riemann / Weyl curvature tensors
- Pseudo-Riemannian (Lorentzian) structures
- Optimal transport / Wasserstein distance infrastructure tied into Riemannian geometry
- Lorentzian Gromov–Hausdorff

### HepLean

[HepLean](https://heplean.github.io/HepLean/) — Joseph Tooby-Smith's formalisation of high-energy physics. Covers the Standard Model, gauge theory, fermions, Lorentz transformations. Active project.

Relevant conventions we will adopt:
- **Index conventions.** HepLean uses Lean's abstract algebraic tensor contraction rather than ad-hoc indexing.
- **Units.** Natural units ($\hbar = c = 1$) consistently, with explicit scaling factors when non-natural units appear.
- **Lorentzian signature.** HepLean uses $(+, -, -, -)$ "east-coast" convention. **We will match this** to minimise friction if we later want to cross-reference or share types, even though some Riemannian-geometry literature uses $(-, +, +, +)$.

### Other ongoing efforts worth tracking

- Classical mechanics / variational principles — small-scale formalisations, not yet a unified library.
- Quantum-mechanics Hilbert-space formalisations — some exist, mostly foundational.
- Topos Institute's physics formalisations — categorical / topos-theoretic direction; relevant if we formalise the multiway-evolution categorically.

We will add citations here as specific pieces of each are used.

## Our conventions (derived)

1. **Namespace.** All material in `InfraFormalization.*`. Sub-namespace `Infra` for the discrete-continuum bridge content. Quantum / branchial content lives alongside (`BranchialHilbert`, `BranchialSchrodinger`, `BranchialCanonical`, `FisherMetric`, etc.).

2. **Axioms.** *Only* `propext`, `Classical.choice`, `Quot.sound`. `#print axioms` check runs as part of `AxiomCheck.lean`. No `sorry`, no `decide` / `native_decide`, no custom axioms. Commit hooks will enforce this if we set them up.

3. **Lorentzian signature.** $(+, -, -, -)$ matching HepLean. (Our current cycle / path / torus work is Riemannian; when we move to causal-graph Lorentzian limits, we commit to this.)

4. **Units.** Natural units throughout ($\hbar = c = G = 1$). Explicit conversions at paper-boundary.

5. **Tensors.** When we reach tensor content (Phase 4+), match Mathlib's current direction — likely abstract vector-bundle connections rather than index-gymnastics. Follow HepLean's lead where it exists.

6. **Continuum types.** Prefer Mathlib's existing types (`ℝ`, `ℂ`, `ℝ × ℝ`, `EuclideanSpace`, `ℝ/ℤ` as an `AddCircle`) over hand-rolled alternatives. Continuum-target metric instances that we use directly (`Hypergraph.dist` `PseudoMetricSpace`, `BranchialHilbert` `InnerProductSpace`) are already bundled; auxiliary helpers (e.g. `circleDist` on `ℝ × ℝ`) are kept as plain functions only where that suffices.

7. **Hypergraph side.** Directed multi-hyperedges as `List V` with nonempty-proof (our current `Hyperedge V`). Hypergraph = `Multiset (Hyperedge V)` (our current `Hypergraph V`). This aligns with the combinatorial base of Mathlib and avoids inventing new type hierarchies.

8. **Multiway vs single-way.** `Trajectory` is the single-way evolution; `MultiwayCausalGraph` (`MultiwayCausalGraph.lean`) bundles a rewriting system with its causal DAG on events for the multiway side. Integration with the `../efficient_rewriting_final/` C++ engine's output format is ongoing so that multiway runs there can be consumed directly by the Lean library.

9. **Documentation style.** Every major definition carries a doc-string. Every theorem has a `/--` comment explaining (a) what it says informally, (b) why it's the right statement, (c) what it depends on. Lean-file comments at the top of each file explain the file's purpose and its role in the programme.

10. **Proof style.** Prefer tactic proofs that are readable — named intermediate hypotheses (`have h_foo : ...`), explicit `calc` chains, minimal `simp` + `omega` at the end. Avoid opaque single-tactic closures (`by aesop`, `by polyrith`) for user-visible theorems; these are fine as auxiliary lemma closers.

## Ingesting external formalisations

When we use a theorem proved elsewhere (e.g., Ollivier's 2009 theorem, Gray's tube formula), we *state* it explicitly in our library with a doc-string pointing to the original source and the proof-outline. If/when a fully-proved Lean version exists (in Mathlib or HepLean), we switch to it. Statement-only tokens are marked with a `/-- STATED; not proved locally. -/` doc prefix.

## Contribution upstream

When our work produces Mathlib-appropriate generalisations (e.g., `GHApproximation` could eventually be a Mathlib type), we pull-request upstream rather than maintaining a fork. Infrageometry builds *on* Mathlib; it does not aspire to be parallel to it.
