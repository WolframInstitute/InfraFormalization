# Rule search via the Lean machinery

Our infrageometry Lean corpus can be used as a **verifier** and **screener** in a rule-search pipeline aimed at finding Wolfram-model rewriting rules whose causal graph converges to a Lorentzian manifold. It does **not** generate rules — that is a separate combinatorial-search problem. What it does is give formal grounds for accepting or rejecting candidates, and quantitative dimensional signatures that drive the rejection phase.

## What the Lean corpus provides

### Negative screening (fast rejection)

| Mechanism | Lean primitive | What it rules out |
|---|---|---|
| Conservation forces constant state size | `Application.size_result_of_conservative` | Rules where the causal graph can grow in density; places an upper bound on cone dimension. Refutes Gorard's named rule (F7). |
| Same-level antichain | `same_level_ordered_antichain`, `no_causal_edge_within_level` | Rules whose causal DAG lacks consistent level structure (shouldn't happen for well-formed trajectories, but the formal invariant is available). |
| Linear cone growth empirically | (combinatorial; driven by level and causal-precedence counts) | Rules with cone dimension 1 on any seed — cannot support 3+1-dim Minkowski. |

### Quantitative signatures

These are the per-rule observables that should track dimensional expectations:

1. **Level-growth signature.** For a (d+1)-dim Minkowski target:
   `|{j : j < N ∧ level τ j ≤ t}|  ~  t^{d+1}` (as `t` grows within the trajectory).
   Formal grounds: `level_add_one_le_of_isCausalPred`, `level_eq`.

2. **Antichain-width signature.** For d spatial dimensions:
   `|{j : level τ j = k}|  ~  k^d`.
   Formal grounds: `no_causal_edge_within_level` (antichain structure).

3. **Forward-cone volume.** `|{j : causallyPrecedes τ i j ∧ level τ j ≤ level τ i + t}|  ~  t^{d+1}`.
   Formal grounds: `causallyPrecedes_implies_minkowski`, `causallyPrecedes_implies_timelike`.

4. **Bridging consistency.** Given a candidate spatial embedding `φ : event-index → Fin d → ℤ`, check that every `causallyPrecedes τ i j` pair satisfies `Timelike d (fullEmbed φ i) (fullEmbed φ j)` in the Lorentz lattice. This is decidable and mechanisable. The 1+0-dim version is already proved automatic (`causallyPrecedes_implies_timelike`); higher-dim is a conditional theorem parameterised by the embedding.

### Verification scaffolding

Once a candidate rule is found:
- Instantiate `Trajectory sys init` for sample trajectories of the rule.
- Compute `level τ` — it is a formally-valid Minkowski time coordinate (`trajectoryToEvent_preserves_causal`).
- The bridging theorems (`causallyPrecedes_implies_timelike`, `trajectoryToEvent_lossy`) transfer automatically. No re-proof per rule.
- Any chosen spatial embedding can be checked for `Timelike`-consistency per causal pair, giving a formal certificate.

## What the Lean corpus does not provide

- **Rule generation.** No enumeration, no evolutionary search, no physics-priors. A separate generator is required (`../efficient_rewriting_final/`, `SetReplace`, heuristic search).
- **Canonical spatial embedding.** F1 rules this out structurally. The best we can offer is: "given this chosen embedding, Lean certifies Minkowski consistency." The embedding itself is a non-canonical choice.
- **Curvature certification.** Pending Mathlib Ricci/Riemann infrastructure. Currently we have Ollivier and Gray *statements* only, plus proven disagreement of Gorard's forms on S² and S³.

## Practical pipeline

The natural build-out is a harness:

1. **Generator** — `../efficient_rewriting_final/` emits trajectory data (initial hypergraph + sequence of applications) per candidate rule.
2. **Python screener** — computes level distribution, antichain widths, cone-volume growth from the trajectory data.
3. **Polynomial-growth filter** — rejects rules failing the `t^{d+1}` and `k^d` signatures for targeted `d`.
4. **Spatial-embedding search** — for surviving rules, attempt embeddings (graph-layout algorithms, spectral embedding, heuristic) into `Fin d → ℤ`.
5. **Lean certificate** — export the trajectory into Lean's `Trajectory` type, load the chosen embedding, and the bridging theorems produce a formal certificate of Minkowski-consistency.

Steps 1–4 are engineering; step 5 is the payoff of our current Lean corpus.

## Scope honesty

This pipeline *verifies* that a candidate rule has causal-graph structure consistent with a chosen Lorentzian target. It does not:
- prove the rule's causal graph *converges* to Lorentzian spacetime (needs a scaled-trajectory GH theorem, not yet formalised);
- produce curvature data (needs Mathlib Ricci, not yet landed);
- prove the target is an *Einstein* manifold (needs the action convergence of F5, which is open).

Those are the remaining structural gaps — tracked in `MILESTONES.md` under Phases 4, 5, and 6.

## References

- `lean/InfraFormalization/CausalLevel.lean` — level function + monotonicity + antichain.
- `lean/InfraFormalization/Infra/TrajectoryLorentz.lean` — 1+0-dim bridging.
- `lean/InfraFormalization/Infra/LorentzLattice.lean` — `CausalPrecedes`, `Timelike`, `Null`, `Spacelike`, `minkowskiIntervalSq`.
- `results/phase1_selfaudit/` — empirical cone-dimension rejection of Gorard's named rule.
- `MAJOR_FLAWS.md` — F1 (no canonical metric), F2 (fiat orthonormality), F5 (ill-defined limit).
