# Roadmap — full project sequencing toward BBH-from-hypergraph

End-state: a real binary black hole merger emerging from a hypergraph
initial condition under a Wolfram rule, with Lean-checked convergence
to NR waveforms. Not a Poisson sprinkling of the target manifold — actual rule
dynamics with rigorous bridge to GR.

This document sorts every pending task into phases by precedence and
dependency. Each phase's tasks must complete before the next phase's
critical-path items are unblocked. Parallel streams that don't gate
the critical path are listed separately.

Last updated: 2026-04-26 (post-#234 closure, post-#231 type bridge,
post-INFRAGEOMETRY synthetic-geometry framing).

---

## Phase A — Make obligation Props load-bearing

The current `HypergraphMetricOriginObligation` is "∃ rule + scaling" —
no actual convergence content. This phase upgrades the obligation
framework to embed real convergence-rate Props, then re-discharges
flat targets.

| # | Task | Deps | Payoff |
|---|---|---|---|
| 233 ✓ | Strengthen origin-obligation Props with W_1 / Wasserstein content | #234 ✓ | Obligations gain quantitative teeth — `HypergraphMetricOriginObligationStrong` lands |
| — | **NEXT**: Refactor `WassersteinRateObligation` → generic `ConvergenceRateObligation` family | #233 ✓ | Admits non-W_1 metrics (Forman-Ricci, GH, spectral) — Phase A follow-up |
| 233 ✓ | Re-discharge Minkowski targets with subdivisionDiscrepancyBundle | #233 ✓ | `minkowski4_from_hypergraph_strong` proven; `any_metric_has_strong_obligation_witness` lifts to all GR-zoo metrics |
| — | **NEXT**: Tie discrepancy to actual W_1 of trajectory's pushed measure | #233 ✓ + measure-of-trajectory infra | Strong obligation becomes load-bearing not just statement-level |

**Phase A unlocks:** Phase B screener metrics know what shape to take
(they target the same obligations they'll be screening for).

---

## Phase B — Rule-search infrastructure

Build the screening pipeline: Lean-side metric definitions matching
the obligation Props, a signature interchange format, and the
wolframscript / efficient-C++-engine driver.

| # | Task | Deps | Payoff |
|---|---|---|---|
| 224 | Rule-output curvature signature screener (per-slice Forman/Ollivier) | Phase A | Per-rule signature metrics in Lean |
| — | RuleSignatureSchema (JSON interchange + Lean validator) | #224 | Engine output → Lean obligation match |
| 190 | Empirical rule search via wolframscript | #224 + RuleSignatureSchema | Bulk rule evaluation against signatures |
| 227 | MultiwayExec per-edge-instance match enumeration (TC4/TC5 fix) | — | Internal cross-validation |
| 228 | MultiwayExec causal edge tracking | #227 | Causal-graph signatures from engine output |
| 229 | MultiwayExec branchial edge tracking | #227 | Branchial-graph signatures from engine output |
| 230 | MultiwayExec state canonicalisation modulo isomorphism | #227 | Multiway state dedup |

**Phase B unlocks:** for any rule R in a corpus, can we *cheaply* check
whether R's trajectory satisfies obligation O_target? If yes, R becomes
a discharge candidate.

---

## Phase C — Curved-target discharge + GR thesis

This is the headline result: discharge a real curved 4D Lorentzian
metric obligation with a found rule. Substantial.

| # | Task | Deps | Payoff |
|---|---|---|---|
| R4 | Curved discrete-Ricci convergence beyond flat | #224 | Curved-Ricci formal status per metric |
| 218 | Prove or disprove curved-target Ricci convergence (per metric) | R4 | Per-metric verdict |
| 217 | Project-own curvature tensors end-to-end on named GR metrics | — | No Mathlib dependency for diff geom |
| 220 | Ollivier-Ricci convergence on a concrete discretisation | R4 | Alternative curvature route |
| 225 | Multi-way → continuum bridge (MultiwayCausalGraph convergence) | #231 ✓ + Phase B | Abstract convergence semantics |
| 235 | Anchoring audit (every Lean module to ExecHG / Multiway / hypergraph-grounded) | #231 ✓ | No continuum islands |
| 236 | Rule-based discharge of curved-target obligations | Phase A + Phase B + R4 | Actual discharge of one curved metric |
| 213 | Lorentzian-GH distance (Noldus/Suhr style) | — | Lorentzian convergence type |
| E6 | Lorentzian Gromov-Hausdorff | #213 | Lorentzian metric on causal graphs |
| E7 | Discrete-causal-DAG → continuum Lorentzian convergence | #213 + E6 | Causal-side convergence theorem |
| 222 | Pointed-GH and metric-measure-GH (project-own) | — | Convergence framework |
| 221 | PDE solution-level convergence, not just eigenvalues | — | Strong PDE convergence |
| 219 | Discrete Hamiltonian / momentum constraint residuals | E5 | ADM constraint preservation |
| H4 | Scaled trajectory → continuum manifold convergence | Phase B | Generic rule → manifold theorem |
| H5 | Curved-target RicciBridge extensions | R4 + #218 | Bridge for each metric |

**Phase C unlocks:** at least one GR metric has a real
`(rule, trajectory, convergence-proof)` discharge. The bridge ladder
becomes load-bearing.

---

## Phase D — BBH merger thesis

The actual research deliverable. Take everything above and produce a
binary black hole merger from hypergraph IC.

| # | Task | Deps | Payoff |
|---|---|---|---|
| D11 | Cauchy problem for Einstein evolution (Choquet-Bruhat) | E5 + Phase C | Existence-uniqueness for Einstein evolution |
| KN1 | Wave equation D'Alembert solution `u(t) = cos(Dt) u₀ + t·sinc(Dt) v₀` | d²=0 ✓ | Discrete-time propagator |
| KN2 | Discrete-time wave step + unitary wave propagator | KN1 | Wave evolution on hypergraph |
| H6 | BBH initial data as hypergraph | Phase C + KN1/KN2 | Two-BH IC (Kerr-Schild approx) |
| H7 | BBH evolution under candidate rule | H6 + #236 | Real Wolfram dynamics, not Poisson |
| H8 | Discrete Ψ₄ extraction matching NR waveforms | H7 | Waveform observables |
| H9 | Convergence to BBH merger spacetime | H8 + Phase C | NR-comparison theorem |

**End state:** Lean-checked theorem `bbh_merger_from_hypergraph_IC :
∃ rule R, hypergraph_IC : ExecHG ℕ, NRwaveform : ℝ → ℂ,
discreteWaveform R IC tendsto NRwaveform`.

---

## Parallel streams (don't gate critical path; do whenever a good landing presents)

### Knill theorem catalogue (KN-track)
Build out the publication-ready Knill discrete-geometry theorems on
top of d²=0 / Hodge foundation. Each is an independent landing.

- KN3 ✓ (partial): Wu inclusion-exclusion + worked examples done.
- KN8 ✓ (partial): Euler-Poincaré f-vector identity done.
- **KN14** McKean-Singer supersymmetry — direct from d²=0; needs spectral / dim-graded form spaces. Foundational.
- **KN16** Cartan magic formula `L_X = i_X d + d i_X`. Needs vector field + interior product infrastructure.
- **KN18** Brouwer-Lefschetz fixed-point. Needs hypergraph endomorphism + Lefschetz number.
- **KN15** Atiyah-Singer / Atiyah-Bott analog. Top of the Knill program.
- KN4, KN5, KN6, KN7, KN9-13, KN17, KN19, KN20 — extensions.

### Synthetic geometry (SIG-track)
Per the INFRAGEOMETRY.md framing just added.

- **SIG3 partial** — Tarski `Between` + `Cong` predicates as 1-line defs on `Hypergraph.dist`. T1–T8 as decidable Props on finite hypergraphs. Quick win.
- **SIG2** — Tarski / Hilbert axioms as Props; per-class verdicts (path / lattice / branching).
- **SIG1** — primitive constructions (`Line`, `Ray`, `Segment`, `Perpendicular`, `Parallel`).
- **SIG4** — coordinatization via shortest-path counts / Cayley embedding.
- **SIG5** — branching-construction stability (uses #234 W_1).

### Bridge architecture (deepening #231)
- **#231 heavier** — `Application` constructor from executable matches; full `singleWayStep` ↔ `MultiStep` correspondence.
- **#267** — `singleWayStep subdivisionSys H = subdivideAll H (nextFresh H)` simulation lemma. Closes the engine ↔ canonical-trajectory gap for all n.
- **#268** — Route C existential path-shape preservation fallback.

### Mathlib-equivalent infrastructure (T-track)
- **T5** Path and d-torus Laplacian spectrum closed forms.
- **#214** Wasserstein-1 distance — already substantial; some closure remaining.
- **#215** Real d-torus Wasserstein O(1/n).
- **#216** Scrub all "await Mathlib" excuses.

### IGE-track (Knill paclet port)
- **#273** Super-trace / pseudo-determinant / super-determinant.
- **#274** Betti vector + Lefschetz number from Hodge blocks. Direct from d²=0 + KN14.
- **IGE2** SimplicialSet (face/degeneracy + delta-complex).
- **IGE3** TDA (VR / Čech / persistence on infrageometry hypergraphs).
- **IGE4** Mesh-generation primitives.
- **IGE5** Formal-chain complex.

### P-track (substantive structural work, mostly future)
P1–P20 — each is a paper's worth of work. P3 (Chern-Simons), P4 (ribbon), P5 (sheaves), P6 (Koszul), P7 (homotopy colimit), P9 (action principle), P11 (interaction diagrams), P14 (blowup → RG), P19 (1-skeleton + clique-complex), etc.

### M-track (collaborator-coupled work)
- **M3** Hubert Kolcz Lie-Poisson MBQC.
- **M4** Jan Pullman IBL-∞ / BV.
- **M6** Pokorny Infrageometry paclet parity.
- **M7** Ahmed EME-tracking community post.
- **M8** Pokorny diffusion-geometry bridge.
- **M9** Tropical-geometry synthetic infrageometry.
- **M10** 3BP / dynamical-systems dimension signature.
- **M1** Ioana Milea gauge-intern coordination.

### Specific GR metrics (B-track)
- **B2** Schwarzschild Riemann tensor components.
- **B3** Schwarzschild Ricci ≡ 0.
- **B4** `schwarzschild_satisfies_vacuum_EFE`.
- **B10** Ricci symmetry for Levi-Civita connection.
- **B11** Second Bianchi identity `∇_μ G^{μν} = 0`.
- **C5** Levi-Civita existence-uniqueness (Koszul).
- **C8** Scaled discrete connection → Levi-Civita.
- **F4** Schwarzschild as explicit vacuum solution.
- **F6** Kerr as vacuum solution.

### Continuum field limits (G-track)
- **G5** Continuum limits of discrete fields.
- **G6** HepLean integration.

### Branchial / quantum (I-track residual)
- **I8** Branchial → QM Hilbert space continuum limit.
- **IQ8** EME persistence as branchial observable.
- **IQ9** Path integral over singleway causal graphs.

### Causal / Lorentzian (E-track residual)
- **E5** Cauchy surfaces + ADM decomposition (in progress).

### Heat / spectral (D / T residual)
- **D6** Long-time convergence to uniform.
- **A6** Weak convergence counting_n → Lebesgue on [0,1).
- **A7** Wasserstein-1 convergence rate O(1/n) (in progress).
- **A8** Lift measure convergence to d-torus.
- **ID7** Spectral dimension via heat-kernel trace.

### Other multiway-engine streams
- **J2** Path integral over causal graphs.
- **J3** Emergent-gravity (Jacobson/Verlinde style).
- **J5** LQG spin-foam comparison.
- **J6** AdS/CFT analog in Wolfram model.

### Publication outputs (K-track)
- **K1** P1 audit paper draft.
- **K2** P2 corrected identities paper.
- **K3** P3 infrageometry continuum-limits paper.
- **K4** P4 structural library paper.
- **K5** P5 Wolfram-to-GR bridge paper. ← *This is the BBH paper.*
- **K6** P6 branchial QM audit + formalization paper.
- **K7** P7 BBH via hypergraph paper. ← *Companion to K5.*
- **K8** P8 discrete d'Alembertian + BD-flag paper.
- **K9** P9 refutation-chain paper.

---

## Critical-path summary

```
Phase A (#233 + refactor + Minkowski re-discharge)
   ↓
Phase B (#224 + RuleSignatureSchema + #190 + MultiwayExec cleanup)
   ↓
Phase C (R4 + #218 + #217 + #225 + #235 + #236 + Lorentzian-GH track)
   ↓
Phase D (D11 + KN1/KN2 + H6 + H7 + H8 + H9)
   ↓
END: BBH merger from hypergraph IC, K5 + K7 papers.
```

**Currently sitting at: #233 lands — Phase A entry done. Two Phase A follow-ups (refactor `WassersteinRateObligation` → generic family; tie discrepancy to actual trajectory W_1) staged. Phase B unlocked.**

Active streams in parallel (will keep landing as opportunities arise):
KN14/16/18 (Hodge consequences), SIG3 partial (Tarski quick win),
#231 heavier (bridge deepening).

---

## Working principle

Per directive: don't think in sessions / time / context. Decompose.
Document. Attack the task list. Phase A first because it makes
everything downstream meaningful.
