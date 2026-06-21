# Universal-theorem upgrade candidates

The native_decide overreach audit (task #494) identified docstring claims that
overreached from finite verification. The accompanying scrub removed the
overclaim language. **Three upgrades** are the highest-impact candidates for
lifting finite native_decide checks to real universal theorems.

Each is tracked as a numbered task.

## #495 — Per-edge additivity (HIGHEST IMPACT)

**Claim.** For a single-edge-LHS rule `r` (`r.lhs.length = 1`):

```
∀ seed d, knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ seed d)
            = (# distinct edges of seed) · knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ edge12 d)
```

**Current state.** Verified at finitely many (rule, seed, depth) tuples
across `UniversalAdditivity.lean`, `BranchialUniversalAdditivity.lean`,
`StableDiscoveredRules.lean`, `DiscreteRicciScalar.lean`,
`BBHCurvatureEvolution.lean`, `BBHDeepEvolution.lean`, `BBHMetricTensor.lean`,
`CurvatureDensityLimit.lean`, `DiscreteBondiFlux.lean`,
`DiscreteMetricTensor.lean`, `BBHBranchialMultiDepth.lean`, …

**Why it's #1.**
- Load-bearing for every BBH calculation, every "Phase-D capstone" prediction,
  the discrete Einstein-Hilbert framing, the `7×` BBH multiplier. Currently
  all sit on this as a finite check. Lifting it makes every downstream
  BBH/Phase-D number a real theorem instead of an extrapolation.
- Project-original (not in Knill or Gorard). Would be the project's signature
  structural result.

**Tractable attack path.**
1. Prove `knillEulerScaled` is additive over disjoint unions of hypergraphs
   (`H = H₁ ⊔ H₂` with `V(H₁) ∩ V(H₂) = ∅` ⇒ `Σ K6 = Σ_{H₁} K6 + Σ_{H₂} K6`).
   **Pure combinatorial — provable now, no engine semantics.**
2. Prove `knillEulerScaled` is invariant under vertex bijection.
   **Pure combinatorial — provable now.**
3. Prove engine commutes with disjoint union for single-edge-LHS rules
   (modulo fresh-vertex relabeling). **Engine-semantics — harder.**
4. Compose to get `disjoint_per_edge_additivity` for vertex-disjoint seeds.
5. Apply to BBH initial data (7 disjoint edges by construction) to derive
   `Knill(BBH, d) = 7 · Knill(edge12, d)` **universally in d** — closes
   the `7×` claim.

**Connected-seed case** (`path123`, `triangle`, ...) requires a tree-
decomposition argument on the causal DAG itself: each binding initiates an
independent sub-DAG of subsequent events, despite seed vertex-sharing,
because causal edges in our framework are edge-level (produce/consume), not
vertex-level. Multi-session.

## #496 — Knill = 6·χ for triangulated d-manifolds

**Claim.** `Σ_v K6(v) = 6·χ(H) = 6·(V − E + F + …)` for any finite hypergraph.

**Current state.** Verified on 3 S² triangulations (tetra/octa/icosa) in
`KnillDiscreteGaussBonnet.lean`, 3 triangulated tori (n ∈ {4,5,6}) in
`KnillHigherGenus.lean`, and ∂Δ⁴ (= K₅, a 3-manifold) in
`KnillThreeManifold.lean`.

**Why.**
- It's **Knill's own theorem** (arxiv:1009.2292, Theorem 1). We're not
  pioneering; we're formalizing literature. Citing the proof we'd be writing
  is honest.
- Closes a chain: every `triangulation → χ` finite check becomes a corollary
  of one universal theorem.
- Pure combinatorics — no engine semantics. Most tractable of the three.

**Proof sketch (direct telescoping).**

```
Σ_v K6(v) = Σ_v Σ_k (-1)^k · (# k-cliques at v) / (k+1)
          = Σ_k (-1)^k · (1/(k+1)) · Σ_v (# k-cliques at v)
          = Σ_k (-1)^k · (1/(k+1)) · (k+1) · n_k     [each k-clique counted k+1 times]
          = Σ_k (-1)^k · n_k
          = χ(H)
```

The `· 6` scaling factor in `knillEulerScaled` then gives `6·χ`.

## #497 — Path / cycle / torus closed-form scalars

**Claim.** Combinatorial closed forms for unweighted curvature scalars:

- `Forman(path_n) = 4` for all n ≥ 3
- `Higuchi(path_n) = 2` for all n ≥ 3
- `SquareCount(path_n) = 0` for all n ≥ 3
- `Forman(T^d(n,…,n)) = -8 d (d−1) · n^d` for all d, n ≥ ?
- `Higuchi(T^d) = (2 − 2d) · n^d`

**Current state.** Verified at finite samples in `PathContinuumLimit.lean`,
`CycleContinuumLimit.lean`, `NormalizedDensityLimits.lean`,
`PolynomialDensityLimits.lean`, `GridContinuumLimit.lean`.

**Why.**
- The `*_lattice_multiscalar_continuum_limit` theorems currently bundle
  TRIVIAL constant-function convergences (`TrueLimitConverges
  constantFourTrace 4`) with finite spot checks. Proving the shape lemmas
  universally would convert them into real `path_n → [0,1]`, `T^d → continuum`
  convergence theorems — which is what they're named for.
- Pure combinatorics. Forman scalar of a path/cycle is a per-vertex sum
  determined entirely by vertex degree; path degrees are `[1, 2, 2, …, 2, 1]`,
  cycle is `[2, 2, …, 2]`. Closed-form sum is immediate.
- Unlocks the Ricci-of-S¹ / T^d bridge.

## Anti-candidates (do NOT upgrade)

- **`LiteratureRules` "emergent geometry"** — `EMERGENT 2D EUCLIDEAN SPACE` /
  `HYPERBOLIC emergence` / `SQUARE emergence`. These are interpretive
  overlays, not theorems. Hedging (already done in #494) is the right
  disposition.
- **`PersistentRDegeneracy` R = 0 from d ≥ 3** — too rule-specific to be
  impactful as a universal claim.
- **`RulePreservationClassification` "any well-designed catalog"** — meta-
  claim that can't be formalized without a much heavier substrate.
- **H9 distinct-edge tripling (#492)** — already in progress; lower priority
  than #495 because per-edge additivity has wider downstream payoff for the
  same engine-semantics effort.

## Status

- **#495** (in progress): per-edge additivity. K1 + K2 closed
  (`K1_proved`, `K2_proved` in `PerEdgeAdditivityFramework.lean`).
  BBH-disjointness reframed to **EdgeCausallyDisjoint** (BBH is NOT
  vertex-disjoint; correct property is edge-causal disjointness of
  the causal sub-DAGs, empirically verified at d=2 via
  `probe_bbh_causal_decomp.lean`). Remaining work decomposed below.
- **#496** (in progress): Knill = 6·χ.
- **#497** (pending): path/cycle/torus closed forms.

### #495 decomposition (sub-tasks)

- **#498 (#495a)** — Fresh-vertex partition lemma for single-edge-LHS
  rules. Direct from singleWayStep's offset accumulator.
- **#499 (#495b)** — Partition closure under singleWayStep (events
  stay in their step-0-rooted partition). Multi-session.
- **#500 (#495c)** — Step-0 ancestor function: existence + uniqueness
  (R1 of EdgeCausallyDisjoint).
- **#501 (#495d)** — Causal sub-DAGs vertex-disjoint in the causal
  DAG (R2 of EdgeCausallyDisjoint).
- **#502 (#495e)** — Compose K1 + K2 to per-edge Knill additivity
  (closes `EdgeCausalDisjoint_implies_knill_additive`).
- **#503 (#495f)** — BBH instance: bbhInitial satisfies
  EdgeCausallyDisjoint (closes BBH 7× theorem universally in d).

Updated after task #494's audit-and-scrub of native_decide overreach
(commits `7f8f1b8`, `a6674b5`, `454d8cd`) and #495 K1+K2 closure
(commit `89795ca`) and BBH framing correction (commit `0b5f437`).
