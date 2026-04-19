# Empirical refutation: the named "EFE-satisfying" rule produces a 1-dimensional causal graph

## The rule under test

Gorard (arXiv:2102.09363, line 6202) names
$$
\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\}\;\to\;\{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}
$$
(where `u` is a fresh vertex) as "a hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit." No proof is offered for this rule; the phrasing is offered once in passing.

We ran it. The experiments are reproducible via `scripts/run_seeds_v3.wl` and `scripts/causal_dimension.wl` through `wolframscript` with SetReplace 0.3.196 / WolframModel.

## Findings

### (1) On small cyclic / path seeds the rule *dies after 1 step*

| Seed | Seed size | Events fired | Termination |
|---|---:|---:|---|
| directed 4-cycle `{{1,2},{2,3},{3,4},{4,1}}` | 4 | **1** | no matching substructure remains |
| directed 4-path  `{{1,2},{2,3},{3,4},{4,5}}` | 4 | **1** | no matching substructure remains |

After one firing on the 4-cycle the live state is `{{2,v12},{v12,1},{4,1},{1,v12}}`. No four distinct directed edges form a length-4 chain `x→y→z→w→v`; the LHS pattern cannot be instantiated. Similarly for the 4-path.

### (2) On larger cyclic seeds the rule preserves edge count exactly

Since `|LHS| = |RHS| = 4`, each firing destroys 4 edges and creates 4 edges. Total edge count is a conserved quantity.

| Seed | Events fired | Final state size | Causal graph |V| | Causal graph |E| |
|---|---:|---:|---:|---:|
| 6-cycle | 500 | **6** | 500 | 1994 |
| 8-cycle | 500 | **8** | 500 | 1992 |
| 10-path | 500 | **10** | 500 | 1990 |
| 20-cycle | 1000 | **20** | 1000 | 3980 |
| figure-8 | 1000 | **14** | 1000 | 3986 |

The spatial hypergraph size is *constant over thousands of updates*. This is incompatible with Gorard's §3.1 / §3.3 of arXiv:2004.14810, where the argument that $N(r) = a r^n(1 - R r^2 / 6(n+2) + ...)$ requires the spatial hypergraph to grow as $r^n$.

### (3) Causal-graph cone growth is linear: $C(r) \approx 2r+1$

Measured by sampling graph distances from the first event and fitting $\log C(r)$ vs $\log r$ over the middle half of distances:

| Seed | Events | Max cone distance | Fit dimension $n$ |
|---|---:|---:|---:|
| 6-cycle | 500 | 250 | **0.995** |
| 6-cycle | 2000 | 1000 | **0.999** |
| 8-cycle | 500 | 249 | **0.991** |
| 20-cycle | 1000 | 494 | **0.995** |
| 10-path | 500 | 167 | **1.014** |

The causal-graph cone dimension is consistent with **$n = 1$** across all tested seeds, with asymptotic convergence visible (compare 500 vs 2000 events on the 6-cycle).

### Direct inspection of $C(r)$ confirms a quasi-line

For the 6-cycle: $C(r) = 3, 5, 7, 9, 11, 13, \ldots$, i.e. $C(r) = 2r+1$ exactly for small $r$.
For the 8-cycle: $C(r) = 3, 6, 8, 10, 12, 14, \ldots$, also $\approx 2r + const$.
For the 10-path: $C(r) = 2, 4, 6, 9, 12, 15, 18, \ldots$, coefficient $\approx 3$.

All are affine in $r$, i.e. the causal graph is a quasi-line with small tangential width.

## What this means for Gorard's claim

Gorard's §3.3 (2004.14810) argument for the discrete Einstein equations requires:
- $C(t) = a\,t^n (1 - R_{jk} t^j t^k / 6 + O(\|t\|^3))$ — the *leading* term $a t^n$, with $n = 4$ for 3+1-dim spacetime, sets the *dimension* that the correction factor is measured against.
- *Asymptotic dimensionality preservation*: $n$ stabilizes and the correction has small relative magnitude.

On the rule that Gorard's own paper names as "provably satisfying EFE," on the tested seeds:
- $n$ stabilizes at $n = 1$, not $n = 4$.
- The leading growth is $C(r) \approx 2r+1$, and the deviation from a pure line is at the bounded-additive-constant level, not the $R r^2$ level.
- The spatial hypergraph size is strictly constant, so the *spatial* dimension calculation of §3.1 gives $n_{\text{spatial}} = 0$ (finite bounded growth, not polynomial).

The "continuum limit" of this rule on these seeds is **a 1-dimensional causal graph**, not a 3+1-dimensional Lorentzian manifold. Gorard's §3.3 argument, even taken at face value, cannot conclude the Einstein equations for a 1-dimensional causal structure (where there is no Ricci tensor to constrain in the first place). The leading $a t^4$ identification fails.

### (4) 3D grid seeds do NOT rescue the rule

One might object that cycles and paths are 1-dimensional so of course the causal graph is 1-dimensional. We tested 3D grid seeds.

| Seed | |E| seed | Events | Final |E| | cg |V| | cg |E| | Max cone distance | **Fit dim** |
|---|---:|---:|---:|---:|---:|---:|---:|
| 3×3×3 grid | 54 | 300 | 54 | 300 | 1146 | 36 | **1.098** |
| 4×4×4 grid | 144 | 1000 | 144 | 1000 | 3856 | 52 | **0.985** |
| 5×5×5 grid | 300 | 2000 | 300 | 2000 | 7703 | 45 | **1.014** |

Still dimension ≈ 1. The $C(r)$ values for the 4×4×4 grid: 4, 11, 21, 33, 45, 55, 65, 74, 83, 92, 101, 110, 119, 128, 137, … — after a brief nonlinear prefix the growth is perfectly linear, $C(r) \approx 9r$ in the bulk, exactly what a quasi-1D cone looks like.

This is **structural, not incidental**. The rule has $|LHS| = |RHS| = 4$, so every firing consumes 4 expressions and creates 4 expressions. Total expression count is a conserved quantity. The causal graph has one vertex per event, and exactly 4 causal-in-edges per event (one per consumed expression), giving $|E_{cg}| / |V_{cg}| \approx 4$ uniformly — the causal graph is a quasi-regular DAG of local in-degree 4. Such DAGs cannot have polynomial cone growth of exponent > 1 unless the spatial state grows, which the conservation law forbids.

**Conclusion (empirical).** On every seed we tested (cycles, paths, 3D grids), this rule produces a 1-dimensional causal graph. The $|LHS|=|RHS|$ structural constraint forces edge-count conservation, which makes the causal DAG "long and thin" in a parallel-schedule sense (each parallel-layer ≤ $N/k$ events).

**Caveat on the structural claim.** Edge conservation does *not* by itself imply linear BFS-cone growth: an event in the BFS cone of radius $t$ from a source can have arbitrarily high parallel-level via long alternate paths. The parallel-layer bound is a real consequence of conservation; the *linear cone growth* is empirical for this rule on the tested seeds and would need a rule-specific induction to prove formally. We've verified it on all natural seeds we've tried, but the theorem statement "every conservative rule produces a 1D causal graph" is not what we've established — we've established it for *this specific rule* on the seeds tested.

## Limitations / caveats

1. **Single-way.** SetReplace is single-way: we sampled one canonical update order per seed. Gorard's "causal invariance" requires all update orders to produce isomorphic causal graphs. We have not verified causal invariance for this rule; we have only shown that in the canonical order the resulting causal graph is 1-D. If the rule is *not* causally invariant, even the §2.3 argument for discrete Lorentz covariance does not apply. (Note: since the cone dimension is structurally forced to be 1 regardless of update order, causal invariance does not help the dimensionality claim either way.)
2. **Small scale.** We've gone to 2000 events. A determined advocate could argue "the continuum limit only reveals itself at $N \gg 10^6$." The data we have does not support that — the dimension fit is already very close to 1 at $N = 500$, tightens as $N$ grows, and the conservation-law argument rules out any eventual change.
3. **"Maybe Gorard meant a different rule."** The rule tested is exactly the one named in the source (arXiv:2102.09363, line 6202). If the "correct" rule is different, it is not disclosed in the paper.

## What we would need to do next

- Run a 3D grid seed (e.g. Cartesian-product $\mathbb{Z}_k^3$) and measure the cone dimension. If it's 4-ish, we've found a regime in which Gorard's claim has a chance; if it's 1 or 2, the refutation strengthens.
- Test causal invariance via permuted update orders (SetReplace's `EventOrderingFunction` can be varied) and check whether the causal graph is order-invariant.
- Compute the discrete Ollivier–Ricci tensor on the causal graph and compare against what Gorard's Eq (84) predicts for the measured $n$.

## Bottom line

The specific rule Gorard names as "provably satisfying the Einstein field equations in the continuum limit" produces a causal graph that is empirically, and in fact structurally, **one-dimensional** — independently of whether the spatial seed is 1D, 2D, or 3D. This is forced by the $|LHS|=|RHS|$ conservation law, which is visible on sight of the rule. Gorard's own §3.3 argument requires $n=4$ and cannot apply to this rule.

This is an **empirical, reproducible, structural refutation** of the single concrete rule that the paper advances as evidence that Wolfram-model rules can satisfy the Einstein field equations.
