# Plan for item #232: the edge-subdivision rule and its n-step path theorem

Lean file: `lean/InfraFormalization/SubdivisionPath.lean`. The rule `subdivisionSys` is {a, b} → {a, c}, {c, b} with c fresh, and the seed `subdSeed` is the single edge [1, 2].

## 1. Target

The target theorem, with proposed name `singleWayEvolve_subdivision_eq_pathEdges`, is

```
singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)
```

for every n, with the corollaries edge count 2^n and vertex count 2^n + 1. It follows by induction on n from the single-step lemma

```
singleWayStep subdivisionSys (pathEdges vs)
  = pathEdges (subdivideVerts vs (listMax vs + 1))
```

for `vs.Nodup` and `2 ≤ vs.length`, where `subdivideVerts vs b` interleaves `vs` with the fresh midpoints b, b + 1, ...

`singleWayStep` applies a maximal set of edge-disjoint matches, chosen greedily in enumeration order. On a path every edge is a match of the one-edge left-hand side and the matches are pairwise edge-disjoint, so the step subdivides every edge.

## 2. Status

| Statement | Lean | Status |
|---|---|---|
| `subdivideAll (pathEdges vs) b = pathEdges (subdivideVerts vs b)` for `2 ≤ vs.length` | `subdivideAll_pathEdges` (`SubdivisionPath.lean:412`) | PROVED |
| `subdivisionTrajectory n := pathEdges (subdVerts n)` has 2^n edges, is a path on `subdVerts n`, and `subdivisionTrajectory (n+1) = subdivideAll (subdivisionTrajectory n) (listMax (subdVerts n) + 1)` | `subdivisionTrajectory_length`, `subdivisionTrajectory_isPathOf`, `subdivisionTrajectory_succ` | PROVED |
| Engine closed form at n = 0 | `singleWayEvolve_subdivision_zero`, `subdivisionTrajectory_eq_engine_at_zero` | PROVED (`rfl`) |
| Engine closed form at n = 1, 2, 3, 4 | `example`s at lines 450-459 and 630-635 | PROVED by `decide` |
| Engine closed form at n = 3, 4, 5 | `example`s at lines 462-471 | PROVED-WITH-NATIVE-DECIDE |
| One edge [a, b] goes to [a, max a b + 1], [max a b + 1, b] | `example`s at lines 541-585 for fixed (a, b) by `decide`; `singleWayStep_subdivisionSys_consEdge_fin8`, `_fin12`, `_high` | `decide` cases PROVED; the `Fin 8`, `Fin 12` and high-value theorems PROVED-WITH-NATIVE-DECIDE |
| Simulation lemma `singleWayStep subdivisionSys H = subdivideAll H (nextFresh H)` for path-shaped H | none | OPEN |
| Closed form for every n | none | OPEN; follows from the simulation lemma and `subdivideAll_pathEdges` |

`subdivisionTrajectory` is defined directly as `pathEdges (subdVerts n)`. Its equality with the engine output is PROVED for n ≤ 4 (kernel `decide`) and n = 5 (`native_decide`), and OPEN for larger n.

## 3. Relation to the Wasserstein rate

`WassersteinRate.subdivisionDiscrepancy n = 1/2^n` is defined directly in `WassersteinRate.lean:55`. It is not computed from any measure on the subdivided path or from the engine output. `subdivisionDiscrepancy_satisfies_obligation` proves `1/2^n ≤ 1/n` for n ≥ 1. `WassersteinRateObligation d` concerns a caller-supplied sequence d and is also satisfied by the zero sequence (`wassersteinRateObligation_zero`). The statements about the subdivision rate are therefore VACUOUS with respect to the convergence of the rule's iterates to Lebesgue measure on [0, 1].

`PathWasserstein.lean` proves facts about W_1 between point masses on a path: `wasserstein1_pathDelta_eq_hypergraphDist` (W_1 equals the graph distance) and `wasserstein1_pathDelta_scaled_eq` (W_1 for the metric scaled by 1/n equals the graph distance divided by n). A convergence statement for the subdivision rule needs a W_1 bound between the uniform measure on the vertices of `subdivisionTrajectory n`, embedded in [0, 1], and Lebesgue measure. This is OPEN.

## 4. Proof plan for the simulation lemma (OPEN)

The proof unfolds the fold in `stepFold` and compares it with `subdivideAll`. With `vs = [v₀, ..., vₘ]` and H = `pathEdges vs`:

- S1 (match count): `(allMatches subdivisionRule H).length = m`. A binding ρ is a match iff (ρ 0, ρ 1) is a consecutive pair of `vs`.
- S2 (match order): `allMatches subdivisionRule H = [ρ_(v₀,v₁), ..., ρ_(vₘ₋₁,vₘ)]`. `allFunctions 2 vs` enumerates pairs (a, b) with a in the outer loop and b in the inner loop, so the order of matches follows the order of `vertexList H`. `vertexList` uses `dedup`, which keeps the last occurrence of each vertex; at n = 2 it gives `[1, 4, 3, 5, 2]`, the order along the path. A proof for all paths needs a lemma on `vertexList (pathEdges vs)`, and possibly a helper lemma `allFunctions_cons` for the recursion of `allFunctions`.
- S3 (fold invariant): after the first k matches, `avail` is the path edges k, ..., m − 1, `produced` is the subdivided edges 0, ..., k − 1, and the fresh-vertex offset is k. Each consumed edge is still available because the produced edges contain fresh vertices greater than `listMax vs`.

S1, S2 and S3 give `singleWayStep subdivisionSys H = subdivideAll H (nextFresh H)`; `nextFresh_pathEdges` (`SubdivisionPath.lean:319`, PROVED) states `nextFresh (pathEdges vs) = listMax vs + 1`.

## 5. Fallbacks

1. If the simulation lemma is not proved: prove `∀ n, ∃ vs, IsPathOf (singleWayEvolve subdivisionSys subdSeed n) vs ∧ vs.length = 2^n + 1 ∧ vs.Nodup` by an induction that tracks the path shape and not the exact vertex list.
2. If fallback 1 is not proved: prove the edge count `(singleWayEvolve subdivisionSys subdSeed n).length = 2^n` for every n.
