# Plan: #232 edge-subdivision rule + n-step path-shape theorem

**Status**: planning artefact, drafted 2026-04-26.
**Owner**: in_progress task #232.
**Route**: B (parallel-definition + simulation bridge), with C (existential weakening) as pre-decided fallback.

---

## 1. Goal

Prove the load-bearing single-step lemma

```
singleWayStep subdivisionSys (pathEdges vs)
  = pathEdges (subdivideVerts vs (listMax vs + 1))
```
for any `vs : List ℕ` with `vs.Nodup` and `2 ≤ vs.length`, where `subdivisionSys` is the rule `{a, b} → {a, c}, {c, b}` and `subdivideVerts vs b` interleaves `vs` with fresh midpoints starting at `b`.

By iterating, this gives the n-step closed form

```
singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)
```
and the corollary edge-count `= 2^n` / vertex-count `= 2^n + 1` for **all** `n`, not just for the small `n` that `decide` can handle.

## 2. Why it matters

This is the **first end-to-end rule trajectory → continuum target** discharge. With this lemma + `PathWasserstein.lean` (existing #214 W_1 / scaled-pathMetric infrastructure), #234 derives an O(1/2^n) Wasserstein-1 convergence rate from the rule's iterates to Lebesgue measure on `[0, 1]`. Concrete answer to "do Wolfram rules produce continuum geometry?" for one rule.

Also: the *simulation lemma* (engine side) is reusable infrastructure for any future "subdivide each match independently" rule. The math side is reusable for any closed-form analysis of subdivision-style rule outputs.

## 3. Route B — parallel definition + simulation bridge

Two-phase proof. Each phase is a separate, atomic deliverable.

### Phase 1 (math side) — `subdivideAll = pathEdges ∘ subdivideVerts`

Introduce a parallel definition of subdivision **on the executable type**, bypassing the engine's `allMatches` / `foldl` machinery:

```lean
/-- For each edge of `H` indexed by `i`, replace `[a, b]` with
    `[a, baseFresh + i], [baseFresh + i, b]`. Pure list manipulation;
    no engine semantics. -/
def subdivideAll (H : ExecHG ℕ) (baseFresh : ℕ) : ExecHG ℕ :=
  (H.zipIdx.map (fun (e, i) =>
    [⟨[e.verts.head?.getD 0, baseFresh + i], by decide⟩,
     ⟨[baseFresh + i, e.verts.tail.head?.getD 0], by decide⟩])).flatten
```

(Exact signature TBD — likely cleaner via pattern-match on `e.verts`, with a fallback for non-2-edges that doesn't trigger on path-shape inputs.)

Then prove

```lean
theorem subdivideAll_pathEdges (vs : List ℕ)
    (h_len : 2 ≤ vs.length) (h_nodup : vs.Nodup) (b : ℕ) :
    subdivideAll (pathEdges vs) b
      = pathEdges (subdivideVerts vs b)
```

by induction on `vs` with the `pathEdges_cons_cons` recursion (already in `SubdivisionPath.lean`). Pure list combinatorics. No engine code involved.

### Phase 2 (engine side) — simulation lemma

Prove

```lean
theorem singleWayStep_subdivisionSys_eq_subdivideAll
    (H : ExecHG ℕ) (h : IsPath H) :   -- some structural predicate
    singleWayStep subdivisionSys H
      = subdivideAll H (nextFresh H)
```

(`IsPath H` to be made precise — likely `∃ vs, IsPathOf H vs ∧ vs.Nodup ∧ 2 ≤ vs.length`.)

This is the hard piece. The proof unpacks `singleWayStep`'s foldl and matches it against `subdivideAll`'s direct construction. Three sub-lemmas:

#### S1: match-count
```
|allMatches subdivisionRule (pathEdges vs)| = vs.length - 1
```
Each binding `ρ` matches iff `(ρ 0, ρ 1)` is a consecutive pair of `vs`. Bijection via `(a, b) ↦ ρ_{a,b}`.

#### S2: match-order
```
allMatches subdivisionRule (pathEdges vs) = [ρ_(v₀, v₁), ρ_(v₁, v₂), …, ρ_(vₘ₋₁, vₘ)]
```
in this exact order. Follows from how `allFunctions 2 (vertexList H)` does the outer-`vs` × inner-`vs` Cartesian flatMap. Requires that `vertexList H` lists the path's vertices in traversal order — caveat: Mathlib's `dedup` keeps **last** occurrence, so the visible `vertexList` may not be in path order. If it isn't, S2 needs adjustment to track the actual order.

#### S3: foldl invariant
```
After processing matches [ρ_0, …, ρ_{k-1}] starting from (H, 0):
  state = removeEdges H (consumed_0..k-1) ++ produced_0..k-1
        = (path edges k..m-1) ++ produced_0..k-1
  off = k
```
Each consumed edge is in the foldl-current state because produced edges have fresh vertices `≥ baseFresh > max(vs)` so cannot equal any consumed edge.

Combine S1+S2+S3: foldl over `m` matches of step `(remove 1, append 2)` gives final state with `2m` edges, structured as `produced_0 ++ … ++ produced_{m-1}` which by inspection equals `subdivideAll H baseFresh`.

### Iteration to n-step form

Once both phases land:

```lean
theorem singleWayEvolve_subdivision_eq_pathEdges (n : ℕ) :
    singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)
```
by induction on `n`, base `rfl`, step uses Phase 1 + Phase 2 + `IsPath` preservation.

Then count corollaries (edges = `2^n`, vertices = `2^n + 1`) drop out trivially.

## 4. Lemma DAG with difficulty + Mathlib API

| Lemma | Phase | Difficulty | Mathlib API expected |
|---|---|---|---|
| `subdivideAll` definition | 1 | trivial | `List.zipIdx`, `List.map`, `List.flatten` (or use `List.flatMap` directly) |
| `subdivideAll_pathEdges` | 1 | medium | `pathEdges_cons_cons` (existing), `subdivideVerts_cons_cons` (existing), `List.zipIdx_cons` |
| `IsPath` predicate | 2 | trivial | direct `Exists` |
| S1 match-count `|allMatches| = vs.length - 1` | 2 | hard | `List.countP_eq_length_filter`, careful counting over `allFunctions 2 vs`; bijection lemma `(a,b) ↔ ρ` via `List.Nodup.length_eq_card_toFinset` |
| S2 match-order | 2 | hard | direct list-equality proof unpacking `allFunctions` recursion; may need helper `allFunctions_cons` lemma stated separately |
| S3 foldl invariant | 2 | hard | `List.foldl_eq_of_invariant` pattern; manual induction; `List.erase_append_left` |
| Combine simulation | 2 | medium | tie S1+S2+S3 together, structural manipulation |
| Iteration `singleWayEvolve_subdivision_eq_pathEdges` | — | easy | induction on n, uses both phases |
| Edge-count corollary | — | trivial | `pathEdges_length` (existing) + `subdVerts_length` (existing) |

## 5. Pre-decided descopes

**Trigger 1**: Phase 1 (`subdivideAll_pathEdges`) exceeds ~80 lines.
- *Action*: ship Phase 1 as-is, accept Route C-style existential weakening for Phase 2. We still gain `subdivideAll` as reusable infrastructure.

**Trigger 2**: Phase 2 simulation lemma exceeds ~200 lines (signal: any single sub-lemma S1/S2/S3 exceeds ~80 lines).
- *Action*: drop Phase 2 entirely. Re-state target as the existential
  ```
  ∀ n, ∃ vs, IsPathOf (singleWayEvolve subdivisionSys subdSeed n) vs
            ∧ vs.length = 2^n + 1 ∧ vs.Nodup
  ```
  Prove by induction on `n` with a *structural* induction step that doesn't track the exact vs (just shows path-shape is preserved + length doubles minus 1). This is the original Route C. Estimate ~150 lines. Sufficient for #234.

**Trigger 3**: Even Route C structural induction step blocks (e.g., S1 match-count is itself ~100 lines).
- *Action*: prove count-only theorem `(singleWayEvolve … n).length = 2^n` for arbitrary n via the foldl-length upper-bound argument I started before. The lower bound + path-shape preservation get marked as future work; #234 gets discharged with a count-only certificate (downgrades from "exact path Wasserstein" to "Wasserstein bounded by const · 2^(-n) using only edge count + diameter"). Estimate ~80 lines, no S1/S2/S3 needed.

## 6. Execution order

1. **Phase 1 first** — atomic commit, lands clean math regardless of Phase 2 status.
2. **Phase 2 sub-lemmas in order**: `IsPath` predicate (trivial) → S1 (hard, do first because S2 and S3 use match list as a primitive) → S2 → S3 → simulation combine.
3. **Iteration + corollaries** last, trivial once Phase 1 and Phase 2 land.

Each sub-lemma is its own commit + axiom check.

## 7. Open questions for the math whiteboard

Before starting Phase 2, verify on small examples (n = 2, 3) via Mathematica or `#eval`:

- **Q1**: Is `vertexList (pathEdges vs)` actually in path-traversal order, or in `dedup` order (last occurrence)? Needed for S2.
  - From the `/tmp/sw_trace.lean` output: at n=2, `verts = [1, 4, 3, 5, 2]` which IS the path-traversal order. So `dedup` happens to land on path order here. But this is incidental — depends on how `flatMap` interleaves and which occurrence is "last". Should pin down precisely whether this holds for arbitrary n or only this trajectory.
- **Q2**: Does `allFunctions 2 vs` enumerate as outer-`a`-then-inner-`b`, or some other order?
  - From inspection: `allFunctions 2 vs = vs.flatMap (fun a => vs.map (fun b => fun i => if i.val = 0 then a else b))`. So order is `(a₀, b₀), (a₀, b₁), …, (a₀, bₘ), (a₁, b₀), …`. For a path with `vs = [v₀, …, vₘ]`, the matching pairs `(vᵢ, vᵢ₊₁)` come out in i-order. ✓
- **Q3**: Sanity-check that `produced_0 ++ produced_1 ++ … ++ produced_{m-1}` equals `subdivideAll`'s output for one concrete case (n=2).

## 8. Stub scaffolding

Architecture stub will live in `/tmp/sub_path_stub.lean` (NOT in the project). All sub-lemmas with `sorry`. Used to type-check the architecture before committing real proofs. Filled bottom-up; signatures move to `lean/InfraFormalization/SubdivisionPath.lean` only when their proofs are filled.
