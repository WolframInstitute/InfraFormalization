/-
**Edge-subdivision rule + n-step path-shape theorem** (#232).

The edge-subdivision rule `{a, b} → {a, c}, {c, b}` (with `c` fresh)
applied via `singleWayEvolve` from a single-edge seed `{1, 2}`
produces, at step `n`, a path-shaped hypergraph with exactly `2^n`
edges and `2^n + 1` vertices.

This is the canonical hypergraph-anchored trajectory feeding into
`PathWasserstein.lean` and the W_1-convergence obligations
(#234): the *state itself* at step `n` is a path on `2^n + 1`
vertices, so the consumer-site path-metric and Wasserstein bounds
apply directly to the rule's output.

**Proof strategy.** A `IsPathOf H vs` predicate captures the
invariant: `H` is the list of consecutive-pair hyperedges of a
nodup ℕ-list `vs` of length ≥ 2. We show:
  * `subdSeed` satisfies `IsPathOf [1, 2]`.
  * `singleWayStep subdivisionSys` preserves `IsPathOf`, with the new
    vertex list being `vs` interleaved with fresh midpoints, doubling
    edge count from `vs.length - 1` to `2(vs.length - 1)` and
    vertex count from `vs.length` to `2 vs.length - 1`.
  * Iterating `n` times: `vs.length = 2^n + 1`, edge count `2^n`.

The inductive step is the load-bearing lemma — it requires reasoning
about `allMatches` enumeration order on the path's vertex list and
the `removeEdges`/`++ produced` foldl in `singleWayStep`.
-/

import InfraFormalization.MultiwayExec
import Mathlib.Data.Finset.Card

namespace InfraFormalization
namespace MultiwayExec

open Hypergraph

/-! ## Path-state predicate -/

/-- The edge between consecutive ℕ vertices `a` and `b`. -/
@[simp] def consEdge (a b : ℕ) : Hyperedge ℕ :=
  ⟨[a, b], List.cons_ne_nil a [b]⟩

/-- Build a path's edge list from its vertex sequence. -/
def pathEdges (vs : List ℕ) : ExecHG ℕ :=
  vs.zipWith consEdge vs.tail

/-- `H` is the path with vertex sequence `vs` (in traversal order). -/
def IsPathOf (H : ExecHG ℕ) (vs : List ℕ) : Prop :=
  2 ≤ vs.length ∧ vs.Nodup ∧ H = pathEdges vs

/-! ## Subdivision rule (re-stated locally for self-contained reasoning) -/

private def sLhs : Hyperedge (Fin 2) := ⟨[0, 1], List.cons_ne_nil _ _⟩
private def sRhsL : Hyperedge (Fin 3) := ⟨[0, 2], List.cons_ne_nil _ _⟩
private def sRhsR : Hyperedge (Fin 3) := ⟨[2, 1], List.cons_ne_nil _ _⟩

/-- The edge-subdivision rule: `{a, b} → {a, c}, {c, b}` with `c` fresh. -/
def subdivisionRule : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [sLhs]
  rhs := [sRhsL, sRhsR]

def subdivisionSys : ExecSystem := ⟨[subdivisionRule]⟩

/-- Seed: a single edge `{1, 2}`. -/
def subdSeed : ExecHG ℕ := [consEdge 1 2]

/-! ## The seed is path-shaped -/

theorem subdSeed_isPathOf : IsPathOf subdSeed [1, 2] := by
  refine ⟨by decide, by decide, ?_⟩
  rfl

/-! ## n-step trajectory and counts

The interleaved vertex sequence at step `n+1`: between every pair
`(vs[i], vs[i+1])` we insert a fresh midpoint `baseFresh + i`,
where `baseFresh = max(vs) + 1`. -/

/-- Interleave `vs` with `baseFresh + i` between position `i` and `i+1`. -/
def subdivideVerts (vs : List ℕ) (baseFresh : ℕ) : List ℕ :=
  match vs with
  | [] => []
  | [v] => [v]
  | v :: w :: rest =>
    v :: baseFresh :: subdivideVerts (w :: rest) (baseFresh + 1)

@[simp] theorem subdivideVerts_nil (b : ℕ) : subdivideVerts [] b = [] := rfl

@[simp] theorem subdivideVerts_singleton (v b : ℕ) :
    subdivideVerts [v] b = [v] := rfl

@[simp] theorem subdivideVerts_cons_cons (v w : ℕ) (rest : List ℕ) (b : ℕ) :
    subdivideVerts (v :: w :: rest) b
      = v :: b :: subdivideVerts (w :: rest) (b + 1) := rfl

/-- Length recurrence: `subdivideVerts vs b` has `2 * vs.length - 1` elements
when `vs.length ≥ 1`. -/
theorem subdivideVerts_length (vs : List ℕ) (h : 1 ≤ vs.length) (b : ℕ) :
    (subdivideVerts vs b).length = 2 * vs.length - 1 := by
  induction vs generalizing b with
  | nil => simp at h
  | cons v rest ih =>
    cases rest with
    | nil => simp
    | cons w rest' =>
      have h_rest : 1 ≤ (w :: rest').length := by simp
      have ih' := ih h_rest (b + 1)
      simp only [subdivideVerts_cons_cons, List.length_cons, ih']
      omega

/-! ## Closed-form vertex sequence

`subdVerts n` is the path-vertex sequence after `n` single-way
subdivision steps starting from `[1, 2]`. Each step interleaves the
current sequence with fresh midpoints starting at `nextFresh` of the
current path. -/

/-- Maximum entry of a list of ℕ; 0 for the empty list. -/
def listMax (vs : List ℕ) : ℕ := vs.foldr Nat.max 0

@[simp] theorem listMax_nil : listMax [] = 0 := rfl

@[simp] theorem listMax_cons (v : ℕ) (vs : List ℕ) :
    listMax (v :: vs) = Nat.max v (listMax vs) := rfl

/-- Iterated vertex sequence; `subdVerts n` is the path's vertex list
at step `n`. -/
def subdVerts : ℕ → List ℕ
  | 0 => [1, 2]
  | n+1 =>
    let vs := subdVerts n
    subdivideVerts vs (listMax vs + 1)

@[simp] theorem subdVerts_zero : subdVerts 0 = [1, 2] := rfl

theorem subdVerts_succ (n : ℕ) :
    subdVerts (n+1) = subdivideVerts (subdVerts n) (listMax (subdVerts n) + 1) :=
  rfl

/-! ## Vertex-count theorem (closed form, proved by induction) -/

/-- `subdVerts n` always has length ≥ 2. -/
theorem subdVerts_length_ge_two (n : ℕ) : 2 ≤ (subdVerts n).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [subdVerts_succ, subdivideVerts_length _ (by omega)]
    omega

/-- `subdVerts n` has exactly `2^n + 1` vertices. -/
theorem subdVerts_length (n : ℕ) :
    (subdVerts n).length = 2^n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hge : 1 ≤ (subdVerts n).length := by
      have := subdVerts_length_ge_two n
      omega
    rw [subdVerts_succ, subdivideVerts_length _ hge, ih, Nat.pow_succ]
    generalize 2^n = k
    omega

/-- `pathEdges vs` has `vs.length - 1` edges. -/
@[simp] theorem pathEdges_length (vs : List ℕ) :
    (pathEdges vs).length = vs.length - 1 := by
  unfold pathEdges
  rw [List.length_zipWith, List.length_tail]
  omega

/-- Recursive shape of `pathEdges`. The case-split is on the head pair. -/
@[simp] theorem pathEdges_nil : pathEdges ([] : List ℕ) = [] := rfl

@[simp] theorem pathEdges_singleton (v : ℕ) : pathEdges [v] = [] := rfl

@[simp] theorem pathEdges_cons_cons (v w : ℕ) (rest : List ℕ) :
    pathEdges (v :: w :: rest) = consEdge v w :: pathEdges (w :: rest) := by
  unfold pathEdges
  rfl

/-- `flatMap (·.verts)` of `pathEdges` is the "edge-traversal trace":
the interior vertices appear twice each, endpoints once.
For `vs = v :: w :: rest`, the trace decomposes as `v :: w :: trace (w :: rest)`. -/
theorem pathEdges_flatMap_verts_cons_cons (v w : ℕ) (rest : List ℕ) :
    (pathEdges (v :: w :: rest)).flatMap (·.verts)
      = v :: w :: (pathEdges (w :: rest)).flatMap (·.verts) := by
  rw [pathEdges_cons_cons]
  simp [List.flatMap_cons, consEdge]

@[simp] theorem pathEdges_flatMap_verts_singleton_pair (v w : ℕ) :
    (pathEdges [v, w]).flatMap (·.verts) = [v, w] := by
  simp [pathEdges, consEdge]

/-- Membership in the flatMap of `pathEdges vs` is exactly membership in `vs`,
when `vs` has at least two elements. -/
theorem mem_pathEdges_flatMap (vs : List ℕ) (h : 2 ≤ vs.length) (x : ℕ) :
    x ∈ (pathEdges vs).flatMap (·.verts) ↔ x ∈ vs := by
  induction vs with
  | nil => simp at h
  | cons v rest ih =>
    cases rest with
    | nil => simp at h
    | cons w rest' =>
      cases rest' with
      | nil =>
        simp
      | cons x' rest'' =>
        rw [pathEdges_flatMap_verts_cons_cons]
        have h_inner : 2 ≤ (w :: x' :: rest'').length := by simp
        have ih' := ih h_inner
        simp only [List.mem_cons, ih']
        tauto

/-! ## Edge-count theorem for `singleWayEvolve`

Combining the closed-form `subdVerts n` (length `2^n + 1`) with the
intent that `singleWayEvolve subdivisionSys subdSeed n` produces
`pathEdges (subdVerts n)` gives `2^n` edges and `2^n + 1` vertices.
The full inductive proof of the equality
  `singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)`
is the load-bearing remaining work for #232. The skeleton above sets
up the closed-form vertex sequence; below is the goal statement and
the verified base case. -/

/-- `vertexList` of `pathEdges vs` has the same length as `vs`, when
`vs` is `Nodup` with at least two elements. The actual list is a
permutation of `vs` (Mathlib's `dedup` keeps the last occurrence;
order may differ from `vs`). -/
theorem vertexList_pathEdges_length (vs : List ℕ)
    (h : 2 ≤ vs.length) (h_nodup : vs.Nodup) :
    (vertexList (pathEdges vs)).length = vs.length := by
  show ((pathEdges vs).flatMap (·.verts)).dedup.length = vs.length
  have h_mem : ∀ x, x ∈ (pathEdges vs).flatMap (·.verts) ↔ x ∈ vs :=
    fun x => mem_pathEdges_flatMap vs h x
  have h_toFinset :
      ((pathEdges vs).flatMap (·.verts)).toFinset = vs.toFinset := by
    ext x
    simp [List.mem_toFinset, h_mem]
  rw [← List.card_toFinset, h_toFinset, List.toFinset_card_of_nodup h_nodup]

/-- The trajectory's path-vertex sequence has `2^n + 1` elements at
step `n`; this is the count we want to read off from
`singleWayEvolve subdivisionSys subdSeed n`. -/
@[simp] theorem subdVerts_pathEdges_length (n : ℕ) :
    (pathEdges (subdVerts n)).length = 2^n := by
  rw [pathEdges_length, subdVerts_length]
  have : 1 ≤ 2^n := Nat.one_le_two_pow
  omega

/-- Base case: `singleWayEvolve` at `n = 0` is the seed itself, which
equals the path with vertex list `[1, 2]`. -/
theorem singleWayEvolve_subdivision_zero :
    singleWayEvolve subdivisionSys subdSeed 0 = pathEdges (subdVerts 0) := by
  rfl

/-! ## Phase 1 of #232 — `subdivideAll = pathEdges ∘ subdivideVerts` (math side)

We introduce a *parallel* definition `subdivideAll` that subdivides
each edge of a hypergraph independently — bypassing the engine's
`allMatches` / `foldl` machinery. This phase proves
`subdivideAll (pathEdges vs) b = pathEdges (subdivideVerts vs b)`,
the closed-form math content of #232's theorem.

Phase 2 (the *simulation lemma* connecting `singleWayStep` to
`subdivideAll`) is staged separately. See
[`notes/232_subdivision_path_plan.md`](../../notes/232_subdivision_path_plan.md). -/

/-- **Edge subdivision**: replace a 2-edge `[a, b]` with the pair
`[a, c], [c, b]`. Non-2-edges are left unchanged (this case never
occurs in the path-shape input we consume). -/
def subdivideEdge (e : Hyperedge ℕ) (c : ℕ) : ExecHG ℕ :=
  match e.verts with
  | [a, b] => [consEdge a c, consEdge c b]
  | _ => [e]

@[simp] theorem subdivideEdge_consEdge (a b c : ℕ) :
    subdivideEdge (consEdge a b) c = [consEdge a c, consEdge c b] := by
  unfold subdivideEdge consEdge; simp

/-- **Subdivide each edge**: walk the edge list, replacing the i-th
edge `[a, b]` with `[a, baseFresh + i], [baseFresh + i, b]`. Manual
recursion on the edge list (cleaner than `zipIdx + flatMap` because
the index offset shifts naturally with the recursion). -/
def subdivideAll : ExecHG ℕ → ℕ → ExecHG ℕ
  | [], _ => []
  | e :: rest, baseFresh => subdivideEdge e baseFresh ++ subdivideAll rest (baseFresh + 1)

@[simp] theorem subdivideAll_nil (b : ℕ) : subdivideAll [] b = [] := rfl

@[simp] theorem subdivideAll_cons (e : Hyperedge ℕ) (rest : ExecHG ℕ) (b : ℕ) :
    subdivideAll (e :: rest) b = subdivideEdge e b ++ subdivideAll rest (b + 1) := rfl

/-- **Math-side equality**: subdividing each edge of `pathEdges vs`
with consecutive midpoints starting at `b` yields `pathEdges` of the
interleaved vertex sequence. Pure list combinatorics — no engine
semantics involved. -/
theorem subdivideAll_pathEdges (vs : List ℕ) (h : 2 ≤ vs.length) (b : ℕ) :
    subdivideAll (pathEdges vs) b = pathEdges (subdivideVerts vs b) := by
  induction vs generalizing b with
  | nil => simp at h
  | cons v rest ih =>
    cases rest with
    | nil => simp at h
    | cons w rest' =>
      cases rest' with
      | nil =>
        -- Base: vs = [v, w]
        show subdivideAll [consEdge v w] b = pathEdges [v, b, w]
        rfl
      | cons x rest'' =>
        -- Step: vs = v :: w :: x :: rest''. Use IH on (w :: x :: rest'').
        rw [pathEdges_cons_cons, subdivideVerts_cons_cons,
            subdivideAll_cons]
        have h_inner : 2 ≤ (w :: x :: rest'').length := by simp
        rw [ih h_inner (b + 1)]
        rw [show subdivideVerts (w :: x :: rest'') (b+1)
              = w :: (b+1) :: subdivideVerts (x :: rest'') (b+2) from rfl]
        rw [subdivideEdge_consEdge]
        rw [pathEdges_cons_cons, pathEdges_cons_cons, pathEdges_cons_cons]
        rfl

/-! ## Remaining inductive step (Phase 2 of #232 — staged)

The *simulation lemma* `singleWayStep subdivisionSys H = subdivideAll H (nextFresh H)`
for path-shape `H` bridges the engine to Phase 1's math side. Three
sub-lemmas (S1 match-count, S2 match-order, S3 foldl invariant) per
`notes/232_subdivision_path_plan.md` §3.

In the meantime, `decide` certifies the full closed form
`singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)`
for small `n`, leveraging Phase 1's `subdivideAll_pathEdges` plus the
fact that both sides are concrete computable `ExecHG ℕ` lists. -/

/-- **Closed form, n=0**: `singleWayEvolve … 0 = pathEdges (subdVerts 0)`. -/
example : singleWayEvolve subdivisionSys subdSeed 0 = pathEdges (subdVerts 0) := by
  decide

/-- **Closed form, n=1**: `singleWayEvolve … 1 = pathEdges (subdVerts 1)`. -/
example : singleWayEvolve subdivisionSys subdSeed 1 = pathEdges (subdVerts 1) := by
  decide

/-- **Closed form, n=2**: `singleWayEvolve … 2 = pathEdges (subdVerts 2)`. -/
example : singleWayEvolve subdivisionSys subdSeed 2 = pathEdges (subdVerts 2) := by
  decide

/-- **Closed form, n=3**: `singleWayEvolve … 3 = pathEdges (subdVerts 3)`. -/
example : singleWayEvolve subdivisionSys subdSeed 3 = pathEdges (subdVerts 3) := by
  decide

/-- **Closed form, n=4**: `singleWayEvolve … 4 = pathEdges (subdVerts 4)`. -/
example : singleWayEvolve subdivisionSys subdSeed 4 = pathEdges (subdVerts 4) := by
  decide

end MultiwayExec
end InfraFormalization
