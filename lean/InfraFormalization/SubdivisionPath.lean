/-
The subdivision rule and path-shaped states.

This module defines the rule `{a, b} → {a, c}, {c, b}` (`c` fresh), the
edge list `pathEdges vs` of a vertex sequence, the predicate `IsPathOf`,
the vertex sequences `subdVerts n` (with `2^n + 1` distinct entries), and
`subdivideAll`, which subdivides every edge of a list. It proves
`subdivideAll (pathEdges vs) b = pathEdges (subdivideVerts vs b)`. The
equality `singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)`
is checked by `decide` for n ≤ 4 and by `native_decide` for n = 3, 4, 5;
it is not proved for every n. One step on `[consEdge a b]` is checked by
`native_decide` for all `a, b < 12`.
-/

import InfraFormalization.MultiwayExec
import Mathlib.Data.Finset.Card

namespace InfraFormalization
namespace MultiwayExec

open Hypergraph

/-! ## Path-state predicate -/

/-- The hyperedge `[a, b]`. -/
@[simp] def consEdge (a b : ℕ) : Hyperedge ℕ :=
  ⟨[a, b], List.cons_ne_nil a [b]⟩

/-- The edges `[vs[i], vs[i+1]]` of the vertex sequence `vs`. -/
def pathEdges (vs : List ℕ) : ExecHG ℕ :=
  vs.zipWith consEdge vs.tail

/-- `vs` has at least 2 entries, no duplicates, and `H = pathEdges vs`. -/
def IsPathOf (H : ExecHG ℕ) (vs : List ℕ) : Prop :=
  2 ≤ vs.length ∧ vs.Nodup ∧ H = pathEdges vs

/-! ## Subdivision rule -/

private def sLhs : Hyperedge (Fin 2) := ⟨[0, 1], List.cons_ne_nil _ _⟩
private def sRhsL : Hyperedge (Fin 3) := ⟨[0, 2], List.cons_ne_nil _ _⟩
private def sRhsR : Hyperedge (Fin 3) := ⟨[2, 1], List.cons_ne_nil _ _⟩

/-- The rule `{a, b} → {a, c}, {c, b}` with `c` fresh. -/
def subdivisionRule : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [sLhs]
  rhs := [sRhsL, sRhsR]

def subdivisionSys : ExecSystem := ⟨[subdivisionRule]⟩

/-- The seed `[{1, 2}]`. -/
def subdSeed : ExecHG ℕ := [consEdge 1 2]

/-! ## The seed is a path -/

theorem subdSeed_isPathOf : IsPathOf subdSeed [1, 2] := by
  refine ⟨by decide, by decide, ?_⟩
  rfl

/-! ## Interleaved vertex sequences

`subdivideVerts vs b` inserts `b + i` between `vs[i]` and `vs[i+1]`. -/

/-- Insert `baseFresh + i` between positions `i` and `i+1` of `vs`. -/
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

/-- For `vs.length ≥ 1`, `subdivideVerts vs b` has `2 · vs.length − 1`
entries. -/
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

/-! ## The vertex sequences `subdVerts n`

`subdVerts 0 = [1, 2]`, and `subdVerts (n+1)` interleaves `subdVerts n`
with midpoints starting at `listMax (subdVerts n) + 1`. -/

/-- The maximum entry of a list of ℕ, or 0 for the empty list. -/
def listMax (vs : List ℕ) : ℕ := vs.foldr Nat.max 0

@[simp] theorem listMax_nil : listMax [] = 0 := rfl

@[simp] theorem listMax_cons (v : ℕ) (vs : List ℕ) :
    listMax (v :: vs) = Nat.max v (listMax vs) := rfl

/-- `subdVerts 0 = [1, 2]` and
`subdVerts (n+1) = subdivideVerts (subdVerts n) (listMax (subdVerts n) + 1)`. -/
def subdVerts : ℕ → List ℕ
  | 0 => [1, 2]
  | n+1 =>
    let vs := subdVerts n
    subdivideVerts vs (listMax vs + 1)

@[simp] theorem subdVerts_zero : subdVerts 0 = [1, 2] := rfl

theorem subdVerts_succ (n : ℕ) :
    subdVerts (n+1) = subdivideVerts (subdVerts n) (listMax (subdVerts n) + 1) :=
  rfl

/-! ## `listMax` -/

/-- Every entry of `vs` is at most `listMax vs`. -/
theorem mem_le_listMax (vs : List ℕ) {x : ℕ} (hx : x ∈ vs) : x ≤ listMax vs := by
  induction vs with
  | nil => simp at hx
  | cons v rest ih =>
    rcases List.mem_cons.mp hx with hxv | hx_rest
    · subst hxv
      exact Nat.le_max_left x (listMax rest)
    · exact (ih hx_rest).trans (Nat.le_max_right v (listMax rest))

/-- `listMax rest ≤ listMax (v :: rest)`. -/
theorem listMax_le_cons (v : ℕ) (rest : List ℕ) :
    listMax rest ≤ listMax (v :: rest) := Nat.le_max_right v (listMax rest)

/-! ## Membership and absence of duplicates for `subdivideVerts` -/

/-- Every entry of `subdivideVerts vs b` is an entry of `vs` or is at
least `b`. -/
theorem mem_subdivideVerts_imp : ∀ (vs : List ℕ) (b : ℕ) {x : ℕ},
    x ∈ subdivideVerts vs b → x ∈ vs ∨ b ≤ x
  | [], b, x, hx => by simp [subdivideVerts] at hx
  | [v], b, x, hx => by
      rw [subdivideVerts_singleton] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact Or.inl List.mem_cons_self
  | v :: w :: rest', b, x, hx => by
      rw [subdivideVerts_cons_cons] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx_rest
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (Nat.le_refl _)
      · rcases mem_subdivideVerts_imp (w :: rest') (b + 1) hx_rest with hin_rest | hb1
        · exact Or.inl (List.mem_cons_of_mem _ hin_rest)
        · exact Or.inr (by omega)

/-- If `vs` has no duplicates and `listMax vs < b`, then
`subdivideVerts vs b` has no duplicates. -/
theorem subdivideVerts_nodup : ∀ (vs : List ℕ) (b : ℕ),
    vs.Nodup → listMax vs < b → (subdivideVerts vs b).Nodup
  | [], b, _, _ => by simp [subdivideVerts]
  | [v], b, _, _ => by simp [subdivideVerts]
  | v :: w :: rest', b, h_nodup, h_fresh => by
      rw [subdivideVerts_cons_cons]
      have h_v_le : v ≤ listMax (v :: w :: rest') :=
        mem_le_listMax _ List.mem_cons_self
      have h_inner_max : listMax (w :: rest') ≤ listMax (v :: w :: rest') :=
        listMax_le_cons _ _
      have h_listmax_inner : listMax (w :: rest') < b + 1 := by omega
      have h_nodup_tail : (w :: rest').Nodup := h_nodup.of_cons
      have ih' := subdivideVerts_nodup (w :: rest') (b + 1) h_nodup_tail h_listmax_inner
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hv
        rcases List.mem_cons.mp hv with hvb | hin
        · omega
        · rcases mem_subdivideVerts_imp _ _ hin with hv_in_rest | hv_ge
          · exact (List.nodup_cons.mp h_nodup).1 hv_in_rest
          · omega
      · refine List.nodup_cons.mpr ⟨?_, ih'⟩
        intro hb_in
        rcases mem_subdivideVerts_imp _ _ hb_in with hb_rest | hb_ge
        · have h_b_le : b ≤ listMax (w :: rest') := mem_le_listMax _ hb_rest
          omega
        · omega

/-! ## Length and absence of duplicates for `subdVerts n` -/

/-- `subdVerts n` has at least 2 entries. -/
theorem subdVerts_length_ge_two (n : ℕ) : 2 ≤ (subdVerts n).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [subdVerts_succ, subdivideVerts_length _ (by omega)]
    omega

/-- `subdVerts n` has no duplicates. -/
theorem subdVerts_nodup (n : ℕ) : (subdVerts n).Nodup := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [subdVerts_succ]
    exact subdivideVerts_nodup _ _ ih (by omega)

/-! ## `listMax` and membership -/

/-- `listMax vs ≤ M ↔ ∀ x ∈ vs, x ≤ M`. -/
theorem listMax_le_iff (vs : List ℕ) (M : ℕ) :
    listMax vs ≤ M ↔ ∀ x ∈ vs, x ≤ M := by
  induction vs with
  | nil => simp [listMax]
  | cons v rest ih =>
    simp only [listMax_cons, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

/-- Two lists with the same members have the same `listMax`. -/
theorem listMax_eq_of_mem_iff (l₁ l₂ : List ℕ) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    listMax l₁ = listMax l₂ := by
  apply Nat.le_antisymm
  · rw [listMax_le_iff]; intro x hx
    exact mem_le_listMax l₂ ((h x).mp hx)
  · rw [listMax_le_iff]; intro x hx
    exact mem_le_listMax l₁ ((h x).mpr hx)

/-- `subdVerts n` has `2^n + 1` entries. -/
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

/-- Unfolding of `pathEdges` on short lists. -/
@[simp] theorem pathEdges_nil : pathEdges ([] : List ℕ) = [] := rfl

@[simp] theorem pathEdges_singleton (v : ℕ) : pathEdges [v] = [] := rfl

@[simp] theorem pathEdges_cons_cons (v w : ℕ) (rest : List ℕ) :
    pathEdges (v :: w :: rest) = consEdge v w :: pathEdges (w :: rest) := by
  unfold pathEdges
  rfl

/-- `(pathEdges (v :: w :: rest)).flatMap verts
= v :: w :: (pathEdges (w :: rest)).flatMap verts`. -/
theorem pathEdges_flatMap_verts_cons_cons (v w : ℕ) (rest : List ℕ) :
    (pathEdges (v :: w :: rest)).flatMap (·.verts)
      = v :: w :: (pathEdges (w :: rest)).flatMap (·.verts) := by
  rw [pathEdges_cons_cons]
  simp [List.flatMap_cons, consEdge]

@[simp] theorem pathEdges_flatMap_verts_singleton_pair (v w : ℕ) :
    (pathEdges [v, w]).flatMap (·.verts) = [v, w] := by
  simp [pathEdges, consEdge]

/-- For `vs` with at least 2 entries, `x` occurs in a hyperedge of
`pathEdges vs` if and only if `x ∈ vs`. -/
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

/-- For `vs` with at least 2 entries,
`nextFresh (pathEdges vs) = listMax vs + 1`. -/
theorem nextFresh_pathEdges (vs : List ℕ) (h : 2 ≤ vs.length) :
    nextFresh (pathEdges vs) = listMax vs + 1 := by
  show (vertexList (pathEdges vs)).foldr Nat.max 0 + 1 = listMax vs + 1
  congr 1
  apply listMax_eq_of_mem_iff
  intro x
  show x ∈ ((pathEdges vs).flatMap (·.verts)).dedup ↔ x ∈ vs
  rw [List.mem_dedup]
  exact mem_pathEdges_flatMap vs h x

/-! ## Counts -/

/-- If `vs` has at least 2 entries and no duplicates, `vertexList
(pathEdges vs)` has `vs.length` entries. -/
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

/-- `pathEdges (subdVerts n)` has `2^n` edges. -/
@[simp] theorem subdVerts_pathEdges_length (n : ℕ) :
    (pathEdges (subdVerts n)).length = 2^n := by
  rw [pathEdges_length, subdVerts_length]
  have : 1 ≤ 2^n := Nat.one_le_two_pow
  omega

/-- `singleWayEvolve subdivisionSys subdSeed 0 = pathEdges (subdVerts 0)`,
by `rfl`. -/
theorem singleWayEvolve_subdivision_zero :
    singleWayEvolve subdivisionSys subdSeed 0 = pathEdges (subdVerts 0) := by
  rfl

/-! ## Subdividing every edge of a path

`subdivideAll` subdivides each edge of a list independently, without
`allMatches`. -/

/-- Replace a hyperedge `[a, b]` by `[a, c], [c, b]`; other hyperedges are
returned unchanged. -/
def subdivideEdge (e : Hyperedge ℕ) (c : ℕ) : ExecHG ℕ :=
  match e.verts with
  | [a, b] => [consEdge a c, consEdge c b]
  | _ => [e]

@[simp] theorem subdivideEdge_consEdge (a b c : ℕ) :
    subdivideEdge (consEdge a b) c = [consEdge a c, consEdge c b] := by
  unfold subdivideEdge consEdge; simp

/-- Replace the i-th edge `[a, b]` by `[a, baseFresh + i], [baseFresh + i, b]`. -/
def subdivideAll : ExecHG ℕ → ℕ → ExecHG ℕ
  | [], _ => []
  | e :: rest, baseFresh => subdivideEdge e baseFresh ++ subdivideAll rest (baseFresh + 1)

@[simp] theorem subdivideAll_nil (b : ℕ) : subdivideAll [] b = [] := rfl

@[simp] theorem subdivideAll_cons (e : Hyperedge ℕ) (rest : ExecHG ℕ) (b : ℕ) :
    subdivideAll (e :: rest) b = subdivideEdge e b ++ subdivideAll rest (b + 1) := rfl

/-- For `vs` with at least 2 entries,
`subdivideAll (pathEdges vs) b = pathEdges (subdivideVerts vs b)`. -/
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

/-! ## The engine run for small n

The equality `singleWayStep subdivisionSys H = subdivideAll H (nextFresh H)`
for paths `H` is not proved. The closed form
`singleWayEvolve subdivisionSys subdSeed n = pathEdges (subdVerts n)` is
checked below for n ≤ 5. -/

/-- n = 0, by `decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 0 = pathEdges (subdVerts 0) := by
  decide

/-- n = 1, by `decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 1 = pathEdges (subdVerts 1) := by
  decide

/-- n = 2, by `decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 2 = pathEdges (subdVerts 2) := by
  decide

/-- n = 3, by `native_decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 3 = pathEdges (subdVerts 3) := by
  native_decide

/-- n = 4, by `native_decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 4 = pathEdges (subdVerts 4) := by
  native_decide

/-- n = 5, by `native_decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 5 = pathEdges (subdVerts 5) := by
  native_decide

/-! ## One edge -/

/-- For `a ≠ b`, `vertexList [consEdge a b] = [a, b]`. -/
theorem vertexList_consEdge_of_ne (a b : ℕ) (h : a ≠ b) :
    vertexList [consEdge a b] = [a, b] := by
  unfold vertexList
  simp [consEdge]
  exact List.Nodup.dedup (by simp [h])

/-- For `a ≠ b`, `nextFresh [consEdge a b] = max a b + 1`. -/
theorem nextFresh_consEdge_of_ne (a b : ℕ) (h : a ≠ b) :
    nextFresh [consEdge a b] = max a b + 1 := by
  unfold nextFresh
  rw [vertexList_consEdge_of_ne a b h]
  show List.foldr Nat.max 0 [a, b] + 1 = max a b + 1
  simp

/-- `subdivideAll [consEdge a b] c = [consEdge a c, consEdge c b]`. -/
theorem subdivideAll_singleton (a b c : ℕ) :
    subdivideAll [consEdge a b] c = [consEdge a c, consEdge c b] := by
  show subdivideEdge (consEdge a b) c ++ subdivideAll [] (c + 1)
       = [consEdge a c, consEdge c b]
  rw [subdivideEdge_consEdge, subdivideAll_nil]
  simp

/-- For `a ≠ b`, `subdivideAll [consEdge a b] (nextFresh [consEdge a b])
= [consEdge a (max a b + 1), consEdge (max a b + 1) b]`. -/
theorem subdivideAll_consEdge_nextFresh_of_ne (a b : ℕ) (h : a ≠ b) :
    subdivideAll [consEdge a b] (nextFresh [consEdge a b])
      = [consEdge a (max a b + 1), consEdge (max a b + 1) b] := by
  rw [nextFresh_consEdge_of_ne a b h, subdivideAll_singleton]

/-! ## One engine step on one edge, for fixed endpoints

The statement for all `a ≠ b` is `singleWayStep_subdivisionSys_consEdge_of_ne`
in `SubdivisionAbstract.lean`. The examples below are checked by
`decide`. -/

/-- `(a, b) = (1, 2)`. -/
example :
    singleWayStep subdivisionSys [consEdge 1 2]
      = [consEdge 1 (max 1 2 + 1), consEdge (max 1 2 + 1) 2] := by
  decide

/-- `(a, b) = (3, 7)`. -/
example :
    singleWayStep subdivisionSys [consEdge 3 7]
      = [consEdge 3 (max 3 7 + 1), consEdge (max 3 7 + 1) 7] := by
  decide

/-- `(a, b) = (5, 2)`. -/
example :
    singleWayStep subdivisionSys [consEdge 5 2]
      = [consEdge 5 (max 5 2 + 1), consEdge (max 5 2 + 1) 2] := by
  decide

/-- `(a, b) = (10, 20)`. -/
example :
    singleWayStep subdivisionSys [consEdge 10 20]
      = [consEdge 10 (max 10 20 + 1), consEdge (max 10 20 + 1) 20] := by
  decide

/-- `(a, b) = (0, 1)`. -/
example :
    singleWayStep subdivisionSys [consEdge 0 1]
      = [consEdge 0 (max 0 1 + 1), consEdge (max 0 1 + 1) 1] := by
  decide

/-- `(a, b) = (1, 5)`. -/
example :
    singleWayStep subdivisionSys [consEdge 1 5]
      = [consEdge 1 (max 1 5 + 1), consEdge (max 1 5 + 1) 5] := by
  decide

/-- `(a, b) = (1, 2)` and `(a, b) = (100, 200)`. -/
example :
    (singleWayStep subdivisionSys [consEdge 1 2]
      = [consEdge 1 (max 1 2 + 1), consEdge (max 1 2 + 1) 2])
    ∧
    (singleWayStep subdivisionSys [consEdge 100 200]
      = [consEdge 100 (max 100 200 + 1), consEdge (max 100 200 + 1) 200]) := by
  decide

/-! ### All pairs below a bound, checked by `native_decide`

These statements include the case `a = b`. -/

/-- The one-step equation holds for all `a, b < 8`, including `a = b`. -/
theorem singleWayStep_subdivisionSys_consEdge_fin8 :
    ∀ a b : Fin 8,
      singleWayStep subdivisionSys [consEdge a.val b.val]
        = [consEdge a.val (max a.val b.val + 1),
           consEdge (max a.val b.val + 1) b.val] := by
  native_decide

/-- The one-step equation holds for all `a, b < 12`. -/
theorem singleWayStep_subdivisionSys_consEdge_fin12 :
    ∀ a b : Fin 12,
      singleWayStep subdivisionSys [consEdge a.val b.val]
        = [consEdge a.val (max a.val b.val + 1),
           consEdge (max a.val b.val + 1) b.val] := by
  native_decide

/-- The one-step equation for `(137, 891)`, `(891, 137)` and `(500, 500)`. -/
theorem singleWayStep_subdivisionSys_consEdge_high :
    (singleWayStep subdivisionSys [consEdge 137 891]
      = [consEdge 137 (max 137 891 + 1),
         consEdge (max 137 891 + 1) 891])
  ∧ (singleWayStep subdivisionSys [consEdge 891 137]
      = [consEdge 891 (max 891 137 + 1),
         consEdge (max 891 137 + 1) 137])
  ∧ (singleWayStep subdivisionSys [consEdge 500 500]
      = [consEdge 500 (max 500 500 + 1),
         consEdge (max 500 500 + 1) 500]) := by
  native_decide

/-- n = 3, by `decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 3 = pathEdges (subdVerts 3) := by
  decide

/-- n = 4, by `decide`. -/
example : singleWayEvolve subdivisionSys subdSeed 4 = pathEdges (subdVerts 4) := by
  decide

/-! ## The sequence `pathEdges (subdVerts n)`

`subdivisionTrajectory n` is defined as `pathEdges (subdVerts n)`, not from
engine runs. It agrees with `singleWayEvolve subdivisionSys subdSeed n` for
the values of n checked above. -/

/-- `pathEdges (subdVerts n)`. -/
@[reducible] def subdivisionTrajectory (n : ℕ) : ExecHG ℕ :=
  pathEdges (subdVerts n)

/-- `subdivisionTrajectory n` has `2^n` edges. -/
@[simp] theorem subdivisionTrajectory_length (n : ℕ) :
    (subdivisionTrajectory n).length = 2^n :=
  subdVerts_pathEdges_length n

/-- `subdivisionTrajectory n` is the path with vertex sequence
`subdVerts n`. -/
theorem subdivisionTrajectory_isPathOf (n : ℕ) :
    IsPathOf (subdivisionTrajectory n) (subdVerts n) := by
  refine ⟨?_, subdVerts_nodup n, rfl⟩
  rw [subdVerts_length]
  have : 1 ≤ 2^n := Nat.one_le_two_pow
  omega

/-- `subdivisionTrajectory (n + 1)` is `subdivideAll` of
`subdivisionTrajectory n` with midpoints starting at
`listMax (subdVerts n) + 1`. -/
theorem subdivisionTrajectory_succ (n : ℕ) :
    subdivisionTrajectory (n + 1) =
      subdivideAll (subdivisionTrajectory n) (listMax (subdVerts n) + 1) := by
  unfold subdivisionTrajectory
  rw [subdVerts_succ]
  rw [subdivideAll_pathEdges _ (subdVerts_length_ge_two n)]

/-- `subdivisionTrajectory 0 = singleWayEvolve subdivisionSys subdSeed 0`,
by `rfl`. -/
theorem subdivisionTrajectory_eq_engine_at_zero :
    subdivisionTrajectory 0 = singleWayEvolve subdivisionSys subdSeed 0 := by
  rfl

end MultiwayExec
end InfraFormalization
