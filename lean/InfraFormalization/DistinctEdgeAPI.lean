/-
**API for `distinctEdgeCount`** (#492 supporting infrastructure).

Foundational lemmas about `distinctEdgeCount` independent of the
engine. These compose into the engine-correspondence bridge proof
(`engineMatchesTriad` in `H9Closure`).

**What's proved here**:

  * `distinctEdgeCount_nil`: empty hypergraph has zero distinct edges.
  * `distinctEdgeCount_singleton`: one edge has one distinct edge.
  * `distinctEdgeCount_le_length`: distinct count is at most edge count.
  * `distinctEdgeCount_cons_mem` / `_not_mem` / `_ge` / `_le`:
    cons behavior.
  * `distinctEdgeCount_append_le`: subadditivity under concatenation.

These lemmas are reusable for any work involving `distinctEdgeCount`
and are independent of any specific rule system or engine semantics.
-/

import InfraFormalization.DistinctEdgeIdentity

namespace InfraFormalization
namespace DistinctEdgeAPI

open MultiwayExec
open DistinctEdgeIdentity

/-! ## Section A: The dedup helper -/

/-- The foldr that builds the deduplicated verts list, factored out
for direct manipulation. -/
def dedupFoldr (xs : List (List ℕ)) : List (List ℕ) :=
  xs.foldr (fun v acc => if v ∈ acc then acc else v :: acc) []

theorem dedupFoldr_nil : dedupFoldr [] = [] := rfl

theorem dedupFoldr_cons (x : List ℕ) (xs : List (List ℕ)) :
    dedupFoldr (x :: xs) =
      (if x ∈ dedupFoldr xs then dedupFoldr xs else x :: dedupFoldr xs) := by
  rfl

/-- `distinctEdgeCount` equals the length of `dedupFoldr` applied to
the verts-projected edges. -/
theorem distinctEdgeCount_eq_dedupFoldr_length (H : ExecHG ℕ) :
    distinctEdgeCount H = (dedupFoldr (H.map (·.verts))).length := rfl

/-! ## Section B: Basic cases -/

theorem distinctEdgeCount_nil : distinctEdgeCount ([] : ExecHG ℕ) = 0 := rfl

theorem distinctEdgeCount_singleton (e : Hyperedge ℕ) :
    distinctEdgeCount [e] = 1 := rfl

/-! ## Section C: Length bound -/

theorem dedupFoldr_length_le (xs : List (List ℕ)) :
    (dedupFoldr xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [dedupFoldr_nil]
  | cons hd tl ih =>
    rw [dedupFoldr_cons]
    by_cases h : hd ∈ dedupFoldr tl
    · rw [if_pos h]
      have : tl.length ≤ (hd :: tl).length := by simp
      omega
    · rw [if_neg h]
      simp [List.length_cons]; omega

theorem distinctEdgeCount_le_length (H : ExecHG ℕ) :
    distinctEdgeCount H ≤ H.length := by
  rw [distinctEdgeCount_eq_dedupFoldr_length]
  have h1 : (dedupFoldr (H.map (·.verts))).length ≤ (H.map (·.verts)).length :=
    dedupFoldr_length_le _
  have h2 : (H.map (·.verts)).length = H.length := List.length_map ..
  omega

/-! ## Section D: Membership characterization -/

theorem mem_dedupFoldr {v : List ℕ} {xs : List (List ℕ)} :
    v ∈ dedupFoldr xs ↔ v ∈ xs := by
  induction xs with
  | nil => simp [dedupFoldr_nil]
  | cons hd tl ih =>
    rw [dedupFoldr_cons]
    by_cases h : hd ∈ dedupFoldr tl
    · rw [if_pos h, List.mem_cons]
      constructor
      · intro hmem
        right; exact ih.mp hmem
      · intro hor
        rcases hor with heq | hmem
        · rw [heq]; exact h
        · exact ih.mpr hmem
    · rw [if_neg h, List.mem_cons, List.mem_cons]
      constructor
      · intro hor
        rcases hor with heq | hmem
        · left; exact heq
        · right; exact ih.mp hmem
      · intro hor
        rcases hor with heq | hmem
        · left; exact heq
        · right; exact ih.mpr hmem

/-! ## Section E: Cons behavior -/

theorem distinctEdgeCount_cons_mem {e : Hyperedge ℕ} {H : ExecHG ℕ}
    (h : e.verts ∈ H.map (·.verts)) :
    distinctEdgeCount (e :: H) = distinctEdgeCount H := by
  rw [distinctEdgeCount_eq_dedupFoldr_length, distinctEdgeCount_eq_dedupFoldr_length]
  rw [List.map_cons, dedupFoldr_cons]
  have h' : e.verts ∈ dedupFoldr (H.map (·.verts)) := mem_dedupFoldr.mpr h
  rw [if_pos h']

theorem distinctEdgeCount_cons_not_mem {e : Hyperedge ℕ} {H : ExecHG ℕ}
    (h : e.verts ∉ H.map (·.verts)) :
    distinctEdgeCount (e :: H) = distinctEdgeCount H + 1 := by
  rw [distinctEdgeCount_eq_dedupFoldr_length, distinctEdgeCount_eq_dedupFoldr_length]
  rw [List.map_cons, dedupFoldr_cons]
  have h' : e.verts ∉ dedupFoldr (H.map (·.verts)) := by
    intro hmem; exact h (mem_dedupFoldr.mp hmem)
  rw [if_neg h']
  simp [List.length_cons]

/-! ## Section F: Cons monotonicity -/

theorem distinctEdgeCount_cons_ge (e : Hyperedge ℕ) (H : ExecHG ℕ) :
    distinctEdgeCount H ≤ distinctEdgeCount (e :: H) := by
  by_cases h : e.verts ∈ H.map (·.verts)
  · rw [distinctEdgeCount_cons_mem h]
  · rw [distinctEdgeCount_cons_not_mem h]; omega

theorem distinctEdgeCount_cons_le (e : Hyperedge ℕ) (H : ExecHG ℕ) :
    distinctEdgeCount (e :: H) ≤ distinctEdgeCount H + 1 := by
  by_cases h : e.verts ∈ H.map (·.verts)
  · rw [distinctEdgeCount_cons_mem h]; omega
  · rw [distinctEdgeCount_cons_not_mem h]

/-! ## Section G: Concatenation subadditivity -/

theorem distinctEdgeCount_append_le (H₁ H₂ : ExecHG ℕ) :
    distinctEdgeCount (H₁ ++ H₂) ≤ distinctEdgeCount H₁ + distinctEdgeCount H₂ := by
  induction H₁ with
  | nil => simp [distinctEdgeCount_nil]
  | cons e H ih =>
    -- distinctEdgeCount ((e :: H) ++ H₂) = distinctEdgeCount (e :: (H ++ H₂))
    have h_assoc : (e :: H) ++ H₂ = e :: (H ++ H₂) := rfl
    rw [h_assoc]
    by_cases h_e_in_HH2 : e.verts ∈ (H ++ H₂).map (·.verts)
    · -- e.verts is in H ++ H₂, so cons doesn't grow that side
      rw [distinctEdgeCount_cons_mem h_e_in_HH2]
      -- distinctEdgeCount (H ++ H₂) ≤ distinctEdgeCount H + distinctEdgeCount H₂ (by IH)
      -- distinctEdgeCount (e :: H) ≥ distinctEdgeCount H (monotonic)
      have h_mono : distinctEdgeCount H ≤ distinctEdgeCount (e :: H) :=
        distinctEdgeCount_cons_ge e H
      calc distinctEdgeCount (H ++ H₂)
          ≤ distinctEdgeCount H + distinctEdgeCount H₂ := ih
        _ ≤ distinctEdgeCount (e :: H) + distinctEdgeCount H₂ := by omega
    · -- e.verts not in H ++ H₂, so cons grows by 1
      rw [distinctEdgeCount_cons_not_mem h_e_in_HH2]
      -- Note: e.verts ∉ H ++ H₂ implies e.verts ∉ H
      have h_e_not_in_H : e.verts ∉ H.map (·.verts) := by
        intro hmem
        apply h_e_in_HH2
        simp [List.map_append, List.mem_append, hmem]
      rw [distinctEdgeCount_cons_not_mem h_e_not_in_H]
      have h_ih := ih
      omega

/-! ## What this delivers

A clean, reusable API for `distinctEdgeCount`:

  * Base values (`_nil`, `_singleton`).
  * Length bound (`_le_length`).
  * Cons behavior (`_cons_mem`, `_cons_not_mem`, `_cons_ge`, `_cons_le`).
  * Concatenation subadditivity (`_append_le`).

These are the foundational lemmas the engine-correspondence bridge
proof (`engineMatchesTriad` in `H9Closure.lean`) will compose to
prove the H9 distinct-edge tripling symbolically.

**Next step toward H9 closure**: with this API, the bridge proof
becomes a matter of characterizing `singleWayStep`'s edge-set behavior:
showing that for our persistent-class systems, the step adds exactly
3× new distinct edges and consumes exactly the input distinct edges.
-/

end DistinctEdgeAPI
end InfraFormalization
