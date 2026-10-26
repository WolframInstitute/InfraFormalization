/-
One single-way step of the subdivision rule on one edge, for all
distinct endpoints.

This module defines the binding `matchAB a b` of the left-hand side to
`[consEdge a b]` and its extension `matchABext a b`, which sends the fresh
vertex to `max a b + 1`. It proves that for `a ≠ b`,
`allMatches subdivisionRule [consEdge a b] = [matchAB a b]`, and from this
`singleWayStep_subdivisionSys_consEdge_of_ne`:
`singleWayStep subdivisionSys [consEdge a b]
= [consEdge a (max a b + 1), consEdge (max a b + 1) b]`. The proofs use
neither `decide` nor `native_decide`.
-/

import InfraFormalization.SubdivisionPath

namespace InfraFormalization
namespace MultiwayExec

open Hypergraph

/-- The left-hand and right-hand hyperedges of `subdivisionRule`, which
are `private` in `SubdivisionPath`. -/
def subdLhs : Hyperedge (Fin 2) := ⟨[0, 1], List.cons_ne_nil _ _⟩
def subdRhsL : Hyperedge (Fin 3) := ⟨[0, 2], List.cons_ne_nil _ _⟩
def subdRhsR : Hyperedge (Fin 3) := ⟨[2, 1], List.cons_ne_nil _ _⟩

/-- `subdivisionRule.lhs = [subdLhs]`. -/
theorem subdivisionRule_lhs_eq : subdivisionRule.lhs = [subdLhs] := rfl

/-- `subdivisionRule.rhs = [subdRhsL, subdRhsR]`. -/
theorem subdivisionRule_rhs_eq : subdivisionRule.rhs = [subdRhsL, subdRhsR] := rfl

/-- The binding `0 ↦ a`, `1 ↦ b`. -/
def matchAB (a b : ℕ) : Fin 2 → ℕ :=
  fun i => if i.val = 0 then a else b

@[simp] theorem matchAB_zero (a b : ℕ) : matchAB a b ⟨0, by decide⟩ = a := rfl
@[simp] theorem matchAB_one (a b : ℕ) : matchAB a b ⟨1, by decide⟩ = b := rfl

/-- The binding `0 ↦ a`, `1 ↦ b`, `2 ↦ max a b + 1`. -/
def matchABext (a b : ℕ) : Fin 3 → ℕ :=
  fun i =>
    if h : i.val < 2 then matchAB a b ⟨i.val, h⟩
    else max a b + 1

@[simp] theorem matchABext_zero (a b : ℕ) : matchABext a b ⟨0, by decide⟩ = a := rfl
@[simp] theorem matchABext_one (a b : ℕ) : matchABext a b ⟨1, by decide⟩ = b := rfl
@[simp] theorem matchABext_two (a b : ℕ) :
    matchABext a b ⟨2, by decide⟩ = max a b + 1 := rfl

/-! ## Images of the two sides, by `rfl` -/

/-- `mapPattern (matchAB a b) subdivisionRule.lhs = [consEdge a b]`. -/
theorem mapPattern_matchAB_lhs (a b : ℕ) :
    mapPattern (matchAB a b) subdivisionRule.lhs = [consEdge a b] := by
  rfl

/-- `mapPattern (matchABext a b) subdivisionRule.rhs =
    [consEdge a (max a b + 1), consEdge (max a b + 1) b]`. -/
theorem mapPattern_matchABext_rhs (a b : ℕ) :
    mapPattern (matchABext a b) subdivisionRule.rhs
      = [consEdge a (max a b + 1), consEdge (max a b + 1) b] := by
  rfl

/-! ## Bindings whose image is `consEdge a b` -/

/-- If `Hyperedge.map ρ subdLhs = consEdge a b`, then `ρ 0 = a` and
`ρ 1 = b`. -/
theorem matchAB_pointwise_of_image_eq {ρ : Fin 2 → ℕ} {a b : ℕ}
    (h : Hyperedge.map ρ subdLhs = consEdge a b) :
    ρ ⟨0, by decide⟩ = a ∧ ρ ⟨1, by decide⟩ = b := by
  have hverts : [ρ ⟨0, by decide⟩, ρ ⟨1, by decide⟩] = [a, b] := by
    have := congrArg Hyperedge.verts h
    simpa [subdLhs, consEdge, Hyperedge.map] using this
  have h0 := (List.cons.inj hverts).1
  have htail := (List.cons.inj hverts).2
  have h1 := (List.cons.inj htail).1
  exact ⟨h0, h1⟩

/-- Two functions `Fin 2 → ℕ` that agree at 0 and 1 are equal. -/
theorem fin2_funext {ρ σ : Fin 2 → ℕ}
    (h0 : ρ ⟨0, by decide⟩ = σ ⟨0, by decide⟩)
    (h1 : ρ ⟨1, by decide⟩ = σ ⟨1, by decide⟩) : ρ = σ := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

/-- If `Hyperedge.map ρ subdLhs = consEdge a b`, then `ρ = matchAB a b`. -/
theorem match_eq_matchAB_of_image_eq {ρ : Fin 2 → ℕ} {a b : ℕ}
    (h : Hyperedge.map ρ subdLhs = consEdge a b) :
    ρ = matchAB a b := by
  obtain ⟨h0, h1⟩ := matchAB_pointwise_of_image_eq h
  apply fin2_funext
  · simpa using h0
  · simpa using h1

/-! ## Lemmas on the parts of `singleWayStep`

`singleWayStep` folds over the rules and, for each rule, over its matches.
`subdivisionSys` has one rule. -/

/-- `subdivisionSys.rules = [subdivisionRule]`. -/
theorem subdivisionSys_rules : subdivisionSys.rules = [subdivisionRule] := rfl

/-- `removeEdges [consEdge a b] [consEdge a b] = []`. -/
theorem removeEdges_consEdge_self (a b : ℕ) :
    removeEdges [consEdge a b] [consEdge a b] = [] := by
  simp [removeEdges]

/-- The extended binding built inside `singleWayStep`, with fresh base
`max a b + 1` and offset 0, equals `matchABext a b`. -/
theorem singleWayStep_inner_extension_eq (a b : ℕ) :
    (fun i : Fin (subdivisionRule.numBound + subdivisionRule.numFresh) =>
        if h : i.val < subdivisionRule.numBound then
          matchAB a b ⟨i.val, h⟩
        else
          (max a b + 1) + 0 + (i.val - subdivisionRule.numBound))
      = matchABext a b := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ =>
    show (max a b + 1) + 0 + (2 - 2) = matchABext a b ⟨2, by decide⟩
    rw [matchABext_two]

/-! ## The candidate list `allFunctions 2 [a, b]` -/

/-- Mapping `ρ ↦ (ρ 0, ρ 1)` over `allFunctions 2 [a, b]` gives
`[(a, a), (a, b), (b, a), (b, b)]`. -/
theorem allFunctions_2_pair_projection (a b : ℕ) :
    ((allFunctions 2 [a, b]).map (fun ρ => (ρ ⟨0, by decide⟩, ρ ⟨1, by decide⟩)))
      = [(a, a), (a, b), (b, a), (b, b)] := by
  simp [allFunctions, List.flatMap]

/-- `allFunctions 2 [a, b]` has exactly 4 elements. -/
theorem allFunctions_2_length (a b : ℕ) :
    (allFunctions 2 [a, b]).length = 4 := by
  simp [allFunctions, List.flatMap]

/-! ## `bindingMatches` on one edge -/

/-- `Hyperedge.map ρ subdLhs = consEdge (ρ 0) (ρ 1)`. -/
theorem mapPattern_subdLhs_eq (ρ : Fin 2 → ℕ) :
    Hyperedge.map ρ subdLhs = consEdge (ρ ⟨0, by decide⟩) (ρ ⟨1, by decide⟩) :=
  rfl

/-- `consEdge` is injective in both arguments. -/
theorem consEdge_eq_iff (x y a b : ℕ) :
    consEdge x y = consEdge a b ↔ x = a ∧ y = b := by
  constructor
  · intro h
    have := congrArg Hyperedge.verts h
    simp [consEdge] at this
    exact this
  · rintro ⟨rfl, rfl⟩; rfl

/-- `bindingMatches subdivisionRule.lhs [consEdge a b] ρ = true` iff
`Hyperedge.map ρ subdLhs = consEdge a b`. -/
theorem bindingMatches_subdLhs_iff (ρ : Fin 2 → ℕ) (a b : ℕ) :
    bindingMatches subdivisionRule.lhs [consEdge a b] ρ = true
    ↔ Hyperedge.map ρ subdLhs = consEdge a b := by
  -- bindingMatches := edgesContained (mapPattern ρ r.lhs) H
  -- = edgesContained [Hyperedge.map ρ subdLhs] [consEdge a b]
  -- = ([Hyperedge.map ρ subdLhs].dedup).all
  --     (fun e => decide (edgeCount e [Hyperedge.map ρ subdLhs] ≤ edgeCount e [consEdge a b]))
  -- = decide (1 ≤ count (Hyperedge.map ρ subdLhs) [consEdge a b])
  -- = (Hyperedge.map ρ subdLhs = consEdge a b)
  show edgesContained [Hyperedge.map ρ subdLhs] [consEdge a b] = true
       ↔ Hyperedge.map ρ subdLhs = consEdge a b
  unfold edgesContained
  have hdedup : ([Hyperedge.map ρ subdLhs]).dedup = [Hyperedge.map ρ subdLhs] := by simp
  rw [hdedup]
  simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq,
             edgeCount, List.count_singleton]
  by_cases heq : Hyperedge.map ρ subdLhs = consEdge a b
  · constructor
    · intro _; exact heq
    · intro _
      rw [heq]
  · constructor
    · intro h
      exfalso
      have hself : (Hyperedge.map ρ subdLhs == Hyperedge.map ρ subdLhs) = true :=
        beq_self_eq_true _
      have hother : (consEdge a b == Hyperedge.map ρ subdLhs) = false := by
        rw [beq_eq_false_iff_ne]
        intro h'; exact heq h'.symm
      rw [hself, hother] at h
      simp at h
    · intro h; exact absurd h heq

/-! ## `allMatches` on one edge

The equality `allMatches subdivisionRule [consEdge a b] = [matchAB a b]`
for `a ≠ b` follows from membership of `matchAB a b`, equality of every
member with `matchAB a b`, and absence of duplicates. -/

/-- `matchAB a b ∈ allFunctions 2 [a, b]` for all `a`, `b`. -/
theorem matchAB_mem_allFunctions (a b : ℕ) :
    matchAB a b ∈ allFunctions 2 [a, b] := by
  -- The 4 candidates' (ρ 0, ρ 1) values are [(a,a), (a,b), (b,a), (b,b)].
  -- matchAB a b has projection (a, b), which is one of them.
  -- Pull this back via `map_mem` from pair-projection.
  have hpair := allFunctions_2_pair_projection a b
  -- (a, b) is in the projected list
  have : (a, b) ∈ ((allFunctions 2 [a, b]).map
      (fun ρ => (ρ ⟨0, by decide⟩, ρ ⟨1, by decide⟩))) := by
    rw [hpair]; simp
  -- Pull back through `map_mem`: there's some ρ in `allFunctions 2 [a, b]`
  -- whose pair projection is (a, b). That ρ equals matchAB a b.
  obtain ⟨ρ, hρ_mem, hρ_proj⟩ := List.mem_map.mp this
  have hρ_eq : ρ = matchAB a b := by
    apply fin2_funext
    · have := congrArg Prod.fst hρ_proj
      simpa using this
    · have := congrArg Prod.snd hρ_proj
      simpa using this
  rw [← hρ_eq]; exact hρ_mem

/-- `bindingMatches subdivisionRule.lhs [consEdge a b] (matchAB a b)`. The
hypothesis `a ≠ b` is not used. -/
theorem matchAB_bindingMatches (a b : ℕ) (_hab : a ≠ b) :
    bindingMatches subdivisionRule.lhs [consEdge a b] (matchAB a b) = true := by
  rw [bindingMatches_subdLhs_iff]
  rfl

/-- `matchAB a b ∈ allMatches subdivisionRule [consEdge a b]` when `a ≠ b`. -/
theorem matchAB_mem_allMatches (a b : ℕ) (hab : a ≠ b) :
    matchAB a b ∈ allMatches subdivisionRule [consEdge a b] := by
  show matchAB a b ∈ (allFunctions 2 (vertexList [consEdge a b])).filter _
  rw [vertexList_consEdge_of_ne a b hab]
  rw [List.mem_filter]
  exact ⟨matchAB_mem_allFunctions a b, matchAB_bindingMatches a b hab⟩

/-- Every member of `allMatches subdivisionRule [consEdge a b]` equals
`matchAB a b`. -/
theorem allMatches_unique (a b : ℕ) :
    ∀ ρ ∈ allMatches subdivisionRule [consEdge a b], ρ = matchAB a b := by
  intro ρ hρ
  -- Extract bindingMatches = true
  have : bindingMatches subdivisionRule.lhs [consEdge a b] ρ = true := by
    have := List.mem_filter.mp hρ
    exact this.2
  rw [bindingMatches_subdLhs_iff] at this
  exact match_eq_matchAB_of_image_eq this

/-! ## No duplicates in `allFunctions 2 [a, b]` for `a ≠ b` -/

/-- `ρ ↦ (ρ 0, ρ 1)` is injective on `Fin 2 → ℕ`. -/
theorem pair_proj_injective {ρ σ : Fin 2 → ℕ}
    (h : (ρ ⟨0, by decide⟩, ρ ⟨1, by decide⟩) = (σ ⟨0, by decide⟩, σ ⟨1, by decide⟩)) :
    ρ = σ := by
  have h0 : ρ ⟨0, by decide⟩ = σ ⟨0, by decide⟩ := congrArg Prod.fst h
  have h1 : ρ ⟨1, by decide⟩ = σ ⟨1, by decide⟩ := congrArg Prod.snd h
  apply fin2_funext h0 h1

/-- For `a ≠ b`, `allFunctions 2 [a, b]` has no duplicates. -/
theorem allFunctions_2_nodup (a b : ℕ) (hab : a ≠ b) :
    (allFunctions 2 [a, b]).Nodup := by
  apply List.Nodup.of_map (fun ρ => (ρ ⟨0, by decide⟩, ρ ⟨1, by decide⟩))
  rw [allFunctions_2_pair_projection]
  -- Goal: [(a,a), (a,b), (b,a), (b,b)] is Nodup when a ≠ b
  simp [List.Nodup, hab, hab.symm, Ne.symm hab]

/-- For `a ≠ b`, `allMatches subdivisionRule [consEdge a b] = [matchAB a b]`. -/
theorem allMatches_eq_singleton_matchAB (a b : ℕ) (hab : a ≠ b) :
    allMatches subdivisionRule [consEdge a b] = [matchAB a b] := by
  -- Strategy: every element equals matchAB a b (uniqueness) + Nodup forces length ≤ 1
  -- + membership forces length ≥ 1 ⇒ singleton.
  have hmem := matchAB_mem_allMatches a b hab
  have huniq := allMatches_unique a b
  have hnodup_orig : (allFunctions 2 [a, b]).Nodup := allFunctions_2_nodup a b hab
  -- allMatches = filter of allFunctions, hence Nodup too.
  have hnodup_matches : (allMatches subdivisionRule [consEdge a b]).Nodup := by
    show (((allFunctions 2 (vertexList [consEdge a b])).filter _)).Nodup
    rw [vertexList_consEdge_of_ne a b hab]
    exact hnodup_orig.filter _
  -- Destructure on allMatches.
  rcases h : allMatches subdivisionRule [consEdge a b] with _ | ⟨ρ, rest⟩
  · -- Empty: contradicts membership.
    rw [h] at hmem; exact absurd hmem (List.not_mem_nil)
  · -- Non-empty: ρ = matchAB a b by uniqueness; rest must be empty by Nodup + uniqueness.
    have hρ_in : ρ ∈ allMatches subdivisionRule [consEdge a b] := by
      rw [h]; exact List.mem_cons_self
    have hρ_eq : ρ = matchAB a b := huniq ρ hρ_in
    have hrest_empty : rest = [] := by
      cases hrest : rest with
      | nil => rfl
      | cons σ rest' =>
        exfalso
        have hσ_in : σ ∈ allMatches subdivisionRule [consEdge a b] := by
          rw [h, hrest]; exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
        have hσ_eq : σ = matchAB a b := huniq σ hσ_in
        -- Nodup of ρ :: σ :: rest' says ρ ∉ σ :: rest', so ρ ≠ σ.
        rw [h, hrest] at hnodup_matches
        have h_head_not_in : ρ ∉ σ :: rest' :=
          (List.nodup_cons.mp hnodup_matches).1
        apply h_head_not_in
        rw [hρ_eq, ← hσ_eq]
        exact List.mem_cons_self
    rw [hρ_eq, hrest_empty]
    rfl

/-! ## One step on one edge -/

/-- For `a ≠ b`, `singleWayStep subdivisionSys [consEdge a b]
= [consEdge a (max a b + 1), consEdge (max a b + 1) b]`. -/
theorem singleWayStep_subdivisionSys_consEdge_of_ne (a b : ℕ) (hab : a ≠ b) :
    singleWayStep subdivisionSys [consEdge a b]
      = [consEdge a (max a b + 1), consEdge (max a b + 1) b] := by
  have hc : edgesContained (mapPattern (matchAB a b) subdivisionRule.lhs)
      [consEdge a b] = true := by
    rw [mapPattern_matchAB_lhs]; simp [edgesContained, edgeCount]
  have hfold : stepFold subdivisionSys [consEdge a b]
      = (allMatches subdivisionRule [consEdge a b]).foldl
          (fireIfFree subdivisionRule 0 (nextFresh [consEdge a b]))
          ⟨[consEdge a b], [], 0, []⟩ := rfl
  show (stepFold subdivisionSys [consEdge a b]).avail
      ++ (stepFold subdivisionSys [consEdge a b]).produced = _
  rw [hfold, allMatches_eq_singleton_matchAB a b hab]
  show (fireIfFree subdivisionRule 0 (nextFresh [consEdge a b])
          ⟨[consEdge a b], [], 0, []⟩ (matchAB a b)).avail
      ++ (fireIfFree subdivisionRule 0 (nextFresh [consEdge a b])
          ⟨[consEdge a b], [], 0, []⟩ (matchAB a b)).produced = _
  rw [fireIfFree_avail_of_contained _ _ _ _ _ hc,
      fireIfFree_produced_of_contained _ _ _ _ _ hc]
  show removeEdges [consEdge a b] [consEdge a b] ++ ([] ++ mapPattern
      (fun i : Fin (subdivisionRule.numBound + subdivisionRule.numFresh) =>
        if h : i.val < subdivisionRule.numBound then matchAB a b ⟨i.val, h⟩
        else nextFresh [consEdge a b] + 0 + (i.val - subdivisionRule.numBound))
      subdivisionRule.rhs) = _
  rw [removeEdges_consEdge_self, nextFresh_consEdge_of_ne a b hab,
    singleWayStep_inner_extension_eq a b]
  show [] ++ ([] ++ mapPattern (matchABext a b) subdivisionRule.rhs) = _
  rw [mapPattern_matchABext_rhs]
  rfl

end MultiwayExec
end InfraFormalization
