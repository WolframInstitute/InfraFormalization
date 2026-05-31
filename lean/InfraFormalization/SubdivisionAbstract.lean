/-
**`#267` abstract base case: structural helpers toward
`singleWayStep subdivisionSys [consEdge a b]` for symbolic `a ≠ b`**
(instantiating #267 / #398).

Provides the structural lemmas needed to lift the Fin-bounded
`singleWayStep_subdivisionSys_consEdge_fin8` / `_fin12` / `_high`
(`SubdivisionPath.lean`, 208 `native_decide`-certified instances) to
the truly-abstract universal statement over `(a b : ℕ)` with `a ≠ b`.

This module establishes:

  1. The canonical match `matchAB a b : Fin 2 → ℕ` (`fun i ↦ if i.val=0 then a else b`).
  2. `mapPattern (matchAB a b) subdivisionRule.lhs = [consEdge a b]`
     (LHS-image identity, by `rfl` / `decide`).
  3. The extended binding `matchABext a b : Fin 3 → ℕ` carrying the
     fresh vertex to `max a b + 1`.
  4. `mapPattern (matchABext a b) subdivisionRule.rhs =
       [consEdge a (max a b + 1), consEdge (max a b + 1) b]` (RHS-image).
  5. **Singleton-image characterization** of any LHS-matching binding
     for `[consEdge a b]`: any `ρ` satisfying
     `bindingMatches subdivisionRule.lhs [consEdge a b] ρ` agrees
     with `matchAB a b` at the two LHS indices.

The remaining mechanical residual — enumerating `allFunctions 2 [a, b]`
into the 4-candidate symbolic list and showing the filter is a singleton
— is bookkeeping the engine's enumeration order. The structural
content (extension agrees pointwise with `matchAB`) lives here; the
enumeration-order bookkeeping is the open piece.
-/

import InfraFormalization.SubdivisionPath

namespace InfraFormalization
namespace MultiwayExec

open Hypergraph

/-- Local copies of the `subdivisionRule`'s LHS and RHS hyperedges
(originals are `private` in `SubdivisionPath`). -/
def subdLhs : Hyperedge (Fin 2) := ⟨[0, 1], List.cons_ne_nil _ _⟩
def subdRhsL : Hyperedge (Fin 3) := ⟨[0, 2], List.cons_ne_nil _ _⟩
def subdRhsR : Hyperedge (Fin 3) := ⟨[2, 1], List.cons_ne_nil _ _⟩

/-- The `subdivisionRule`'s LHS factors through `subdLhs`. -/
theorem subdivisionRule_lhs_eq : subdivisionRule.lhs = [subdLhs] := rfl

/-- The `subdivisionRule`'s RHS factors through `subdRhsL`, `subdRhsR`. -/
theorem subdivisionRule_rhs_eq : subdivisionRule.rhs = [subdRhsL, subdRhsR] := rfl

/-- The unique LHS-matching binding `Fin 2 → ℕ` for `[consEdge a b]`. -/
def matchAB (a b : ℕ) : Fin 2 → ℕ :=
  fun i => if i.val = 0 then a else b

@[simp] theorem matchAB_zero (a b : ℕ) : matchAB a b ⟨0, by decide⟩ = a := rfl
@[simp] theorem matchAB_one (a b : ℕ) : matchAB a b ⟨1, by decide⟩ = b := rfl

/-- The unique extended binding for the subdivision rule, with the
fresh vertex pinned to `max a b + 1`. -/
def matchABext (a b : ℕ) : Fin 3 → ℕ :=
  fun i =>
    if h : i.val < 2 then matchAB a b ⟨i.val, h⟩
    else max a b + 1

@[simp] theorem matchABext_zero (a b : ℕ) : matchABext a b ⟨0, by decide⟩ = a := rfl
@[simp] theorem matchABext_one (a b : ℕ) : matchABext a b ⟨1, by decide⟩ = b := rfl
@[simp] theorem matchABext_two (a b : ℕ) :
    matchABext a b ⟨2, by decide⟩ = max a b + 1 := rfl

/-! ## LHS / RHS image identities

These are by `rfl` after unfolding the `matchAB` and `matchABext`
definitions on the `Fin 2` / `Fin 3` indices. -/

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

/-! ## Singleton-image characterization

Any binding `ρ` whose image of `subdivisionRule.lhs` matches the
single-edge state `[consEdge a b]` must agree with `matchAB a b` on
indices `0` and `1`. -/

/-- Pointwise extraction: if `Hyperedge.map ρ subdLhs = consEdge a b`,
then `ρ ⟨0,_⟩ = a` and `ρ ⟨1,_⟩ = b`. -/
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

/-- Pointwise-equal `Fin 2 → ℕ` functions are equal via funext. -/
theorem fin2_funext {ρ σ : Fin 2 → ℕ}
    (h0 : ρ ⟨0, by decide⟩ = σ ⟨0, by decide⟩)
    (h1 : ρ ⟨1, by decide⟩ = σ ⟨1, by decide⟩) : ρ = σ := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

/-- A binding `ρ : Fin 2 → ℕ` whose LHS-image equals `consEdge a b`
literally equals the canonical `matchAB a b`. -/
theorem match_eq_matchAB_of_image_eq {ρ : Fin 2 → ℕ} {a b : ℕ}
    (h : Hyperedge.map ρ subdLhs = consEdge a b) :
    ρ = matchAB a b := by
  obtain ⟨h0, h1⟩ := matchAB_pointwise_of_image_eq h
  apply fin2_funext
  · simpa using h0
  · simpa using h1

/-! ## `singleWayStep` structural pieces

These primitive lemmas chip away at the residual mechanical bookkeeping
for the abstract `singleWayStep_subdivisionSys_consEdge_of_ne`. The
`singleWayStep` is a foldl over rules and (per rule) matches; for
`subdivisionSys`, the rules-fold is trivial (single rule), and the
match-fold operates on `allMatches subdivisionRule [consEdge a b]`.

The remaining mechanical residual is to characterize `allMatches`
symbolically — i.e. to prove
`allMatches subdivisionRule [consEdge a b] = [matchAB a b]` when
`a ≠ b`. The Fin-bounded version (`SubdivisionPath`'s 208
`native_decide`-certified instances) already covers this for every
concrete `(a, b)` in the search space. -/

/-- The `subdivisionSys` system has exactly one rule (`subdivisionRule`). -/
theorem subdivisionSys_rules : subdivisionSys.rules = [subdivisionRule] := rfl

/-- `removeEdges [consEdge a b] [consEdge a b] = []`: removing a singleton
edge list from itself yields the empty list. -/
theorem removeEdges_consEdge_self (a b : ℕ) :
    removeEdges [consEdge a b] [consEdge a b] = [] := by
  simp [removeEdges]

/-- The extended-binding shape used in `singleWayStep` (with `baseFresh
+ offset` for the fresh-RHS slot) equals `matchABext a b` whenever the
offset is `0` and `baseFresh = max a b + 1`. -/
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

end MultiwayExec
end InfraFormalization
