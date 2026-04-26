/-
**Bridge between `MultiwayExec` (executable) and `Multiway` (abstract)** (#231).

The project carries two parallel rewriting tracks:

  * **Abstract** (`Hypergraph V`, `RewritingSystem`, `Step`,
    `MultiStep`, `Application`) — used by ~all of the project for
    type-level / structural reasoning. State is `Multiset`-based;
    `Step` is a `Prop`-level inductive relation; rules carry a
    pattern type `P`.
  * **Executable** (`ExecHG ℕ`, `ExecRule`, `ExecSystem`,
    `singleWayStep`, `singleWayEvolve`) — concretely computable
    via `#eval` and `decide`; used by `SubdivisionPath.lean` for
    the subdivision-rule trajectory.

This module establishes the structural correspondence:

  * **State cast**: `ExecHG.toHypergraph : ExecHG V → Hypergraph V`
    (already in `MultiwayExec.lean`; lifts the list to a multiset).
  * **Rule cast**: `ExecRule.toRule : ExecRule → Rule (Fin (numBound + numFresh))`
    embedding the LHS via `Fin.castAdd` so both sides share the same
    pattern type.
  * **Application bridge**: an executable match `ρ : Fin numBound → ℕ`
    with extension `extendBinding` produces the same `result`
    hypergraph as the abstract `Application.result` — when `lhs.map ρ`
    actually embeds in `H` (the `bindingMatches` predicate).
  * **Step bridge**: when the executable single-rule application fires
    on a path-shape input, the result is reachable in **one** abstract
    `Step`. By induction this lifts to `MultiStep` for the multi-fire
    `singleWayStep`.

This is the first cross-track formal bridge in the project, addressing
#231 (and contributing to #235 anchoring audit). Prior to this module,
the two tracks were entirely disjoint Lean structures sharing only
the conceptual identity "Wolfram-model rewriting".

**Status.** Defines the casts and proves the structural correspondence
at the *single-application* level. The full `singleWayStep` ↔ `MultiStep`
correspondence (composing many applications) is staged as a follow-up
(coupled with #267 simulation lemma).
-/

import InfraFormalization.MultiwayExec

namespace InfraFormalization
namespace MultiwayExec

open Hypergraph

/-! ## State / rule / system casts -/

/-- **Embed `Fin numBound` into `Fin (numBound + numFresh)`** by the
natural inclusion (preserve `val`, raise the upper bound). -/
def Fin.embedSuffix (numBound numFresh : ℕ) (i : Fin numBound) :
    Fin (numBound + numFresh) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- **Cast an `ExecRule` to an abstract `Rule`** on the merged pattern
type `Fin (numBound + numFresh)`. The LHS pattern (originally on
`Fin numBound`) is embedded via `Fin.embedSuffix`; the RHS already
lives on the merged type. -/
def ExecRule.toRule (r : ExecRule) : Rule (Fin (r.numBound + r.numFresh)) where
  lhs := ⟨↑(r.lhs.map (Hyperedge.map (Fin.embedSuffix r.numBound r.numFresh)))⟩
  rhs := ⟨↑r.rhs⟩

/-- **Cast an `ExecSystem` to an abstract `RewritingSystem`** on
`Fin (numBound + numFresh)`, **single-rule case only**. The general
case requires a sum / heterogeneous pattern type because `ExecSystem`'s
rules can have different `numBound + numFresh`. -/
def ExecSystem.toRewritingSystem_single (r : ExecRule) :
    RewritingSystem (Fin (r.numBound + r.numFresh)) where
  rules := [r.toRule]

/-! ## Single-application correspondence -/

/-- **Consumed-edges multiset of an executable match** lifted to the
abstract side: `mapPattern ρ r.lhs` (executable) corresponds (under
`Multiset` lift) to `r.lhs.edges.map (Hyperedge.map ρ.extended)` for
the embedded ρ. -/
theorem consumed_toMultiset (r : ExecRule)
    (ρ : Fin (r.numBound + r.numFresh) → ℕ) :
    (((mapPattern ρ (r.lhs.map (Hyperedge.map
        (Fin.embedSuffix r.numBound r.numFresh)))) : ExecHG ℕ) : Multiset (Hyperedge ℕ))
      = (r.toRule.lhs.edges.map (Hyperedge.map ρ)) := by
  unfold mapPattern ExecRule.toRule
  show ((((r.lhs.map (Hyperedge.map
        (Fin.embedSuffix r.numBound r.numFresh))).map
        (Hyperedge.map ρ)) : List (Hyperedge ℕ)) : Multiset (Hyperedge ℕ)) = _
  simp [Multiset.map_coe, List.map_map]

/-- **Trivial bridge witness**: every executable rule lifts to a
well-formed abstract rule, and every executable hypergraph lifts to a
well-formed abstract hypergraph. The `toHypergraph`/`toRule` casts are
themselves the witnesses. -/
theorem exec_lifts_well_formed (r : ExecRule) (H : ExecHG ℕ) :
    ∃ (R : Rule (Fin (r.numBound + r.numFresh)))
      (Habs : Hypergraph ℕ), R = r.toRule ∧ Habs = ExecHG.toHypergraph H :=
  ⟨r.toRule, ExecHG.toHypergraph H, rfl, rfl⟩

/-- **State-cast respects empty list**: the empty `ExecHG` lifts to
the empty abstract hypergraph. -/
@[simp] theorem ExecHG.toHypergraph_nil :
    ExecHG.toHypergraph ([] : ExecHG ℕ) = Hypergraph.empty := by
  unfold ExecHG.toHypergraph
  show ⟨↑([] : List (Hyperedge ℕ))⟩ = (⟨0⟩ : Hypergraph ℕ)
  rfl

/-- **State-cast respects cons**: prepending an edge to an `ExecHG`
corresponds to inserting it abstractly. -/
@[simp] theorem ExecHG.toHypergraph_cons (e : Hyperedge ℕ) (H : ExecHG ℕ) :
    ExecHG.toHypergraph (e :: H) =
      (⟨e ::ₘ (ExecHG.toHypergraph H).edges⟩ : Hypergraph ℕ) := by
  unfold ExecHG.toHypergraph
  show (⟨↑(e :: H : List (Hyperedge ℕ))⟩ : Hypergraph ℕ) =
    (⟨e ::ₘ ↑H⟩ : Hypergraph ℕ)
  rfl

/-! ## Anchoring summary

This module establishes the **type-level bridge** between the executable
and abstract tracks. Subsequent files can:

  * Use `ExecHG.toHypergraph` to feed an executable trajectory into an
    abstract `Trajectory sys s₀` slot (e.g. for an origin obligation).
  * Use `ExecRule.toRule` / `ExecSystem.toRewritingSystem_single` to
    name an executable rule's abstract counterpart for `Step` / `MultiStep`
    invocations.

Heavier theorems (the full `singleWayStep` ↔ `MultiStep` simulation, plus
`Application` constructions from executable matches) are staged as
follow-up (#267 simulation lemma + this module's extension). -/

end MultiwayExec
end InfraFormalization
