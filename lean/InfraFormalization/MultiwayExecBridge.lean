/-
Casts from the executable rewriting types to the abstract ones.

The abstract types (`Hypergraph V`, `Rule P`, `RewritingSystem`, `Step`, `MultiStep`) use multisets
and propositions. The executable types (`ExecHG ℕ`, `ExecRule`, `ExecSystem`, `singleWayStep`) use
lists and are computable. This module defines `ExecRule.toRule`, which embeds the left-hand side
into
the pattern type `Fin (numBound + numFresh)`, and the single-rule system
`ExecSystem.toRewritingSystem_single`. It proves that the consumed edges of an executable match lift
to the abstract consumed edges and that `ExecHG.toHypergraph` sends `[]` to the empty hypergraph and
`e :: H` to the insertion of `e`. No theorem relates `singleWayStep` to `Step` or `MultiStep`.
-/

import InfraFormalization.MultiwayExec

namespace InfraFormalization
namespace MultiwayExec

open Hypergraph

/-! ## State / rule / system casts -/

/-- The inclusion `Fin numBound → Fin (numBound + numFresh)` that keeps the value. -/
def Fin.embedSuffix (numBound numFresh : ℕ) (i : Fin numBound) :
    Fin (numBound + numFresh) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- The abstract rule on `Fin (numBound + numFresh)` whose left-hand side is the executable
left-hand
side mapped by `Fin.embedSuffix` and whose right-hand side is the executable right-hand side. -/
def ExecRule.toRule (r : ExecRule) : Rule (Fin (r.numBound + r.numFresh)) where
  lhs := ⟨↑(r.lhs.map (Hyperedge.map (Fin.embedSuffix r.numBound r.numFresh)))⟩
  rhs := ⟨↑r.rhs⟩

/-- The abstract rewriting system consisting of the single rule `r.toRule`. Systems whose rules have
different `numBound + numFresh` have no common pattern type and are not covered. -/
def ExecSystem.toRewritingSystem_single (r : ExecRule) :
    RewritingSystem (Fin (r.numBound + r.numFresh)) where
  rules := [r.toRule]

/-! ## Single-application correspondence -/

/-- The multiset of `mapPattern ρ` applied to the embedded left-hand side equals
`r.toRule.lhs.edges.map (Hyperedge.map ρ)`. -/
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

/-- `ExecHG.toHypergraph [] = Hypergraph.empty`. -/
@[simp] theorem ExecHG.toHypergraph_nil :
    ExecHG.toHypergraph ([] : ExecHG ℕ) = Hypergraph.empty := by
  unfold ExecHG.toHypergraph
  show ⟨↑([] : List (Hyperedge ℕ))⟩ = (⟨0⟩ : Hypergraph ℕ)
  rfl

/-- `ExecHG.toHypergraph (e :: H)` is `ExecHG.toHypergraph H` with `e` inserted into its edge
multiset. -/
@[simp] theorem ExecHG.toHypergraph_cons (e : Hyperedge ℕ) (H : ExecHG ℕ) :
    ExecHG.toHypergraph (e :: H) =
      (⟨e ::ₘ (ExecHG.toHypergraph H).edges⟩ : Hypergraph ℕ) := by
  unfold ExecHG.toHypergraph
  show (⟨↑(e :: H : List (Hyperedge ℕ))⟩ : Hypergraph ℕ) =
    (⟨e ::ₘ ↑H⟩ : Hypergraph ℕ)
  rfl

/-! ## Summary

`ExecHG.toHypergraph`, `ExecRule.toRule` and `ExecSystem.toRewritingSystem_single` map executable
states, rules and single-rule systems to their abstract counterparts. A simulation theorem from
`singleWayStep` to `MultiStep`, and the construction of an `Application` from an executable match,
are not in this module. -/

end MultiwayExec
end InfraFormalization
