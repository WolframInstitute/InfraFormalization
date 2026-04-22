/-
**Blowup / refinement operators** (Group IA / #113 IA5).

A *blowup* refines a hypergraph by subdividing vertices, edges, or
both. The canonical example: the cycle blowup `cycleHypergraph n →
cycleHypergraph (2n)` halves each edge.

Blowups commute with discrete calculus (`dagDerivative`,
`laplacianHyper`) up to `O(1/n)` rescaling — this is the
renormalization-flow direction of the infrageometry program.

**Connection to hypergraphs.** Every blowup is a map between two
`Hypergraph V`'s (or more generally, between `Hypergraph V` and
`Hypergraph W`). No continuum.
-/

import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.DagBlowup

namespace InfraFormalization

/-! ## Cycle-doubling blowup -/

/-- **Edge-midpoint subdivision** on a cycle hypergraph: each edge
`[k, k+1]` becomes two edges `[2k, 2k+1], [2k+1, 2k+2]` in the
doubled cycle `cycleHypergraph (2n)`. Stated at the index level. -/
def cycleDoubleIndex (n : Nat) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val, by
    have := i.isLt
    omega⟩

/-- **Cycle blowup embeds vertices** `Fin n ↪ Fin (2n)`. -/
theorem cycleDoubleIndex_injective {n : Nat} (hn : 0 < n) :
    Function.Injective (cycleDoubleIndex n) := by
  intros i j hij
  unfold cycleDoubleIndex at hij
  have hval := congrArg Fin.val hij
  simp at hval
  ext
  omega

/-- **Scale factor** of a cycle-doubling blowup: each refinement
halves the edge length, so a sequence of `k` blowups scales
distance by `1/2^k`. -/
noncomputable def blowupScale (k : Nat) : ℝ := (1 : ℝ) / (2 ^ k)

theorem blowupScale_pos (k : Nat) : 0 < blowupScale k := by
  unfold blowupScale
  positivity

theorem blowupScale_halves (k : Nat) : blowupScale (k + 1) = blowupScale k / 2 := by
  unfold blowupScale
  rw [pow_succ]
  ring

end InfraFormalization
