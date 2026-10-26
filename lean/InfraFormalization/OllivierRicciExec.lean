/-
A transport-cost quantity on neighbourhoods in `ExecHG ℕ`.

The Ollivier–Ricci curvature of an edge `(u, v)` is `κ(u, v) = 1 − W₁(μ_u, μ_v) / d(u, v)`, with
`μ_x`
the uniform probability measure on the closed neighbourhood `{x} ∪ N(x)`. This module defines the
closed neighbourhood, the unnormalised weight 1 on it, a hop cost (0, 1 or 2), and the transport
cost
`w1NeighbourhoodProduct` of the product weight of the two neighbourhood weights. The product weight is
not normalised and its marginals are not `μ_u` and `μ_v`, so this transport cost is not W₁ and not
an
upper bound on it. The module proves non-negativity and checks neighbourhood sizes on `K₃` and the
4-cycle by `native_decide`.
-/

import InfraFormalization.MultiwayExec
import InfraFormalization.InfraMeasure
import InfraFormalization.RuleSignatureExecMetrics

namespace InfraFormalization
namespace OllivierRicciExec

open MultiwayExec
open InfraMeasure
open RuleSignatureExecMetrics

/-- The vertices `u ≠ v` of `H` that share an edge with `v`. -/
def neighbourhood (H : ExecHG ℕ) (v : ℕ) : List ℕ :=
  (vertexList H).filter (fun u =>
    (u != v) && H.any (fun e => e.verts.contains u && e.verts.contains v))

/-- The closed neighbourhood `{v} ∪ N(v)` as a deduplicated list. -/
def closedNeighbourhood (H : ExecHG ℕ) (v : ℕ) : List ℕ :=
  (v :: neighbourhood H v).dedup

/-- The weight equal to 1 on each vertex of `{v} ∪ N(v)` and 0 elsewhere, not normalised. -/
def uniformOnNeighbourhood (H : ExecHG ℕ) (v : ℕ) : InfraMeasureData ℕ :=
  uniformOn (closedNeighbourhood H v)

/-- 0 if `u = v`, 1 if `u` and `v` are adjacent in `H`, and 2 otherwise. -/
def hopCost (H : ExecHG ℕ) (u v : ℕ) : ℝ :=
  if u = v then 0
  else if execAdj H u v then 1
  else 2

/-- Hop cost is non-negative. -/
theorem hopCost_nonneg (H : ExecHG ℕ) (u v : ℕ) :
    0 ≤ hopCost H u v := by
  unfold hopCost
  by_cases huv : u = v
  · simp [huv]
  · by_cases hadj : execAdj H u v
    · simp [huv, hadj]
    · simp [huv, hadj]

/-- The transport cost, with `hopCost`, of the product of the neighbourhood weights of `u` and `v`.
-/
noncomputable def w1NeighbourhoodProduct (H : ExecHG ℕ) (u v : ℕ) : ℝ :=
  let carrier := (vertexList H)
  w1ProductCost carrier (hopCost H)
    (uniformOnNeighbourhood H u) (uniformOnNeighbourhood H v)

/-- `w1NeighbourhoodProduct` is non-negative. -/
theorem w1NeighbourhoodUpper_nonneg (H : ExecHG ℕ) (u v : ℕ) :
    0 ≤ w1NeighbourhoodProduct H u v := by
  unfold w1NeighbourhoodProduct
  apply w1ProductUpper_nonneg
  intro x y
  exact hopCost_nonneg H x y

/-- `1 − w1NeighbourhoodProduct H u v / hopCost H u v`, and 0 when `u = v`. -/
noncomputable def ollivierRicciEdgeProduct (H : ExecHG ℕ) (u v : ℕ) : ℝ :=
  let d := hopCost H u v
  if d = 0 then 0
  else 1 - w1NeighbourhoodProduct H u v / d

/-! ## Neighbourhoods in `K₃` and the 4-cycle -/

/-- Triangle K₃ on `{1, 2, 3}`. -/
def k3 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[1, 3], by decide⟩]

/-- The neighbourhood of vertex `1` in K₃ is `{2, 3}` (the other two
vertices). -/
example : (neighbourhood k3 1).length = 2 := by native_decide

/-- The closed neighbourhood of `1` is `{1, 2, 3}` (the whole vertex
set on K₃). -/
example : (closedNeighbourhood k3 1).length = 3 := by native_decide

/-- The 4-cycle on `{1, 2, 3, 4}`. -/
def cycle4 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩,
   ⟨[3, 4], by decide⟩, ⟨[1, 4], by decide⟩]

/-- The neighbourhood of `1` in the 4-cycle is `{2, 4}` (size 2). -/
example : (neighbourhood cycle4 1).length = 2 := by native_decide

/-- Closed neighbourhood of `1` in the 4-cycle: `{1, 2, 4}` (size 3). -/
example : (closedNeighbourhood cycle4 1).length = 3 := by native_decide

end OllivierRicciExec
end InfraFormalization
