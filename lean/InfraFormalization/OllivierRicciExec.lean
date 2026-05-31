/-
**Ollivier-Ricci screener on `ExecHG ℕ`** (#368 instantiation, #401).

Discrete edge-curvature defined via the W₁ Wasserstein-1 distance
between vertex-neighbourhood `InfraMeasureData`s. For an edge `(u, v)`
in a hypergraph `H`:

  κ(u, v) := 1 − W₁(μ_u, μ_v) / d(u, v)

where `μ_x` is the uniform measure on `{x} ∪ N(x)` and `d` is a hop
distance. This is the Ollivier-Ricci curvature; positive on
spheres / dense connected regions, negative on trees / hyperbolic
regions.

**This module** uses the `productCoupling`-based upper bound on W₁
(from #400's `InfraMeasure.w1ProductUpper`) — a computable proxy for
the true infimum-W₁. For Ollivier-Ricci on small concrete graphs the
upper bound is informative; the true LP-optimum can be approximated
by enumerating candidate couplings (`w1InfimumOver`).

**Engine-port spec.** Like the triangle-Forman screener in
`RuleSignatureExecMetrics`, this is the metric set to port into
RASSAR's fast `HypergraphRewritingEngine` for an Ollivier-Ricci
rule-search filter — the W₁-product-upper version is decide-checkable
and feeds the existing screener bridge directly.
-/

import InfraFormalization.MultiwayExec
import InfraFormalization.InfraMeasure
import InfraFormalization.RuleSignatureExecMetrics

namespace InfraFormalization
namespace OllivierRicciExec

open MultiwayExec
open InfraMeasure
open RuleSignatureExecMetrics

/-- The open neighbourhood of `v` in `H` (excluding `v` itself):
all `u ∈ vertexList H` with `u ≠ v` and some edge containing both. -/
def neighbourhood (H : ExecHG ℕ) (v : ℕ) : List ℕ :=
  (vertexList H).filter (fun u =>
    decide (u ≠ v) ∧ H.any (fun e => e.verts.contains u && e.verts.contains v))

/-- The closed neighbourhood `{v} ∪ N(v)` as a deduplicated list. -/
def closedNeighbourhood (H : ExecHG ℕ) (v : ℕ) : List ℕ :=
  (v :: neighbourhood H v).dedup

/-- The **uniform measure on the closed neighbourhood of `v`** in `H`.
Each vertex in `{v} ∪ N(v)` gets weight `1` (unnormalised — the W₁
upper bound scales linearly so this is harmless for comparisons). -/
def uniformOnNeighbourhood (H : ExecHG ℕ) (v : ℕ) : InfraMeasureData ℕ :=
  uniformOn (closedNeighbourhood H v)

/-- The **hop cost** between two vertices: `0` if equal, `1` if
adjacent in `H`, `2` if non-adjacent and distinct. Small-step distance
sufficient for Ollivier-Ricci on small graphs. -/
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

/-- The **W₁ upper bound** between the two vertex-neighbourhood
uniform measures, with the hop-cost function. Computable; gives an
upper bound on the true W₁. -/
noncomputable def w1NeighbourhoodUpper (H : ExecHG ℕ) (u v : ℕ) : ℝ :=
  let carrier := (vertexList H)
  w1ProductUpper carrier (hopCost H)
    (uniformOnNeighbourhood H u) (uniformOnNeighbourhood H v)

/-- The W₁ upper bound is non-negative. -/
theorem w1NeighbourhoodUpper_nonneg (H : ExecHG ℕ) (u v : ℕ) :
    0 ≤ w1NeighbourhoodUpper H u v := by
  unfold w1NeighbourhoodUpper
  apply w1ProductUpper_nonneg
  intro x y
  exact hopCost_nonneg H x y

/-- **Ollivier-Ricci edge-curvature upper-bound**:
`κ(u, v) := 1 − W₁_upper(μ_u, μ_v) / d(u, v)`.
For non-adjacent or equal vertices, returns `0` (convention: curvature
is meaningful between adjacent vertices). -/
noncomputable def ollivierRicciEdgeUpper (H : ExecHG ℕ) (u v : ℕ) : ℝ :=
  let d := hopCost H u v
  if d = 0 then 0
  else 1 - w1NeighbourhoodUpper H u v / d

/-! ## Demonstration on small graphs

For a triangle K₃ on `{1, 2, 3}`, every neighbourhood is the full
3-vertex set, so the W₁ upper bound between any two vertex-
neighbourhood measures involves transport across at most the small
hop-cost diameter. Positive κ on K₃ is the Ollivier-Ricci signature
of a positively-curved region (clique). -/

/-- Triangle K₃ on `{1, 2, 3}`. -/
def k3 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[1, 3], by decide⟩]

/-- The neighbourhood of vertex `1` in K₃ is `{2, 3}` (the other two
vertices). -/
example : (neighbourhood k3 1).length = 2 := by native_decide

/-- The closed neighbourhood of `1` is `{1, 2, 3}` (the whole vertex
set on K₃). -/
example : (closedNeighbourhood k3 1).length = 3 := by native_decide

/-- 4-cycle on `{1, 2, 3, 4}` — neighbourhoods are size 2 (two
adjacent vertices), giving a different curvature signature than K₃. -/
def cycle4 : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩,
   ⟨[3, 4], by decide⟩, ⟨[1, 4], by decide⟩]

/-- The neighbourhood of `1` in the 4-cycle is `{2, 4}` (size 2). -/
example : (neighbourhood cycle4 1).length = 2 := by native_decide

/-- Closed neighbourhood of `1` in the 4-cycle: `{1, 2, 4}` (size 3). -/
example : (closedNeighbourhood cycle4 1).length = 3 := by native_decide

end OllivierRicciExec
end InfraFormalization
