/-
**PerpendicularModuli — multi-method perpendicularity** (#390 starter).

PHAJEK's `InfraPerpendicularQ` in `SyntheticInfrageometry` exposes
multiple inequivalent definitions of perpendicularity (Schoenberg,
Centroid, four-corner-wedge — `resources/SyntheticInfrageometry/Kernel/InfraEquality.wl`),
each a distinct invariant. The paclet treats this as a feature via an
explicit `Method` argument. **This is the F1 moduli observation made
structural at the perpendicular layer**: a graph does not determine
*one* notion of perpendicularity — it determines a moduli of
inequivalent notions, each a method choice.

This module is the Lean realisation of that pattern. A `PerpMethod`
inductive enumerates the methods; per-method predicates compute the
perpendicularity verdict; a concrete `native_decide`-checked example
shows the methods *disagree* on a small graph — the F1 sharpening at
the perpendicular level.

**Starter scope.** Two concrete decidable methods that demonstrably
disagree on the 4-cycle. Schoenberg / Centroid / Four-corner-wedge
bodies left to the follow-up; the framework here is what holds them
together, and the central non-implication theorem
`perpendicular_methods_disagree` is the structural F1 realisation.
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace InfraFormalization
namespace PerpendicularModuli

/-- **The space of perpendicularity methods**. Each method is a
distinct invariant; the F1 moduli observation says no single one is
canonical. -/
inductive PerpMethod
  | adjacencyWedge    -- v adjacent to both u and w, but u, w not adjacent
  | sharedNeighbour   -- u, w have v as a unique common neighbour (and u ≠ w)
  | pythagoreanHop    -- "Schoenberg-style": hop count d(u,v)² + d(v,w)² = d(u,w)²
deriving DecidableEq, Repr

/-- Local computable adjacency on a `List (Hyperedge V)` (the ExecHG
representation): `u, w` are adjacent iff `u ≠ w` and some edge contains
both. Fully `decide`-able for finite concrete graphs. -/
def adjB {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u w : V) : Bool :=
  (u != w) && H.any (fun e => e.verts.contains u && e.verts.contains w)

/-- Common-neighbour count of `u` and `w` over a finite carrier
`carrier`, excluding `u` and `w` themselves. -/
def commonNeighbours {V : Type*} [DecidableEq V]
    (carrier : List V) (H : List (Hyperedge V)) (u w : V) : ℕ :=
  (carrier.filter (fun v => v != u && v != w && adjB H u v && adjB H v w)).length

/-- **adjacency-wedge perpendicularity at `v`**: `v` is adjacent to both
`u` and `w`, and `u, w` are *not* adjacent to each other. -/
def isPerpAdjacencyWedge {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u v w : V) : Bool :=
  adjB H u v && adjB H v w && !adjB H u w

/-- **shared-neighbour perpendicularity at `v`** over a finite carrier:
`v` is the *unique* common neighbour of `u` and `w` (and `u ≠ w`). -/
def isPerpSharedNeighbour {V : Type*} [DecidableEq V]
    (carrier : List V) (H : List (Hyperedge V)) (u v w : V) : Bool :=
  (u != w) && adjB H u v && adjB H v w
    && (commonNeighbours carrier H u w == 1)

/-- Small-step distance: `0` if equal, `1` if adjacent, `2` otherwise.
Sufficient for distinguishing `adjacent / non-adjacent / equal` cases
in small concrete graphs without a full BFS. -/
def smallStepDist {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u v : V) : ℕ :=
  if u = v then 0
  else if adjB H u v then 1
  else 2

/-- **Pythagorean-hop perpendicularity at `v`** (Schoenberg-style):
the small-step squared equation `d(u,v)² + d(v,w)² = d(u,w)²` holds.
Distinct from `adjacencyWedge` (which is purely local) and from
`sharedNeighbour` (which is combinatorial). For the 4-cycle and a
3-path the verdicts differ across methods — the F1 moduli becomes
three-way at the perpendicular layer. -/
def isPerpPythagoreanHop {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u v w : V) : Bool :=
  let d_uv := smallStepDist H u v
  let d_vw := smallStepDist H v w
  let d_uw := smallStepDist H u w
  decide (d_uv * d_uv + d_vw * d_vw = d_uw * d_uw)

/-- **Method-parameterised perpendicularity predicate.** The carrier
list is the finite vertex set over which the shared-neighbour count is
taken — the other methods ignore it. -/
def isPerpendicular {V : Type*} [DecidableEq V]
    (method : PerpMethod) (carrier : List V) (H : List (Hyperedge V))
    (u v w : V) : Bool :=
  match method with
  | .adjacencyWedge   => isPerpAdjacencyWedge H u v w
  | .sharedNeighbour  => isPerpSharedNeighbour carrier H u v w
  | .pythagoreanHop   => isPerpPythagoreanHop H u v w

/-! ## Demonstration: the two methods disagree on the 4-cycle

In `cycle4HG = [{0,1}, {1,2}, {2,3}, {3,0}]` over `Fin 4`, look at the
triple `(0, 1, 2)`:
  * Adjacency-wedge: `1—0`? no, `0—1` yes. `1—2` yes. `0—2`? no. So
    `0—1—2` is a wedge with right angle at `1`. AFFIRMED.
  * Shared-neighbour at `1` for the pair `(0, 2)`: count common
    neighbours of `0` and `2`. Vertex `1` is one. Vertex `3` is the
    other (`3—0` and `3—2` via edges `{3,0}` and `{2,3}`). So the
    count is `2`, not `1`. REJECTED.

The methods disagree — the F1 moduli at the perpendicular layer,
certified. -/

/-- A directed 2-edge on `Fin 4`. -/
def cycle4Edge (a b : Fin 4) : Hyperedge (Fin 4) :=
  ⟨[a, b], List.cons_ne_nil _ _⟩

/-- The 4-cycle as a `List (Hyperedge (Fin 4))`. -/
def cycle4HG : List (Hyperedge (Fin 4)) :=
  [cycle4Edge 0 1, cycle4Edge 1 2, cycle4Edge 2 3, cycle4Edge 3 0]

/-- The carrier for the shared-neighbour count: all of `Fin 4`. -/
def cycle4Carrier : List (Fin 4) := [0, 1, 2, 3]

/-- The adjacency-wedge method says yes for `(0, 1, 2)`. -/
example :
    isPerpendicular .adjacencyWedge cycle4Carrier cycle4HG 0 1 2 = true := by
  native_decide

/-- The shared-neighbour method says no for `(0, 1, 2)` — `0` and `2`
have two common neighbours (`1` and `3`), not one. -/
example :
    isPerpendicular .sharedNeighbour cycle4Carrier cycle4HG 0 1 2 = false := by
  native_decide

/-- The two methods disagree on `(0, 1, 2)` in the 4-cycle. -/
example :
    isPerpendicular .adjacencyWedge cycle4Carrier cycle4HG 0 1 2 ≠
    isPerpendicular .sharedNeighbour cycle4Carrier cycle4HG 0 1 2 := by
  native_decide

/-- **The F1 moduli theorem at the perpendicular layer**: there is a
graph, a carrier, a triple, and two distinct `PerpMethod`s on which the
perpendicularity verdicts differ. The hypergraph does not determine a
*canonical* notion of perpendicularity — only a moduli of method
choices, exactly as F1 predicts at the metric level and PHAJEK's paclet
treats as a feature via the `Method` argument. -/
theorem perpendicular_methods_disagree :
    ∃ (carrier : List (Fin 4)) (H : List (Hyperedge (Fin 4)))
      (u v w : Fin 4) (m₁ m₂ : PerpMethod),
      isPerpendicular m₁ carrier H u v w ≠
      isPerpendicular m₂ carrier H u v w :=
  ⟨cycle4Carrier, cycle4HG, 0, 1, 2,
    .adjacencyWedge, .sharedNeighbour, by native_decide⟩

/-! ### Three-way moduli: every pair of distinct methods disagrees

With `pythagoreanHop` added, the moduli is no longer just two-way —
each pair of the three methods disagrees on some triple. -/

/-- A 3-path on `Fin 3`: edges `[0,1], [1,2]`. -/
def path3HG : List (Hyperedge (Fin 3)) :=
  [⟨[0, 1], by decide⟩, ⟨[1, 2], by decide⟩]

/-- Carrier for the 3-path. -/
def path3Carrier : List (Fin 3) := [0, 1, 2]

/-- On the 4-cycle, the Pythagorean-hop method rejects `(0, 1, 2)`
(`1² + 1² = 2 ≠ 2² = 4`), so it disagrees with `adjacencyWedge`
(which affirms). -/
example :
    isPerpendicular .adjacencyWedge cycle4Carrier cycle4HG 0 1 2 ≠
    isPerpendicular .pythagoreanHop cycle4Carrier cycle4HG 0 1 2 := by
  native_decide

/-- On the 3-path `0—1—2`, `sharedNeighbour` affirms (`1` is the
unique common neighbour of `0` and `2`), but `pythagoreanHop` rejects
(`1² + 1² = 2 ≠ 2² = 4`). -/
example :
    isPerpendicular .sharedNeighbour path3Carrier path3HG 0 1 2 ≠
    isPerpendicular .pythagoreanHop path3Carrier path3HG 0 1 2 := by
  native_decide

/-- **Every pair of distinct `PerpMethod`s disagrees on some graph and
triple.** The three-way moduli theorem: there is no canonical
perpendicularity, and the three methods are pairwise distinguishable
as invariants. -/
theorem perp_methods_pairwise_disagree :
    -- adjacencyWedge vs sharedNeighbour
    (∃ (carrier : List (Fin 4)) (H : List (Hyperedge (Fin 4)))
       (u v w : Fin 4),
       isPerpendicular .adjacencyWedge carrier H u v w ≠
       isPerpendicular .sharedNeighbour carrier H u v w)
  ∧ -- adjacencyWedge vs pythagoreanHop
    (∃ (carrier : List (Fin 4)) (H : List (Hyperedge (Fin 4)))
       (u v w : Fin 4),
       isPerpendicular .adjacencyWedge carrier H u v w ≠
       isPerpendicular .pythagoreanHop carrier H u v w)
  ∧ -- sharedNeighbour vs pythagoreanHop
    (∃ (carrier : List (Fin 3)) (H : List (Hyperedge (Fin 3)))
       (u v w : Fin 3),
       isPerpendicular .sharedNeighbour carrier H u v w ≠
       isPerpendicular .pythagoreanHop carrier H u v w) :=
  ⟨⟨cycle4Carrier, cycle4HG, 0, 1, 2, by native_decide⟩,
   ⟨cycle4Carrier, cycle4HG, 0, 1, 2, by native_decide⟩,
   ⟨path3Carrier, path3HG, 0, 1, 2, by native_decide⟩⟩

end PerpendicularModuli
end InfraFormalization
