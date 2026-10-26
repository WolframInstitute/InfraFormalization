/-
Several definitions of perpendicularity on a graph.

P. Hajek's `InfraPerpendicularQ` in the `SyntheticInfrageometry` paclet
(`resources/SyntheticInfrageometry/Kernel/InfraEquality.wl`) takes a `Method` argument that selects
one of several inequivalent definitions of perpendicularity. This module defines three decidable
methods (`adjacencyWedge`, `sharedNeighbour`, `pythagoreanHop`) for a triple `(u, v, w)` with vertex
`v` at the corner, and proves by `decide` that each pair of methods gives different values on some
triple in the 4-cycle or the path on three vertices. The Schoenberg, centroid and four-corner-wedge
methods of the paclet are not defined here.
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace InfraFormalization
namespace PerpendicularModuli

/-- The three perpendicularity methods defined in this module. -/
inductive PerpMethod
  | adjacencyWedge    -- v adjacent to both u and w, but u, w not adjacent
  | sharedNeighbour   -- u, w have v as a unique common neighbour (and u ≠ w)
  | pythagoreanHop    -- "Schoenberg-style": hop count d(u,v)² + d(v,w)² = d(u,w)²
deriving DecidableEq, Repr

/-- `u ≠ w` and some edge of `H` contains both. -/
def adjB {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u w : V) : Bool :=
  (u != w) && H.any (fun e => e.verts.contains u && e.verts.contains w)

/-- Common-neighbour count of `u` and `w` over a finite carrier
`carrier`, excluding `u` and `w` themselves. -/
def commonNeighbours {V : Type*} [DecidableEq V]
    (carrier : List V) (H : List (Hyperedge V)) (u w : V) : ℕ :=
  (carrier.filter (fun v => v != u && v != w && adjB H u v && adjB H v w)).length

/-- `v` is adjacent to `u` and to `w`, and `u` is not adjacent to `w`. -/
def isPerpAdjacencyWedge {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u v w : V) : Bool :=
  adjB H u v && adjB H v w && !adjB H u w

/-- `u ≠ w` and `v` is the only common neighbour of `u` and `w` in `carrier`. -/
def isPerpSharedNeighbour {V : Type*} [DecidableEq V]
    (carrier : List V) (H : List (Hyperedge V)) (u v w : V) : Bool :=
  (u != w) && adjB H u v && adjB H v w
    && (commonNeighbours carrier H u w == 1)

/-- 0 if `u = v`, 1 if `u` and `v` are adjacent, and 2 otherwise. -/
def smallStepDist {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u v : V) : ℕ :=
  if u = v then 0
  else if adjB H u v then 1
  else 2

/-- `d(u,v)² + d(v,w)² = d(u,w)²` with `d = smallStepDist H`. -/
def isPerpPythagoreanHop {V : Type*} [DecidableEq V]
    (H : List (Hyperedge V)) (u v w : V) : Bool :=
  let d_uv := smallStepDist H u v
  let d_vw := smallStepDist H v w
  let d_uw := smallStepDist H u w
  decide (d_uv * d_uv + d_vw * d_vw = d_uw * d_uw)

/-- Perpendicularity of `(u, v, w)` by the given method. Only `sharedNeighbour` uses `carrier`. -/
def isPerpendicular {V : Type*} [DecidableEq V]
    (method : PerpMethod) (carrier : List V) (H : List (Hyperedge V))
    (u v w : V) : Bool :=
  match method with
  | .adjacencyWedge   => isPerpAdjacencyWedge H u v w
  | .sharedNeighbour  => isPerpSharedNeighbour carrier H u v w
  | .pythagoreanHop   => isPerpPythagoreanHop H u v w

/-! ## Two methods on the 4-cycle

In `cycle4HG = [{0,1}, {1,2}, {2,3}, {3,0}]` and the triple `(0, 1, 2)`, `adjacencyWedge` holds:
`1` is adjacent to `0` and `2`, and `0` is not adjacent to `2`. `sharedNeighbour` fails: `0` and `2`
have the two common neighbours `1` and `3`. -/

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

/-- There exist a carrier, a graph on `Fin 4`, a triple and two methods for which `isPerpendicular`
takes
different values. -/
theorem perpendicular_methods_disagree :
    ∃ (carrier : List (Fin 4)) (H : List (Hyperedge (Fin 4)))
      (u v w : Fin 4) (m₁ m₂ : PerpMethod),
      isPerpendicular m₁ carrier H u v w ≠
      isPerpendicular m₂ carrier H u v w :=
  ⟨cycle4Carrier, cycle4HG, 0, 1, 2,
    .adjacencyWedge, .sharedNeighbour, by native_decide⟩

/-! ### Each pair of the three methods -/

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

/-- For each of the three pairs of methods, there exist a graph and a triple on which the two
methods
give different values. -/
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
