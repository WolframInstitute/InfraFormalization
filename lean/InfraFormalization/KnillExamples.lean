/-
**Knill examples** — sanity checks for the `KnillCore.lean` operators.

Worked computations on small simplicial complexes verifying that the
primitives (`simplexWeight`, `eulerCharacteristic`, `complexClosure`,
`connectionEntry`, `superTrace`, `incidence`, `dirac`) behave as
expected on concrete data. Every proof is by `decide` or kernel
reduction — these are concrete certificates, not theorems.

Test complexes used:
  * `vertex` = `{{0}}` — single vertex; χ = 1.
  * `edge` = `{{0}, {1}, {0, 1}}` — closed edge complex; χ = 1.
  * `triangle` = `complexClosure {{0, 1, 2}}` — full 2-simplex closure;
    has 3 vertices, 3 edges, 1 triangle; χ = 3 - 3 + 1 = 1.
  * `triangleBoundary` = `{{0}, {1}, {2}, {0,1}, {1,2}, {0,2}}` —
    boundary of a triangle (no 2-simplex); χ = 3 - 3 + 0 = 0 (= S¹).
-/

import InfraFormalization.KnillCore

namespace InfraFormalization
namespace Knill
namespace Examples

/-! ## Test complexes -/

/-- **Single vertex** complex `{{0}}` on `Fin 3`. -/
def vertex : SimplexSet (Fin 3) := {{0}}

/-- **Closed edge complex** `{{0}, {1}, {0, 1}}` — two vertices and
their connecting edge, all closed. -/
def edge : SimplexSet (Fin 3) :=
  {{0}, {1}, {0, 1}}

/-- **Triangle** as the closure of the facet `{0, 1, 2}` — 3 vertices,
3 edges, 1 triangle. -/
def triangle : SimplexSet (Fin 3) :=
  complexClosure {{0, 1, 2}}

/-- **Boundary of a triangle** — 3 vertices, 3 edges, no 2-simplex
(homotopically a circle `S¹`). -/
def triangleBoundary : SimplexSet (Fin 3) :=
  {{0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}}

/-! ## Euler characteristic computations -/

/-- **`χ(vertex) = 1`**: a single vertex has weight `(-1)^(1+1) = 1`. -/
example : eulerCharacteristic vertex = 1 := by decide

/-- **`χ(edge) = 1`**: two vertices contribute `+2`, one edge
contributes `-1`, total `1`. The closed edge complex is contractible. -/
example : eulerCharacteristic edge = 1 := by decide

/-- **`χ(triangle) = 1`**: three vertices `+3`, three edges `-3`, one
2-simplex `+1`. The full triangle complex (closure of a 2-facet) is
contractible. -/
example : eulerCharacteristic triangle = 1 := by decide

/-- **`χ(triangleBoundary) = 0`**: three vertices `+3`, three edges
`-3`, no 2-simplex. The triangle's boundary is `S¹` topologically;
its Euler characteristic vanishes. -/
example : eulerCharacteristic triangleBoundary = 0 := by decide

/-! ## Fermi characteristic -/

/-- **`Fermi(vertex) = 1`**: one vertex with weight `1`. -/
example : fermiCharacteristic vertex = 1 := by decide

/-- **`Fermi(edge) = -1`**: two vertices `(+1)·(+1) = 1`, times one
edge `(-1)` = `-1`. -/
example : fermiCharacteristic edge = -1 := by decide

/-! ## Simplex weight -/

example : simplexWeight ({0} : Simplex (Fin 3)) = 1 := by decide
example : simplexWeight ({0, 1} : Simplex (Fin 3)) = -1 := by decide
example : simplexWeight ({0, 1, 2} : Simplex (Fin 3)) = 1 := by decide

/-! ## Star, core, unit sphere -/

/-- **`simplexStar triangle {0}` = simplices of triangle containing
`{0}`**: vertex `{0}`, edges `{0,1}`, `{0,2}`, triangle `{0,1,2}`. -/
example : simplexStar triangle {0} =
    ({{0}, {0, 1}, {0, 2}, {0, 1, 2}} : SimplexSet (Fin 3)) := by
  decide

/-- **`simplexCore triangle {0, 1, 2}` = simplices of triangle that
are subsets of `{0,1,2}`** = all of `triangle`. -/
example : simplexCore triangle {0, 1, 2} = triangle := by decide

/-! ## Connection-matrix entries -/

/-- **`L(vertex {0}, vertex {0})` on the triangle** equals
`χ(simplexCore triangle {0}) = χ({{0}}) = 1` (just the vertex `{0}`
itself). -/
example : connectionEntry triangle {0} {0} = 1 := by decide

/-- **`L({0,1}, {0,2})` on the triangle** = `χ(common subsimplices)`.
The simplices of triangle that are subsets of both `{0,1}` and
`{0,2}` are exactly `{{0}}`, so `L = χ({{0}}) = 1`. -/
example : connectionEntry triangle {0, 1} {0, 2} = 1 := by decide

/-- **`L({0,1,2}, {0,1,2})` on the triangle** = `χ(triangle) = 1`
(the whole complex is the core of the top simplex). -/
example : connectionEntry triangle {0, 1, 2} {0, 1, 2} = 1 := by decide

/-! ## Super-trace -/

/-- **Super-trace of constant `1` on the edge** = Euler characteristic.
Sanity check on `superTrace_diag_one`. -/
example : superTrace edge (fun _ _ => 1) = eulerCharacteristic edge := by
  rw [superTrace_diag_one]

/-! ## Wu characteristic -/

/-- **`wuCharacteristic₁ triangle = χ(triangle) = 1`**. -/
example : wuCharacteristic₁ triangle = 1 := by decide

end Examples
end Knill
end InfraFormalization
