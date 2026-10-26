/-
Examples for the operators of `KnillCore.lean`.

This module evaluates `simplexWeight`, `eulerCharacteristic`, `fermiCharacteristic`,
`complexClosure`, `connectionEntry`, `superTrace`, the Wu characteristics, `incidence`, `dirac`,
`dSquared` and `hodgeOnG` on small complexes on `Fin 3`. The proofs are by `decide` or
`native_decide`. The complexes are:
  * `vertex = {{0}}`, with χ = 1;
  * `edge = {{0}, {1}, {0, 1}}`, with χ = 1;
  * `triangle = complexClosure {{0, 1, 2}}`, with 3 vertices, 3 edges, 1 triangle and χ = 1;
  * `triangleBoundary = {{0}, {1}, {2}, {0,1}, {1,2}, {0,2}}`, with χ = 0.
-/

import InfraFormalization.KnillCore

namespace InfraFormalization
namespace Knill
namespace Examples

/-! ## Test complexes -/

/-- Single vertex complex `{{0}}` on `Fin 3`. -/
def vertex : SimplexSet (Fin 3) := {{0}}

/-- Closed edge complex `{{0}, {1}, {0, 1}}` — two vertices and
their connecting edge, all closed. -/
def edge : SimplexSet (Fin 3) :=
  {{0}, {1}, {0, 1}}

/-- Triangle as the closure of the facet `{0, 1, 2}` — 3 vertices,
3 edges, 1 triangle. -/
def triangle : SimplexSet (Fin 3) :=
  complexClosure {{0, 1, 2}}

/-- Boundary of a triangle — 3 vertices, 3 edges, no 2-simplex
(homotopically a circle `S¹`). -/
def triangleBoundary : SimplexSet (Fin 3) :=
  {{0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}}

/-! ## Euler characteristic computations -/

/-- `χ(vertex) = 1`: a single vertex has weight `(-1)^(1+1) = 1`. -/
example : eulerCharacteristic vertex = 1 := by decide

/-- `χ(edge) = 1`: two vertices contribute `+2`, one edge
contributes `-1`, total `1`. The closed edge complex is contractible. -/
example : eulerCharacteristic edge = 1 := by decide

/-- `χ(triangle) = 1`: three vertices `+3`, three edges `-3`, one
2-simplex `+1`. The full triangle complex (closure of a 2-facet) is
contractible. -/
example : eulerCharacteristic triangle = 1 := by decide

/-- `χ(triangleBoundary) = 0`: three vertices `+3`, three edges
`-3`, no 2-simplex. The triangle's boundary is `S¹` topologically;
its Euler characteristic vanishes. -/
example : eulerCharacteristic triangleBoundary = 0 := by decide

/-! ## Fermi characteristic -/

/-- `Fermi(vertex) = 1`: one vertex with weight `1`. -/
example : fermiCharacteristic vertex = 1 := by decide

/-- `Fermi(edge) = -1`: two vertices `(+1)·(+1) = 1`, times one
edge `(-1)` = `-1`. -/
example : fermiCharacteristic edge = -1 := by decide

/-! ## Simplex weight -/

example : simplexWeight ({0} : Simplex (Fin 3)) = 1 := by decide
example : simplexWeight ({0, 1} : Simplex (Fin 3)) = -1 := by decide
example : simplexWeight ({0, 1, 2} : Simplex (Fin 3)) = 1 := by decide

/-! ## Star, core, unit sphere -/

/-- `simplexStar triangle {0}` = simplices of triangle containing
`{0}`: vertex `{0}`, edges `{0,1}`, `{0,2}`, triangle `{0,1,2}`. -/
example : simplexStar triangle {0} =
    ({{0}, {0, 1}, {0, 2}, {0, 1, 2}} : SimplexSet (Fin 3)) := by
  decide

/-- `simplexCore triangle {0, 1, 2}` = simplices of triangle that
are subsets of `{0,1,2}` = all of `triangle`. -/
example : simplexCore triangle {0, 1, 2} = triangle := by decide

/-! ## Connection-matrix entries -/

/-- `L(vertex {0}, vertex {0})` on the triangle equals
`χ(simplexCore triangle {0}) = χ({{0}}) = 1` (just the vertex `{0}`
itself). -/
example : connectionEntry triangle {0} {0} = 1 := by decide

/-- `L({0,1}, {0,2})` on the triangle = `χ(common subsimplices)`.
The simplices of triangle that are subsets of both `{0,1}` and
`{0,2}` are exactly `{{0}}`, so `L = χ({{0}}) = 1`. -/
example : connectionEntry triangle {0, 1} {0, 2} = 1 := by decide

/-- `L({0,1,2}, {0,1,2})` on the triangle = `χ(triangle) = 1`
(the whole complex is the core of the top simplex). -/
example : connectionEntry triangle {0, 1, 2} {0, 1, 2} = 1 := by decide

/-! ## Super-trace -/

/-- The super-trace of the constant 1 on `edge` equals `χ(edge)`. -/
example : superTrace edge (fun _ _ => 1) = eulerCharacteristic edge := by
  rw [superTrace_diag_one]

/-! ## Wu characteristic -/

/-- `wuCharacteristic₁ triangle = χ(triangle) = 1`. -/
example : wuCharacteristic₁ triangle = 1 := by decide

/-- `wuCharacteristic₂ vertex = 1` — single simplex contributes `ω({0})² = 1`. -/
example : wuCharacteristic₂ vertex = 1 := by decide

/-- `wuCharacteristic₂ edge = -1` — matches `fermiCharacteristic edge` here. -/
example : wuCharacteristic₂ edge = -1 := by decide

/-- `wuCharacteristic₂ triangle = 1 = χ(triangle)` — Wu m=2 agrees with
Euler on the contractible 2-simplex closure. -/
example : wuCharacteristic₂ triangle = 1 := by decide

/-- `wuCharacteristic₂ triangleBoundary = 0 = χ(S¹)` — Wu m=2 agrees with
Euler on the circle. -/
example : wuCharacteristic₂ triangleBoundary = 0 := by decide

/-! ## Signed incidence d

The examples use the order of `Fin 3`. -/

/-- `d({0, 1}, {0}) = (-1)^position-of-1-in-{0,1}`. After
removing `1`, position of `1` in sorted `{0, 1}` is `1`, so
`d = (-1)^1 = -1`. -/
example : incidence ({0, 1} : Simplex (Fin 3)) {0} = -1 := by native_decide

/-- `d({0, 1}, {1}) = (-1)^position-of-0-in-{0,1}`. After
removing `0`, position of `0` in sorted `{0, 1}` is `0`, so
`d = (-1)^0 = 1`. -/
example : incidence ({0, 1} : Simplex (Fin 3)) {1} = 1 := by native_decide

/-- `d({0,1,2}, {0,1}) = (-1)^position-of-2 = (-1)^2 = 1`. -/
example : incidence ({0, 1, 2} : Simplex (Fin 3)) {0, 1} = 1 := by native_decide

/-- `d({0,1,2}, {0,2}) = (-1)^position-of-1 = (-1)^1 = -1`. -/
example : incidence ({0, 1, 2} : Simplex (Fin 3)) {0, 2} = -1 := by native_decide

/-- `d({0,1,2}, {1,2}) = (-1)^position-of-0 = (-1)^0 = 1`. -/
example : incidence ({0, 1, 2} : Simplex (Fin 3)) {1, 2} = 1 := by native_decide

/-- Off-support: `d({0,1}, {2}) = 0` (`{2}` is not a face of
`{0, 1}`). -/
example : incidence ({0, 1} : Simplex (Fin 3)) {2} = 0 := by native_decide

/-! ## Dirac matrix D = d + d* -/

/-- `D({0}, {0,1}) = d({0}, {0,1}) + d({0,1}, {0})
                    = 0 + (-1) = -1`. -/
example : dirac ({0} : Simplex (Fin 3)) {0, 1} = -1 := by native_decide

/-- Self-adjointness witness: `D({0,1}, {0}) = D({0}, {0,1})`. -/
example : dirac ({0, 1} : Simplex (Fin 3)) {0} =
          dirac ({0} : Simplex (Fin 3)) {0, 1} := by
  rw [dirac_symm]

/-! ## d² = 0 — concrete sign-cancellation witnesses

Concrete instances of `d ∘ d = 0` on the triangle, verifying the
sign cancellation. -/

/-- `(d²)({0,1,2}, {0}) = 0`: removing one of the two extra
vertices first then the other gives cancelling signs. The two
non-zero summands are `d({0,1,2}, {0,1}) · d({0,1}, {0}) +
d({0,1,2}, {0,2}) · d({0,2}, {0}) = 1 · (-1) + (-1) · (-1) = 0`. -/
example : dSquared ({0, 1, 2} : Simplex (Fin 3)) {0} = 0 := by native_decide

/-- `(d²)({0,1,2}, {1}) = 0` by the same mechanism. -/
example : dSquared ({0, 1, 2} : Simplex (Fin 3)) {1} = 0 := by native_decide

/-- `(d²)({0,1,2}, {2}) = 0`. -/
example : dSquared ({0, 1, 2} : Simplex (Fin 3)) {2} = 0 := by native_decide

/-! ## d ∘ d = 0 in general

`KnillCore.dSquared_eq_zero` applied to an arbitrary pair of simplices on `Fin 3`. -/

example (x z : Simplex (Fin 3)) : dSquared x z = 0 :=
  dSquared_eq_zero x z

/-! ## Hodge matrix on the triangle

Entries of `H = D²` on the triangle complex, and non-negativity of the diagonal. -/

/-- `H({0}, {0}) = ∑_z d({0},z)² = d({0},{0,1})² + d({0},{0,2})²
= 1 + 1 = 2` — degree of `{0}` in the triangle's edge graph. -/
example : hodgeOnG triangle ({0} : Simplex (Fin 3)) {0} = 2 := by native_decide

/-- `H({0,1}, {0,1}) = 3` on the triangle: the nonzero terms are those for `z = {0}`, `{1}` and
`{0,1,2}`. -/
example : hodgeOnG triangle ({0, 1} : Simplex (Fin 3)) {0, 1} = 3 := by
  native_decide

/-- `H({0,1,2}, {0,1,2}) = 3`: the diagonal entry on the top
2-simplex (incidences from its three boundary edges, each squared). -/
example : hodgeOnG triangle ({0, 1, 2} : Simplex (Fin 3)) {0, 1, 2} = 3 := by
  native_decide

/-- General Hodge diagonal non-negativity: `H(x, x) ≥ 0` for any
simplex on `Fin 3`. -/
example (G : SimplexSet (Fin 3)) (x : Simplex (Fin 3)) :
    0 ≤ hodgeOnG G x x :=
  hodgeOnG_diag_nonneg G x

/-! ## Euler–Poincaré formula on the triangle

`χ(G) = ∑_k (-1)^k · |k-skeleton|`: the triangle has 3 vertices, 3 edges and 1 triangle, and
`3 - 3 + 1 = 1`. -/

/-- `kSkeleton triangle 0` = the three vertex simplices. -/
example : (kSkeleton triangle 0).card = 3 := by decide

/-- `kSkeleton triangle 1` = the three edges. -/
example : (kSkeleton triangle 1).card = 3 := by decide

/-- `kSkeleton triangle 2` = the top 2-simplex. -/
example : (kSkeleton triangle 2).card = 1 := by decide

/-- Euler-Poincaré on triangle: `χ = 3 - 3 + 1 = 1` matches the
alternating-sum-over-skeletons formula. -/
example : eulerCharacteristic triangle =
    (Finset.range 3).sum (fun k => (-1 : ℤ)^k * ((kSkeleton triangle k).card : ℤ)) :=
  eulerCharacteristic_eq_alt_sum_kSkeleton triangle (by decide) 3 (by decide)

end Examples
end Knill
end InfraFormalization
