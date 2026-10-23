/-
Knill value per seed edge for two rules at depth 4.

The quantity is `knillEulerScaled (causalDAGOfFireAll sys seed 4)`
divided by the number of edges of `seed`, with `/` the integer
division on `Int`. The evolution is `fireAllStep`, which applies every
match of every rule found in the state, including matches that share
edges. It is not a Wolfram model update when matches overlap.

Values (PROVED-WITH-NATIVE-DECIDE):

  * `doubleCycleSys_5`: quotient -6 on `seedEdge12`, `seedPath123`,
    `seedTriangle` and `bbhInitial`.
  * `bidirectedEdgeSys`: quotient 126 on `seedEdge12` and
    `seedTriangle`.

The module also defines the Prop `CurvatureDensityWellDefined`, which
states that the Knill value is the edge count times a constant for
every nonempty seed. The module proves no instance of it and states no
limit. It defines no manifold, metric or stress-energy tensor.
-/

import InfraFormalization.UniversalAdditivity

namespace InfraFormalization
namespace CurvatureDensityLimit

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open BBHInitialData
open UniversalAdditivity

/-! ## doubleCycleSys_5: quotient -6 -/

/-- For `doubleCycleSys_5` at depth 4 on `seedEdge12`, the integer
quotient is -6. -/
theorem density_doubleCycle_5_edge12 :
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = -6 := by
  native_decide

theorem density_doubleCycle_5_path :
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedPath123 4) /
      (Int.ofNat seedPath123.length) = -6 := by
  native_decide

theorem density_doubleCycle_5_triangle :
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = -6 := by
  native_decide

theorem density_doubleCycle_5_bbh :
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 bbhInitial 4) /
      (Int.ofNat bbhInitial.length) = -6 := by
  native_decide

/-- `density_doubleCycle_5_universal`: for `doubleCycleSys_5` at depth
4, the integer quotient is -6 for `seedEdge12`, `seedPath123`,
`seedTriangle` and `bbhInitial`. The statement is a conjunction over
these four seeds. -/
theorem density_doubleCycle_5_universal :
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = -6 ∧
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedPath123 4) /
      (Int.ofNat seedPath123.length) = -6 ∧
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = -6 ∧
    knillEulerScaled (causalDAGOfFireAll doubleCycleSys_5 bbhInitial 4) /
      (Int.ofNat bbhInitial.length) = -6 :=
  ⟨density_doubleCycle_5_edge12,
   density_doubleCycle_5_path,
   density_doubleCycle_5_triangle,
   density_doubleCycle_5_bbh⟩

/-! ## bidirectedEdgeSys: quotient 126 -/

theorem density_bidirected_edge12 :
    knillEulerScaled (causalDAGOfFireAll bidirectedEdgeSys seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = 126 := by
  native_decide

theorem density_bidirected_triangle :
    knillEulerScaled (causalDAGOfFireAll bidirectedEdgeSys seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = 126 := by
  native_decide

/-- `density_bidirected_universal`: for `bidirectedEdgeSys` at depth 4,
the integer quotient is 126 for `seedEdge12` and `seedTriangle`. The
statement is a conjunction over these two seeds. -/
theorem density_bidirected_universal :
    knillEulerScaled (causalDAGOfFireAll bidirectedEdgeSys seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = 126 ∧
    knillEulerScaled (causalDAGOfFireAll bidirectedEdgeSys seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = 126 :=
  ⟨density_bidirected_edge12, density_bidirected_triangle⟩

/-! ## The per-edge linearity Prop -/

/-- `CurvatureDensityWellDefined sys d c`: the scaled Knill value of
`causalDAGOfFireAll sys seedEdge12 d` is `c`, and for every nonempty
seed the value equals `seed.length * c`. -/
def CurvatureDensityWellDefined (sys : ExecSystem) (d : Nat) (c : Int) : Prop :=
  knillEulerScaled (causalDAGOfFireAll sys seedEdge12 d) = c ∧
  ∀ seed : ExecHG ℕ, seed.length ≠ 0 →
    knillEulerScaled (causalDAGOfFireAll sys seed d) =
      (Int.ofNat seed.length) * c

/-! ## Summary

  * `density_doubleCycle_5_universal`: the quotient is -6 for four
    seeds with `doubleCycleSys_5` at depth 4.
  * `density_bidirected_universal`: the quotient is 126 for two seeds
    with `bidirectedEdgeSys` at depth 4.
  * `CurvatureDensityWellDefined`: a Prop that quantifies over every
    nonempty seed. No theorem in the library proves it for any system
    and depth. It is OPEN for every instance.
-/

end CurvatureDensityLimit
end InfraFormalization
