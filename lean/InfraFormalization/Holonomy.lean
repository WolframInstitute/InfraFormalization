/-
Parallel transport, holonomy and a fixed-point count on a fibered graph.

For a `FiberedGraph V W` and a `Connection F`, this module defines parallel transport along a list of base vertices as an inductive relation built from horizontal lifts. It defines `Holonomy` as transport that ends in the starting fiber, `wilsonLoop` as the number of fiber vertices that the transport returns to themselves. The lemmas cover the empty path.
-/

import InfraFormalization.FiberedGraph

namespace InfraFormalization
namespace FiberedGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {F : FiberedGraph V W}

/-! ## Horizontal lift (predicate) -/

/-- `IsHorizontalLift C v w' v'` holds when `v'` lies in the fiber over `w'` and `connectionAdj C v v'`. -/
def IsHorizontalLift (C : Connection F) (v : V) (w' : W) (v' : V) : Prop :=
  F.π v' = w' ∧ connectionAdj C v v'

/-! ## Parallel transport along a base path

A base path is a list of base vertices `[w₁, …, wₙ]`. Transport from `v₀` lifts each entry in turn. -/

/-- `ParallelTransportList C path v v'` holds when there is a sequence of horizontal lifts, one per entry of `path`, from `v` to `v'`. The empty path relates `v` to itself. -/
inductive ParallelTransportList (C : Connection F) :
    List W → V → V → Prop where
  | nil {v : V} : ParallelTransportList C [] v v
  | step {w : W} {path : List W} {v v' v'' : V}
      (hlift : IsHorizontalLift C v w v')
      (hrest : ParallelTransportList C path v' v'') :
      ParallelTransportList C (w :: path) v v''

/-! ## Holonomy and Wilson loops -/

/-- `Holonomy C v loop v'` holds when `π v' = π v` and `ParallelTransportList C loop v v'`. -/
def Holonomy (C : Connection F) (v : V) (loop : List W) (v' : V) : Prop :=
  F.π v' = F.π v ∧ ParallelTransportList C loop v v'

/-- The number of vertices `v` in the fiber over `w` with `Holonomy C v loop v`. Decidability is supplied by `Classical.decPred`. -/
noncomputable def wilsonLoop (C : Connection F) (w : W) (loop : List W) : Nat :=
  haveI : DecidablePred (fun v : V => Holonomy C v loop v) := Classical.decPred _
  ((F.fiber w).filter (fun v => Holonomy C v loop v)).card

/-! ## Basic lemmas -/

/-- `ParallelTransportList C [] v v`. -/
theorem parallelTransportList_nil (C : Connection F) (v : V) :
    ParallelTransportList C [] v v :=
  ParallelTransportList.nil

/-- `Holonomy C v [] v`. -/
theorem holonomy_empty_loop (C : Connection F) (v : V) :
    Holonomy C v [] v :=
  ⟨rfl, ParallelTransportList.nil⟩

end FiberedGraph
end InfraFormalization
