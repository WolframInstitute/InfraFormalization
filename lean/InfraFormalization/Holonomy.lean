/-
**Parallel transport, holonomy, and Wilson loops** on a fibered graph
(Group IG / #117, #118, #119).

Given a `FiberedGraph V W` and a `Connection F`, horizontal edges
define parallel transport. Iterated along a base path, they give a
partial function from start-fiber to end-fiber. When the base path
is a loop, parallel transport becomes a permutation-like map from
the fiber to itself — the *holonomy*. The *Wilson loop* is the
trace of the holonomy matrix.

**Connection to hypergraphs.** Native. Everything factors through
`FiberedGraph V W`, `Connection F`, `Hypergraph.Adj`, and the
underlying vertex set `V`.

**Status.** Closes IG4, IG5 (stub), IG6 (stub). Full
`HolonomyMatrix` as a `Matrix (Fiber _) (Fiber _) ℝ` and character
theory (Wilson-loop invariants) are follow-ups; here we give the
operational definition + basic lemmas at predicate level. -/

import InfraFormalization.FiberedGraph

namespace InfraFormalization
namespace FiberedGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {F : FiberedGraph V W}

/-! ## Horizontal lift (predicate) -/

/-- **`IsHorizontalLift C v w' v'`**: `v'` is a horizontal lift of
the base step `π v → w'` along connection `C`, i.e., `v'` is in
fiber `w'` and `connectionAdj C v v'`. -/
def IsHorizontalLift (C : Connection F) (v : V) (w' : W) (v' : V) : Prop :=
  F.π v' = w' ∧ connectionAdj C v v'

/-! ## Parallel transport along a base path

A base path is represented as a list of vertices `[w₀, w₁, …, wₙ]`.
Parallel transport from `v₀` (with `π v₀ = w₀`) lifts each step
`wᵢ → wᵢ₊₁`. We represent the result as a predicate: `ParallelTransport
C path v₀ vₙ` means there's a sequence of horizontal lifts along the
whole path. -/

/-- **Recursive definition** of parallel transport: folds the
horizontal lift along the base path. `ParallelTransportList C path v
v'` means `v'` is the total-space endpoint of lifting `path`
horizontally starting from `v`. -/
inductive ParallelTransportList (C : Connection F) :
    List W → V → V → Prop where
  | nil {v : V} : ParallelTransportList C [] v v
  | step {w : W} {path : List W} {v v' v'' : V}
      (hlift : IsHorizontalLift C v w v')
      (hrest : ParallelTransportList C path v' v'') :
      ParallelTransportList C (w :: path) v v''

/-! ## Holonomy and Wilson loops -/

/-- **Holonomy around a loop based at `v`**: parallel transport
along a closed base path returning to `π v` defines a (partial)
map fiber → fiber. `Holonomy C v loop v'` says the loop transport
starting from `v` ends at `v'` (which is also in fiber of `π v`). -/
def Holonomy (C : Connection F) (v : V) (loop : List W) (v' : V) : Prop :=
  F.π v' = F.π v ∧ ParallelTransportList C loop v v'

/-- **Wilson loop** (trace form): count of fiber vertices fixed by
holonomy around the loop based at a vertex in fiber `w`. This is
the combinatorial analog of `trace (HolonomyMatrix)` from the paclet.

Uses `Classical.decPred` for the non-computable case. -/
noncomputable def wilsonLoop (C : Connection F) (w : W) (loop : List W) : Nat :=
  haveI : DecidablePred (fun v : V => Holonomy C v loop v) := Classical.decPred _
  ((F.fiber w).filter (fun v => Holonomy C v loop v)).card

/-- **Flat connection**: holonomy is trivial (every lift returns to
its starting point) for all loops at all basepoints. -/
def IsFlatConnection (C : Connection F) : Prop :=
  ∀ (w : W) (loop : List W) (v : V), v ∈ F.fiber w →
    Holonomy C v loop v

/-! ## Basic lemmas -/

/-- **Trivial transport on empty path**: the parallel transport
along the empty list just sits at `v`. -/
theorem parallelTransportList_nil (C : Connection F) (v : V) :
    ParallelTransportList C [] v v :=
  ParallelTransportList.nil

/-- **Trivial holonomy on empty loop.** -/
theorem holonomy_empty_loop (C : Connection F) (v : V) :
    Holonomy C v [] v :=
  ⟨rfl, ParallelTransportList.nil⟩

/-- **On a flat connection, every fiber vertex is fixed** — the
Wilson-loop count is the fiber size. Stated at the `∀` level to
avoid decidability plumbing. -/
theorem flat_holonomy_all_fixed (C : Connection F)
    (hFlat : IsFlatConnection C) (w : W) (v : V) (hv : v ∈ F.fiber w)
    (loop : List W) :
    Holonomy C v loop v :=
  hFlat w loop v hv

end FiberedGraph
end InfraFormalization
