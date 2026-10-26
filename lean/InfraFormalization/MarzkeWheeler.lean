/-
Marzke–Wheeler clocks on a causal graph.

Following C. Zapata-Carratalá, an observer's proper time in a causal graph can be measured by
counting round trips of signals to a reference event. This module defines a tick `v → m → v'` as two
causal edges, an `n`-tick clock as a chain of `n` ticks, and proves that the end of a clock is
causally preceded by its start.
-/

import InfraFormalization.CausalGraphType

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `v → m` and `m → v'` are causal edges of `G`. -/
def IsMWTick (G : CausalGraph V) (v m v' : V) : Prop :=
  G.causalEdge v m ∧ G.causalEdge m v'

/-- `MWClock G n v v'`: `v'` is reached from `v` by `n` successive ticks. -/
inductive MWClock (G : CausalGraph V) : Nat → V → V → Prop
  | refl (v : V) : MWClock G 0 v v
  | tick {n : Nat} {v v' v'' : V} {m : V}
      (hprev : MWClock G n v v')
      (htick : IsMWTick G v' m v'') :
      MWClock G (n + 1) v v''

/-- If `MWClock G n v v'`, then `G.causallyPrecedes v v'`. -/
theorem mwClock_implies_causallyPrecedes (G : CausalGraph V) :
    ∀ {n : Nat} {v v' : V}, MWClock G n v v' → G.causallyPrecedes v v' := by
  intros n v v' h
  induction h with
  | refl _ => exact G.causallyPrecedes_refl _
  | tick _ htick ih =>
    have h1 : G.causallyPrecedes _ _ :=
      G.causalEdge_implies_precedes htick.1
    have h2 : G.causallyPrecedes _ _ :=
      G.causalEdge_implies_precedes htick.2
    exact G.causallyPrecedes_trans ih (G.causallyPrecedes_trans h1 h2)

end CausalGraph
end InfraFormalization
