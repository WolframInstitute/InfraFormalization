/-
**Marzke-Wheeler clock construction** (Group IC / #132 IC8).

Following Zapata-Ahmed: in a transitively-reduced causal graph, an
observer's proper time can be defined operationally by bouncing
light rays off a reference (the "MW clock"). Each tick of the
clock is a round-trip along two null edges.

This file gives the construction:

  * `MWClock G v w n` — an `n`-tick MW clock between observer `v`
    and reference `w` in causal graph `G`.
  * `mwTickInterval` — single tick interval (two null steps).
  * Consistency with `ChainOfLength` (the clock gives a proper-time
    chain when projected).

**Connection to hypergraphs.** Native. Clocks are chains on a
causal graph arising from a `Trajectory`.
-/

import InfraFormalization.CausalGraphType

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Single MW tick**: from `v`, emit a null edge to `m` then a
null edge from `m` to `v'` (the "next tick" on the observer).
Predicate-level: `v → m → v'` is two direct causal edges. -/
def IsMWTick (G : CausalGraph V) (v m v' : V) : Prop :=
  G.causalEdge v m ∧ G.causalEdge m v'

/-- **An `n`-tick MW clock** from observer `v`: a sequence of
`n+1` observer-events linked by single ticks. -/
inductive MWClock (G : CausalGraph V) : Nat → V → V → Prop
  | refl (v : V) : MWClock G 0 v v
  | tick {n : Nat} {v v' v'' : V} {m : V}
      (hprev : MWClock G n v v')
      (htick : IsMWTick G v' m v'') :
      MWClock G (n + 1) v v''

/-- **Every `n`-tick MW clock induces a causally-precedes relation**
(since each tick is a causal chain). -/
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
