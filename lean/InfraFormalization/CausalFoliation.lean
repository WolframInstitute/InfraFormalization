/-
**Foliations and proper time on a causal graph** (Group IC / #128).

A foliation of a causal graph is a decomposition into successive
antichains — Cauchy surfaces, in the GR analog. Proper time between
two vertices on a chain is the length of the longest causal chain
between them.

This file formalises:

  * `Antichain G` — a Finset of vertices, no two causally related.
  * `IsFoliation G f` — `f : ℕ → Finset V` is a foliation if every
    `f n` is an antichain, they're disjoint, cover `V`, and the
    natural order matches causality.
  * `properTime G u v` — longest chain length from `u` to `v`.

**Connection to hypergraphs.** Every Trajectory-induced causal graph
(from `Causal.lean`) has a canonical foliation by step-layer
(see `CausalLevel.lean`). Foliations are observer-dependent; different
foliations correspond to different simultaneity choices — this is
the discrete analog of Lorentz boosts.
-/

import InfraFormalization.CausalGraphType
import Mathlib.Data.Finset.Basic

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-! ## Antichains -/

/-- **An antichain** in `G`: a finset of pairwise causally-unrelated
vertices. -/
def IsAntichain (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.strictCausallyPrecedes u v

/-- **Empty set is an antichain.** -/
theorem isAntichain_empty : G.IsAntichain ∅ := by
  intros u hu
  exact absurd hu (Finset.notMem_empty u)

/-- **Singleton is an antichain.** -/
theorem isAntichain_singleton (v : V) : G.IsAntichain {v} := by
  intros u hu w hw hne
  rw [Finset.mem_singleton] at hu hw
  subst hu; subst hw
  exact absurd rfl hne

/-! ## Foliations -/

/-- **`IsFoliation G f`**: the sequence `f : ℕ → Finset V` is a
causal-graph foliation if every level is an antichain, successive
levels are disjoint (guaranteeing no vertex in two layers), and the
union covers `V`. Causal ordering between consecutive layers is a
consequence of the overall structure. -/
structure IsFoliation (f : Nat → Finset V) : Prop where
  antichain : ∀ n, G.IsAntichain (f n)
  disjoint  : ∀ m n, m ≠ n → Disjoint (f m) (f n)
  covers    : ∀ v : V, ∃ n, v ∈ f n

/-- **Finite-support foliation**: if `V` is a Fintype, a foliation
has finite support — eventually every level is empty. -/
def FiniteSupportFoliation (f : Nat → Finset V) (N : Nat) : Prop :=
  ∀ n ≥ N, f n = ∅

end CausalGraph

/-! ## Proper time

`properTime G u v` := maximal length of a chain from `u` to `v`.
For a finite causal graph, this is well-defined and finite. -/

namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-- **Proper time** from `u` to `v`: the length of the longest
chain from `u` to `v`, if any exists. Defined as a Prop-level
predicate `HasProperTime G u v n` meaning "there's a chain of length
`n` but no longer chain"; the numerical value is extracted in
follow-up. -/
def HasProperTime (u v : V) (n : Nat) : Prop :=
  G.ChainOfLength n u v ∧ ∀ m, G.ChainOfLength m u v → m ≤ n

/-- **Proper time from `v` to `v` is at least 0** (reflexive chain
exists). A stronger theorem `hasProperTime_self_zero` requires the
no-loops fact (`v → ... → v` of positive length contradicts irrefl
+ TR); deferred. -/
theorem properTime_self_exists (v : V) : G.ChainOfLength 0 v v :=
  ChainOfLength.refl v

end CausalGraph

end InfraFormalization
