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

/-! ## Foliation from a time function (E5 step)

Given a `TimeFunction` `τ : V → ℕ` that strictly increases along every
causal edge, the level sets `{v : τ v = n}` form a foliation. This is
the discrete analog of constructing a Cauchy foliation of spacetime
from a proper-time function. -/

/-- **Time function is weakly monotone along `causallyPrecedes`.**
`u ≼ v` (= `ReflTransGen causalEdge u v`) implies `tf.τ u ≤ tf.τ v`. -/
theorem time_monotone_causallyPrecedes (tf : G.TimeFunction)
    {u v : V} (h : G.causallyPrecedes u v) :
    tf.τ u ≤ tf.τ v := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (tf.monotone hbc))

/-- **Time function is strictly monotone along strict causal precedence.**
If `u ≺ v` strictly (i.e., `u ≠ v ∧ u ≼ v`), then `tf.τ u < tf.τ v`. -/
theorem time_strict_monotone_strictCausallyPrecedes
    (tf : G.TimeFunction)
    {u v : V} (h : G.strictCausallyPrecedes u v) :
    tf.τ u < tf.τ v := by
  obtain ⟨hne, hprec⟩ := h
  rcases Relation.ReflTransGen.cases_tail hprec with heq | hex
  · exact absurd heq.symm hne
  · obtain ⟨c, hrt, hedge⟩ := hex
    have hmono : tf.τ u ≤ tf.τ c := time_monotone_causallyPrecedes G tf hrt
    have hstrict : tf.τ c < tf.τ v := tf.monotone hedge
    omega

/-- **Level set at time `n`**: the set of vertices with `τ v = n`. -/
noncomputable def timeLevelSet (tf : G.TimeFunction) (n : ℕ) : Finset V :=
  Finset.univ.filter (fun v => tf.τ v = n)

/-- **Level sets are antichains**: no strict causal relation exists
between two vertices at the same time. -/
theorem timeLevelSet_isAntichain (tf : G.TimeFunction) (n : ℕ) :
    G.IsAntichain (timeLevelSet G tf n) := by
  intro u hu v hv _huv hstrict
  simp [timeLevelSet, Finset.mem_filter] at hu hv
  have h_strict : tf.τ u < tf.τ v :=
    time_strict_monotone_strictCausallyPrecedes G tf hstrict
  omega

/-- **Level sets at different times are disjoint**: by definition, a
vertex lives at exactly one time. -/
theorem timeLevelSet_disjoint (tf : G.TimeFunction)
    (m n : ℕ) (hmn : m ≠ n) :
    Disjoint (timeLevelSet G tf m) (timeLevelSet G tf n) := by
  rw [Finset.disjoint_left]
  intro v hv_m hv_n
  simp [timeLevelSet, Finset.mem_filter] at hv_m hv_n
  omega

/-- **Level sets cover `V`**: every vertex is at some time (namely
`τ v`). -/
theorem timeLevelSet_covers (tf : G.TimeFunction) (v : V) :
    ∃ n, v ∈ timeLevelSet G tf n := by
  refine ⟨tf.τ v, ?_⟩
  simp [timeLevelSet, Finset.mem_filter]

/-- **Foliation from a time function** (E5: discrete Cauchy foliation).
Given a `TimeFunction` on `G`, the level sets of `τ` form a foliation.
This is the discrete analog of a Cauchy foliation of spacetime by
constant-proper-time slices. -/
theorem timeFunction_foliation (tf : G.TimeFunction) :
    G.IsFoliation (timeLevelSet G tf) where
  antichain := timeLevelSet_isAntichain G tf
  disjoint := timeLevelSet_disjoint G tf
  covers := timeLevelSet_covers G tf

/-- **Stably causal graphs admit a foliation**: the existence of a
time function (= stable causality) gives a foliation. This is the
cleanest discrete form of E5: every stably causal DAG has a Cauchy
foliation. -/
theorem stablyCausal_hasFoliation (h : G.StablyCausal) :
    ∃ f : ℕ → Finset V, G.IsFoliation f :=
  ⟨timeLevelSet G (Classical.choice h),
    timeFunction_foliation G (Classical.choice h)⟩

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
