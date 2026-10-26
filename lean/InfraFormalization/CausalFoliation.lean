/-
Antichains, foliations and proper time on a causal graph.

The module defines antichains (`IsAntichain`), foliations (`IsFoliation`: a sequence of
pairwise disjoint antichains covering the vertex set) and the predicate `HasProperTime`
(the longest chain from `u` to `v` has length `n`). It proves that the level sets of a
time function form a foliation, so every stably causal graph admits a foliation.
-/

import InfraFormalization.CausalGraphType
import Mathlib.Data.Finset.Basic

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-! ## Antichains -/

/-- A finset is an antichain if no two distinct members are strictly causally related. -/
def IsAntichain (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.strictCausallyPrecedes u v

/-- The empty set is an antichain. -/
theorem isAntichain_empty : G.IsAntichain ∅ := by
  intros u hu
  exact absurd hu (Finset.notMem_empty u)

/-- A singleton is an antichain. -/
theorem isAntichain_singleton (v : V) : G.IsAntichain {v} := by
  intros u hu w hw hne
  rw [Finset.mem_singleton] at hu hw
  subst hu; subst hw
  exact absurd rfl hne

/-! ## Foliations -/

/-- A sequence `f : ℕ → Finset V` is a foliation of `G` if every level is an antichain,
distinct levels are disjoint, and every vertex lies in some level. -/
structure IsFoliation (f : Nat → Finset V) : Prop where
  antichain : ∀ n, G.IsAntichain (f n)
  disjoint  : ∀ m n, m ≠ n → Disjoint (f m) (f n)
  covers    : ∀ v : V, ∃ n, v ∈ f n

/-! ## Foliation from a time function

For a `TimeFunction` `τ : V → ℕ`, which strictly increases along every causal edge, the
level sets `{v : τ v = n}` form a foliation. -/

/-- `u ≼ v` (`ReflTransGen causalEdge u v`) implies `tf.τ u ≤ tf.τ v`. -/
theorem time_monotone_causallyPrecedes (tf : G.TimeFunction)
    {u v : V} (h : G.causallyPrecedes u v) :
    tf.τ u ≤ tf.τ v := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (tf.monotone hbc))

/-- If `u ≺ v` (that is, `u ≠ v ∧ u ≼ v`), then `tf.τ u < tf.τ v`. -/
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

/-- The level set `{v : τ v = n}`. -/
noncomputable def timeLevelSet (tf : G.TimeFunction) (n : ℕ) : Finset V :=
  Finset.univ.filter (fun v => tf.τ v = n)

/-- Each level set of a time function is an antichain. -/
theorem timeLevelSet_isAntichain (tf : G.TimeFunction) (n : ℕ) :
    G.IsAntichain (timeLevelSet G tf n) := by
  intro u hu v hv _huv hstrict
  simp [timeLevelSet, Finset.mem_filter] at hu hv
  have h_strict : tf.τ u < tf.τ v :=
    time_strict_monotone_strictCausallyPrecedes G tf hstrict
  omega

/-- Level sets at distinct times are disjoint. -/
theorem timeLevelSet_disjoint (tf : G.TimeFunction)
    (m n : ℕ) (hmn : m ≠ n) :
    Disjoint (timeLevelSet G tf m) (timeLevelSet G tf n) := by
  rw [Finset.disjoint_left]
  intro v hv_m hv_n
  simp [timeLevelSet, Finset.mem_filter] at hv_m hv_n
  omega

/-- Every vertex `v` lies in the level set at time `τ v`. -/
theorem timeLevelSet_covers (tf : G.TimeFunction) (v : V) :
    ∃ n, v ∈ timeLevelSet G tf n := by
  refine ⟨tf.τ v, ?_⟩
  simp [timeLevelSet, Finset.mem_filter]

/-- The level sets of a time function on `G` form a foliation of `G`. -/
theorem timeFunction_foliation (tf : G.TimeFunction) :
    G.IsFoliation (timeLevelSet G tf) where
  antichain := timeLevelSet_isAntichain G tf
  disjoint := timeLevelSet_disjoint G tf
  covers := timeLevelSet_covers G tf

/-- A stably causal graph (one with a time function) admits a foliation. -/
theorem stablyCausal_hasFoliation (h : G.StablyCausal) :
    ∃ f : ℕ → Finset V, G.IsFoliation f :=
  ⟨timeLevelSet G (Classical.choice h),
    timeFunction_foliation G (Classical.choice h)⟩

end CausalGraph

/-! ## Proper time

Proper time from `u` to `v` is the maximal length of a chain from `u` to `v`. -/

namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-- `HasProperTime G u v n`: there is a chain of length `n` from `u` to `v` and every
chain from `u` to `v` has length at most `n`. -/
def HasProperTime (u v : V) (n : Nat) : Prop :=
  G.ChainOfLength n u v ∧ ∀ m, G.ChainOfLength m u v → m ≤ n

end CausalGraph

end InfraFormalization
