/-
An abstract causal graph type: an irreflexive, transitively reduced edge relation.

The module defines `CausalGraph V`, the reflexive-transitive closure `causallyPrecedes` and
its strict version, chains of a given length (`ChainOfLength`), degenerate intervals,
causal future, past and light cone, the no-closed-chain condition `StronglyCausal`, time
functions and `StablyCausal` (a time function exists). It proves basic order facts and
that `StablyCausal` implies `StronglyCausal`. The structure does not require acyclicity.
-/

import InfraFormalization.Hypergraph
import InfraFormalization.Causal
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A relation `causalEdge` on `V` that is irreflexive and transitively reduced. -/
structure CausalGraph (V : Type*) where
  causalEdge  : V → V → Prop
  irrefl      : ∀ v, ¬ causalEdge v v
  /- Transitive reduction: for an edge `a → b` there is no `c` distinct from `a` and `b`
  with an edge `a → c` and a path from `c` to `b`. -/
  transitively_reduced :
    ∀ a b, causalEdge a b →
    ¬ ∃ c, causalEdge a c ∧ Relation.ReflTransGen causalEdge c b ∧ c ≠ a ∧ c ≠ b

namespace CausalGraph

variable (G : CausalGraph V)

/-- The reflexive-transitive closure of `causalEdge`. -/
def causallyPrecedes (u v : V) : Prop :=
  Relation.ReflTransGen G.causalEdge u v

/-- `u ≠ v ∧ causallyPrecedes u v`. -/
def strictCausallyPrecedes (u v : V) : Prop :=
  u ≠ v ∧ G.causallyPrecedes u v

theorem causallyPrecedes_refl (v : V) : G.causallyPrecedes v v :=
  Relation.ReflTransGen.refl

theorem causallyPrecedes_trans {u v w : V}
    (huv : G.causallyPrecedes u v) (hvw : G.causallyPrecedes v w) :
    G.causallyPrecedes u w :=
  Relation.ReflTransGen.trans huv hvw

/-- An edge `u → v` implies `causallyPrecedes u v`. -/
theorem causalEdge_implies_precedes {u v : V} (h : G.causalEdge u v) :
    G.causallyPrecedes u v :=
  Relation.ReflTransGen.single h

/-! ### Chronological and causal relations

`chronological` is a second name for `strictCausallyPrecedes`, and `causal` for
`causallyPrecedes`, following the continuum notation `I^+` and `J^+`. -/

/-- A second name for `strictCausallyPrecedes`. -/
def chronological (u v : V) : Prop := G.strictCausallyPrecedes u v

/-- A second name for `causallyPrecedes`. -/
def causal (u v : V) : Prop := G.causallyPrecedes u v

/-- `chronological u v` implies `causal u v`. -/
theorem chronological_implies_causal {u v : V}
    (h : G.chronological u v) : G.causal u v :=
  h.2

/-- `causal` is reflexive. -/
theorem causal_refl (v : V) : G.causal v v :=
  G.causallyPrecedes_refl v

/-- `chronological` is irreflexive. -/
theorem chronological_irrefl (v : V) : ¬ G.chronological v v :=
  fun h => h.1 rfl


/-! ## Chains of a given length -/

/-- `ChainOfLength G n u v`: there is a path of exactly `n` edges from `u` to `v`. -/
inductive ChainOfLength (G : CausalGraph V) : Nat → V → V → Prop
  | refl (v : V) : ChainOfLength G 0 v v
  | cons {n : Nat} {u v w : V} :
      ChainOfLength G n u v → G.causalEdge v w → ChainOfLength G (n + 1) u w

/-- `ChainOfLength G n u v` implies `causallyPrecedes u v`. -/
theorem chainOfLength_implies_causallyPrecedes
    {n : Nat} {u v : V} (c : ChainOfLength G n u v) :
    G.causallyPrecedes u v := by
  induction c with
  | refl _ => exact G.causallyPrecedes_refl _
  | cons _ hedge ih =>
    exact G.causallyPrecedes_trans ih (G.causalEdge_implies_precedes hedge)

/-! ## Degenerate intervals -/

/-- `v ≼ u`, and every `w` with `v ≼ w ≼ u` equals `v` or `u`. -/
def DegenerateInterval (v u : V) : Prop :=
  G.causallyPrecedes v u ∧
  ∀ w, G.causallyPrecedes v w → G.causallyPrecedes w u → w = v ∨ w = u

/-- A second name for `DegenerateInterval v u`. -/
def OnLightStepFrom (v u : V) : Prop := G.DegenerateInterval v u

/-! ### Causal future, past and light cone -/

/-- The causal future `{u | v ≼ u}`. -/
def causalFuture (v : V) : Set V :=
  {u | G.causallyPrecedes v u}

/-- The causal past `{u | u ≼ v}`. -/
def causalPast (v : V) : Set V :=
  {u | G.causallyPrecedes u v}

/-- The union of the causal future and the causal past of `v`. -/
def lightCone (v : V) : Set V :=
  G.causalFuture v ∪ G.causalPast v

/-- `v ∈ causalFuture v`. -/
theorem self_mem_causalFuture (v : V) : v ∈ G.causalFuture v :=
  G.causallyPrecedes_refl v

/-- `v ∈ causalPast v`. -/
theorem self_mem_causalPast (v : V) : v ∈ G.causalPast v :=
  G.causallyPrecedes_refl v

/-- `v ∈ lightCone v`. -/
theorem self_mem_lightCone (v : V) : v ∈ G.lightCone v :=
  Or.inl (G.self_mem_causalFuture v)

/-- If `v ∈ causalFuture u` and `w ∈ causalFuture v`, then `w ∈ causalFuture u`. -/
theorem causalFuture_trans {u v w : V}
    (hvu : v ∈ G.causalFuture u) (hwv : w ∈ G.causalFuture v) :
    w ∈ G.causalFuture u :=
  G.causallyPrecedes_trans hvu hwv

/-! ### Causality conditions -/

/-- No closed path of positive length: `ChainOfLength G n v v` fails for every `n > 0`. -/
def StronglyCausal : Prop :=
  ∀ {n : Nat} {v : V}, 0 < n → ¬ ChainOfLength G n v v

/-- A map `τ : V → ℕ` with `τ u < τ v` for every edge `u → v`. -/
structure TimeFunction where
  /-- The underlying map. -/
  τ : V → ℕ
  /-- `τ` strictly increases along every edge. -/
  monotone : ∀ {u v}, G.causalEdge u v → τ u < τ v

/-- A time function exists. -/
def StablyCausal : Prop := Nonempty G.TimeFunction

/-- `ChainOfLength G n u v` implies `τ u ≤ τ v`. -/
theorem chain_monotone_time (tf : G.TimeFunction) :
    ∀ {n : Nat} {u v : V}, ChainOfLength G n u v → tf.τ u ≤ tf.τ v
  | 0, _, _, ChainOfLength.refl _ => le_refl _
  | _ + 1, _, _, ChainOfLength.cons c e => by
    have ih := chain_monotone_time tf c
    have hedge : tf.τ _ < tf.τ _ := tf.monotone e
    omega

/-- For `n > 0`, `ChainOfLength G n u v` implies `τ u < τ v`. -/
theorem chain_strict_time (tf : G.TimeFunction) :
    ∀ {n : Nat} {u v : V}, 0 < n → ChainOfLength G n u v →
      tf.τ u < tf.τ v
  | 0, _, _, hpos, _ => absurd hpos (by omega)
  | _ + 1, _, _, _, ChainOfLength.cons c e => by
    have ih := G.chain_monotone_time tf c
    have hedge := tf.monotone e
    omega

/-- `StablyCausal` implies `StronglyCausal`. -/
theorem stablyCausal_implies_stronglyCausal
    (h : G.StablyCausal) : G.StronglyCausal := by
  intro n v hn_pos hchain
  have tf : G.TimeFunction := Classical.choice h
  have : tf.τ v < tf.τ v := G.chain_strict_time tf hn_pos hchain
  exact absurd this (Nat.lt_irrefl _)

/-- A causal graph with no edges is `StablyCausal`, with the constant function 0. -/
theorem stablyCausal_of_no_edges (h : ∀ u v : V, ¬ G.causalEdge u v) :
    G.StablyCausal :=
  ⟨{ τ := fun _ => 0
     monotone := fun {u v} hedge => absurd hedge (h u v) }⟩

end CausalGraph

end InfraFormalization
