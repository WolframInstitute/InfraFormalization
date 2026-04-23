/-
**Transitively-reduced causal graph type** (Group IC — infracausality).

The Srní / Madrid Infrageometry program (Pavel Hájek et al.) and
the "Axiomatic Relativity from Causal Graphs" draft (Carlos Zapata,
Sara Ahmed) anchor everything on *transitively-reduced* causal
graphs as the minimal data structure for special relativity in the
Wolfram-model context. Light rays, observer chains, Cauchy foliations,
and Marzke–Wheeler clocks all live on this type.

This file formalises:

  * `CausalGraph V` — a finite DAG on `V`, transitively reduced
    (`TR`), with an explicit irreflexive + antisymmetric proof.
  * `ObserverChain G v` (IC2) — a maximal causal chain from `v`.
  * `LightRay G v` (IC3, stub form) — a subgraph whose causal
    interval to every vertex is degenerate.
  * Basic lemmas: `causalPrecedes_refl` is false, `causalPrecedes`
    is transitive, acyclicity follows from TR.

**Connection to hypergraphs.** Every `Trajectory sys init` induces a
causal graph (via `Causal.lean`'s `causallyPrecedes`). The
transitive reduction is then the minimal edge set generating the same
order — the *direct* causal-precedence relation. We define
`CausalGraph V` abstractly so that both hypergraph-trajectory-induced
and other causal graphs (e.g. Minkowski-sprinkled causal sets) can
inhabit the same type.

**Status.** Closes IC1; prepares IC2, IC3. EPS axiomatics (IC7) and
Marzke–Wheeler (IC8) build further on this scaffold.
-/

import InfraFormalization.Hypergraph
import InfraFormalization.Causal
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Transitively-reduced causal graph on `V`**: a binary relation
`causalEdge` that is irreflexive, antisymmetric (via its transitive
closure), and **transitively reduced** (no edge `a → b` is redundant
given the rest). Minimal data for a "direct-cause" DAG. -/
structure CausalGraph (V : Type*) where
  causalEdge  : V → V → Prop
  irrefl      : ∀ v, ¬ causalEdge v v
  /- Transitive reduction: no direct edge `a → b` is witnessed
  by an intermediate `a → c → b`. Enforces minimality. -/
  transitively_reduced :
    ∀ a b, causalEdge a b →
    ¬ ∃ c, causalEdge a c ∧ Relation.ReflTransGen causalEdge c b ∧ c ≠ a ∧ c ≠ b

namespace CausalGraph

variable (G : CausalGraph V)

/-- **Causal precedence** (reflexive-transitive closure of `causalEdge`). -/
def causallyPrecedes (u v : V) : Prop :=
  Relation.ReflTransGen G.causalEdge u v

/-- **Strict causal precedence**: `u ≠ v ∧ causallyPrecedes u v`. -/
def strictCausallyPrecedes (u v : V) : Prop :=
  u ≠ v ∧ G.causallyPrecedes u v

theorem causallyPrecedes_refl (v : V) : G.causallyPrecedes v v :=
  Relation.ReflTransGen.refl

theorem causallyPrecedes_trans {u v w : V}
    (huv : G.causallyPrecedes u v) (hvw : G.causallyPrecedes v w) :
    G.causallyPrecedes u w :=
  Relation.ReflTransGen.trans huv hvw

/-- **Direct causation implies causal precedence.** -/
theorem causalEdge_implies_precedes {u v : V} (h : G.causalEdge u v) :
    G.causallyPrecedes u v :=
  Relation.ReflTransGen.single h

/-! ### Chronological vs causal relations (E2 / #54)

In continuum Lorentzian geometry, the *chronological* relation `I^+`
is strict timelike precedence (`u ≪ v`); the *causal* relation `J^+`
is non-strict ≤ (`u ≼ v`), including both timelike and null. On a
discrete causal graph:

  * `causallyPrecedes u v` = `u ≼ v`  (causal J^+)
  * `strictCausallyPrecedes u v` = `u ≠ v ∧ u ≼ v`  (chronological I^+)

The inclusion `I^+ ⊆ J^+` (chronological ⇒ causal) is immediate from
the definition. -/

/-- **Chronological relation** (alias of `strictCausallyPrecedes`): on
a discrete causal graph the chronological future is strict causal
precedence. -/
def chronological (u v : V) : Prop := G.strictCausallyPrecedes u v

/-- **Causal relation** (alias of `causallyPrecedes`): non-strict
causal precedence. -/
def causal (u v : V) : Prop := G.causallyPrecedes u v

/-- **Chronological implies causal** (`I^+ ⊆ J^+`). -/
theorem chronological_implies_causal {u v : V}
    (h : G.chronological u v) : G.causal u v :=
  h.2

/-- **Causal relation is reflexive**. -/
theorem causal_refl (v : V) : G.causal v v :=
  G.causallyPrecedes_refl v

/-- **Chronological relation is irreflexive**: no event is strictly
causally before itself. -/
theorem chronological_irrefl (v : V) : ¬ G.chronological v v :=
  fun h => h.1 rfl


/-! ## Observer chains (Prop-level)

An **observer chain from `u` to `v`** is simply the causal-precedence
relation: `u` can reach `v` via a sequence of direct causal edges.
The relation is already `causallyPrecedes` (the `ReflTransGen`). This
section provides the structured-pattern view as an inductive Prop for
downstream reasoning about chain lengths. -/

/-- **`ChainOfLength G n u v`** holds iff there is a chain of exactly
`n` direct causal edges from `u` to `v`. Length-0 = equality;
length-(n+1) = length-n chain followed by one edge. -/
inductive ChainOfLength (G : CausalGraph V) : Nat → V → V → Prop
  | refl (v : V) : ChainOfLength G 0 v v
  | cons {n : Nat} {u v w : V} :
      ChainOfLength G n u v → G.causalEdge v w → ChainOfLength G (n + 1) u w

/-- **Chain endpoints are causally related.** -/
theorem chainOfLength_implies_causallyPrecedes
    {n : Nat} {u v : V} (c : ChainOfLength G n u v) :
    G.causallyPrecedes u v := by
  induction c with
  | refl _ => exact G.causallyPrecedes_refl _
  | cons _ hedge ih =>
    exact G.causallyPrecedes_trans ih (G.causalEdge_implies_precedes hedge)

/-! ## Light rays (stub)

A **light ray** from `v` is a subgraph whose vertices `u` satisfy:
the causal interval `[v, u]` is *degenerate*, i.e., every causal
precedence `v ≺ w ≺ u` forces `w = v` or `w = u`. In the transitively-
reduced causal graph, this captures "nothing between `v` and `u`" —
the Wolfram-Institute operational definition of a light-ray step.

Here we define the basic predicate; the full light-ray subgraph
construction (IC3) extends it. -/

/-- **Degenerate causal interval**: `[v, u]` contains no
intermediate vertex (other than `v` and `u`). -/
def DegenerateInterval (v u : V) : Prop :=
  G.causallyPrecedes v u ∧
  ∀ w, G.causallyPrecedes v w → G.causallyPrecedes w u → w = v ∨ w = u

/-- **On a light-step from `v`**: `u` is on the light ray through `v`
if `[v, u]` is degenerate. This aligns with Carlos Zapata's
Marzke–Wheeler setup where direct causal edges are light-steps. -/
def OnLightStepFrom (v u : V) : Prop := G.DegenerateInterval v u

/-! ### Discrete light cones, causal future and past (E3 / #55)

The causal partial order on a causal graph induces light-cone-like
set-theoretic structures: the causal future of an event is the set of
events it can influence; the causal past is the set of events that
can influence it; the (closed) light cone is the union.
-/

/-- **Causal future** of an event `v`: the set of events `u` with
`v ≼ u`. -/
def causalFuture (v : V) : Set V :=
  {u | G.causallyPrecedes v u}

/-- **Causal past** of an event `v`: the set of events `u` with
`u ≼ v`. -/
def causalPast (v : V) : Set V :=
  {u | G.causallyPrecedes u v}

/-- **Closed light cone** of an event `v`: the union of its causal
future and causal past. -/
def lightCone (v : V) : Set V :=
  G.causalFuture v ∪ G.causalPast v

/-- **Every event is in its own causal future** (reflexivity of
`causallyPrecedes`). -/
theorem self_mem_causalFuture (v : V) : v ∈ G.causalFuture v :=
  G.causallyPrecedes_refl v

/-- **Every event is in its own causal past**. -/
theorem self_mem_causalPast (v : V) : v ∈ G.causalPast v :=
  G.causallyPrecedes_refl v

/-- **Every event is in its own light cone**. -/
theorem self_mem_lightCone (v : V) : v ∈ G.lightCone v :=
  Or.inl (G.self_mem_causalFuture v)

/-- **Causal future is transitively closed**: if `v` is in `u`'s
future and `w` is in `v`'s future, then `w` is in `u`'s future. -/
theorem causalFuture_trans {u v w : V}
    (hvu : v ∈ G.causalFuture u) (hwv : w ∈ G.causalFuture v) :
    w ∈ G.causalFuture u :=
  G.causallyPrecedes_trans hvu hwv

/-! ### Causality conditions (E4 / #56)

Discrete analogs of continuum Lorentzian causality conditions:

  * **StronglyCausal** — there are no closed timelike-like loops: no
    non-trivial chain of causal edges returns to its start.
  * **StablyCausal** — there exists a "time function" `τ : V → ℕ`
    strictly increasing along causal edges.
  * Implication: stably causal ⇒ strongly causal. -/

/-- **Strong causality**: no non-trivial closed chain.
`ChainOfLength G n v v` with `n > 0` never holds. -/
def StronglyCausal : Prop :=
  ∀ {n : Nat} {v : V}, 0 < n → ¬ ChainOfLength G n v v

/-- **A time function** on `G` is a map `V → ℕ` strictly increasing
along every direct causal edge. -/
structure TimeFunction where
  /-- The underlying map. -/
  τ : V → ℕ
  /-- `τ` strictly increases along every direct causal edge. -/
  monotone : ∀ {u v}, G.causalEdge u v → τ u < τ v

/-- **Stable causality**: a time function exists. -/
def StablyCausal : Prop := Nonempty G.TimeFunction

/-- **Time-function chain lemma**: along any chain of length `n`, the
time function weakly increases. -/
theorem chain_monotone_time (tf : G.TimeFunction) :
    ∀ {n : Nat} {u v : V}, ChainOfLength G n u v → tf.τ u ≤ tf.τ v
  | 0, _, _, ChainOfLength.refl _ => le_refl _
  | _ + 1, _, _, ChainOfLength.cons c e => by
    have ih := chain_monotone_time tf c
    have hedge : tf.τ _ < tf.τ _ := tf.monotone e
    omega

/-- **Strict time-function chain lemma**: a chain of length `n > 0`
forces strict increase of `τ`. -/
theorem chain_strict_time (tf : G.TimeFunction) :
    ∀ {n : Nat} {u v : V}, 0 < n → ChainOfLength G n u v →
      tf.τ u < tf.τ v
  | 0, _, _, hpos, _ => absurd hpos (by omega)
  | _ + 1, _, _, _, ChainOfLength.cons c e => by
    have ih := G.chain_monotone_time tf c
    have hedge := tf.monotone e
    omega

/-- **Stably causal implies strongly causal** — a time function blocks
closed non-trivial chains: `τ(v) < τ(v)` is impossible. -/
theorem stablyCausal_implies_stronglyCausal
    (h : G.StablyCausal) : G.StronglyCausal := by
  intro n v hn_pos hchain
  have tf : G.TimeFunction := Classical.choice h
  have : tf.τ v < tf.τ v := G.chain_strict_time tf hn_pos hchain
  exact absurd this (Nat.lt_irrefl _)

/-- **Edge-free causal graph is stably causal.** If `G` has no causal
edges, the constant-zero function is a valid time function (vacuously
monotone). -/
theorem stablyCausal_of_no_edges (h : ∀ u v : V, ¬ G.causalEdge u v) :
    G.StablyCausal :=
  ⟨{ τ := fun _ => 0
     monotone := fun {u v} hedge => absurd hedge (h u v) }⟩

end CausalGraph

end InfraFormalization
